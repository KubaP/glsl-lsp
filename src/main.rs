use gl::types::{GLenum, GLsizei, GLuint};
use glutin::{window::Window, ContextWrapper, PossiblyCurrent};
use notify::Watcher;
use std::{
	collections::VecDeque,
	fs,
	path::Path,
	sync::{Arc, Mutex},
	thread,
};

pub mod ast;
pub mod parser;
pub mod shader;
pub mod lexer;
pub mod expression;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
	Compile,
	Parse,
}

#[allow(unused_assignments)]
fn main() {
	// Variables to contain stuff modified at runtime.
	let mut v_source = String::new();
	let mut f_source = String::new();
	let mut parse_source = String::new();

	// Check that the files exists.
	if !Path::exists(Path::new("./test.parse")) {
		panic!("Could not find 'test.parse' in the project root!");
	}
	if !Path::exists(Path::new("./test.vert")) {
		panic!("Could not find 'test.vert' in the project root!");
	}
	if !Path::exists(Path::new("./test.frag")) {
		panic!("Could not find 'test.frag' in the project root!");
	}

	// Setup file watching.
	let event_queue = Arc::new(Mutex::new(VecDeque::new()));
	let handle = Arc::clone(&event_queue);
	thread::spawn(move || {
		let (tx, rx) = std::sync::mpsc::channel();
		let mut watcher =
			notify::watcher(tx, std::time::Duration::from_secs(1)).unwrap();
		watcher
			.watch("./test.parse", notify::RecursiveMode::Recursive)
			.unwrap();

		loop {
			match rx.recv() {
				Ok(_event) => {
					let mut queue = handle.lock().unwrap();
					queue.push_back(Type::Parse);
				}
				Err(e) => panic!("{e:?}"),
			}
		}
	});
	let handle = Arc::clone(&event_queue);
	thread::spawn(move || {
		let (tx, rx) = std::sync::mpsc::channel();
		let mut watcher =
			notify::watcher(tx, std::time::Duration::from_millis(500)).unwrap();
		watcher
			.watch("./test.vert", notify::RecursiveMode::Recursive)
			.unwrap();
		watcher
			.watch("./test.frag", notify::RecursiveMode::Recursive)
			.unwrap();

		loop {
			match rx.recv() {
				Ok(_event) => {
					let mut queue = handle.lock().unwrap();
					queue.push_back(Type::Compile);
				}
				Err(e) => panic!("{e:?}"),
			}
		}
	});

	// Create context and enter the event loop.
	let event_loop = glutin::event_loop::EventLoop::new();
	let window = initialise_gl(&event_loop);

	// Print at the start.
	parse_source = fs::read_to_string("./test.parse").unwrap();
	println!("\r\n");
	parser::parse(&parse_source);

	v_source = fs::read_to_string("./test.vert").unwrap();
	f_source = fs::read_to_string("./test.frag").unwrap();
	println!("\r\n\x1b[31;4mCOMPILING SHADER\x1b[0m");
	shader::create_shader(&v_source, None, &f_source);
	println!("Compiled");

	event_loop.run(move |event, _, control_flow| {
		use glutin::event::{Event, WindowEvent};
		use glutin::event_loop::ControlFlow;

		*control_flow = ControlFlow::Poll;

		match event {
			Event::LoopDestroyed => return,
			Event::MainEventsCleared => {
				window.window().request_redraw();
			}
			Event::RedrawRequested(_) => unsafe {
				gl::ClearColor(0.0, 0.0, 0.0, 1.0);
				gl::Clear(gl::COLOR_BUFFER_BIT | gl::DEPTH_BUFFER_BIT);

				let mut queue = event_queue.lock().unwrap();
				if !queue.is_empty() {
					let mut has_reparsed = false;
					let mut has_recompiled = false;

					queue.iter().for_each(|t| {
						if t == &Type::Parse && !has_reparsed {
							parse_source =
								fs::read_to_string("./test.parse").unwrap();

							println!("\r\n");
							parser::parse(&parse_source);

							has_reparsed = true;
						}
						if t == &Type::Compile && !has_recompiled {
							v_source =
								fs::read_to_string("./test.vert").unwrap();
							f_source =
								fs::read_to_string("./test.frag").unwrap();

							println!("\r\n\x1b[31;4mCOMPILING SHADER\x1b[0m");
							shader::create_shader(&v_source, None, &f_source);
							println!("Compiled");

							has_recompiled = true;
						}
					});
					queue.clear();
				}

				window.swap_buffers().unwrap();
			},
			Event::WindowEvent { ref event, .. } => match event {
				WindowEvent::Resized(_) => {}
				WindowEvent::CloseRequested => {
					*control_flow = ControlFlow::Exit;
				}
				WindowEvent::KeyboardInput { .. } => {}
				_ => {}
			},
			_ => {}
		}
	});
}

extern "system" fn opengl_dbg_callback(
	_source: GLenum,
	r#type: GLenum,
	_id: GLuint,
	severity: GLenum,
	_length: GLsizei,
	message: *const i8,
	_user_param: *mut std::ffi::c_void,
) {
	unsafe {
		// 'message' should be a null-terminated string.
		let message = std::ffi::CStr::from_ptr(message)
			.to_str()
			.unwrap_or("CANNOT READ OPENGL ERROR MESSAGE STRING!");

		// Convert the opengl enums into readable form.
		let error_type = match r#type {
			gl::DEBUG_TYPE_ERROR => "ERROR",
			gl::DEBUG_TYPE_DEPRECATED_BEHAVIOR => "DEPRECATED",
			gl::DEBUG_TYPE_UNDEFINED_BEHAVIOR => "UNDEFINED BEHAVIOUR",
			gl::DEBUG_TYPE_PORTABILITY => "NOT PORTABLE",
			gl::DEBUG_TYPE_PERFORMANCE => "PERFORMANCE ISSUE",
			_ => "OTHER",
		};
		let severity = match severity {
			gl::DEBUG_SEVERITY_HIGH => "High",
			gl::DEBUG_SEVERITY_MEDIUM => "Medium",
			gl::DEBUG_SEVERITY_LOW => "Low",
			gl::DEBUG_SEVERITY_NOTIFICATION => "Info",
			_ => "?",
		};

		println!(
			"\x1b[35m{error_type} ( Severity: {severity} )\n{message}\x1b[0m"
		);
	}
}

fn initialise_gl(
	event_loop: &glutin::event_loop::EventLoop<()>,
) -> ContextWrapper<PossiblyCurrent, Window> {
	unsafe {
		let builder = glutin::window::WindowBuilder::new()
			.with_title("GLSL PLAYGROUND")
			.with_inner_size(glutin::dpi::PhysicalSize::new(10u32, 10u32))
			.with_decorations(false);

		let window = glutin::ContextBuilder::new()
			.with_vsync(true)
			.with_gl_profile(glutin::GlProfile::Core)
			.with_gl(glutin::GlRequest::Specific(glutin::Api::OpenGl, (4, 5)))
			.with_gl_debug_flag(true)
			.with_depth_buffer(24)
			.with_stencil_buffer(8)
			.build_windowed(builder, &event_loop)
			.unwrap()
			.make_current()
			.unwrap();

		// Initialise OPENGL.
		gl::load_with(|s| {
			window.get_proc_address(s) as *const std::ffi::c_void
		});

		// Set the GL_VIEWPORT.
		// (0, 0) is the lower-left corner.
		// (width, height) is the upper-right corner.
		// This gets mapped to the -1 to 1 absolute values.
		// 		i.e. (-1, -1) is (0, 0); (0, 0) is (width/2, height/2); (1, 1) is (width, height).
		// glViewport https://docs.gl/gl4/glViewport
		gl::Viewport(0, 0, 10, 10);

		gl::Enable(gl::DEBUG_OUTPUT);
		gl::DebugMessageCallback(
			Some(opengl_dbg_callback),
			0 as *const std::ffi::c_void,
		);

		window
	}
}
