use gl::types::{GLenum, GLsizei, GLuint};
use glutin::{window::Window, ContextWrapper, PossiblyCurrent};
use std::{fs, path::Path};

pub mod parser;
pub mod shader;

fn main() {
	// Variables to contain stuff modified at runtime.
	let mut buffer = String::new();
	let stdin = std::io::stdin();
	let mut v_source = String::new();
	let mut f_source = String::new();

	// Check that the files exists.
	if !Path::exists(Path::new("./test.vert")) {
		panic!("Could not find 'test.vert' in the project root!");
	}
	if !Path::exists(Path::new("./test.frag")) {
		panic!("Could not find 'test.vert' in the project root!");
	}

	// Ask for user input.
	const MSG: &str = "[p_] to parse, [c] to compile, [e] to exit:";
	println!("{}", MSG);

	// Enter the event loop.
	let event_loop = glutin::event_loop::EventLoop::new();
	let window = initialise_gl(&event_loop);
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

				if stdin.read_line(&mut buffer).is_ok() {
					// Clear the screen. NOTE: This doesn't actually clear it, just puts a bunch of newlines.
					print!("\x1b[2J");

					// Update the contents of the file.
					v_source = fs::read_to_string("./test.vert").unwrap();
					f_source = fs::read_to_string("./test.frag").unwrap();

					match buffer.trim().to_lowercase().as_ref() {
						"pv" => parser::parse(&v_source),
						"pf" => parser::parse(&f_source),
						"c" => {
							println!("\x1b[31;4mCOMPILING SHADER\x1b[0m");
							shader::create_shader(&v_source, None, &f_source);
							println!("Compiled");
						}
						"e" => *control_flow = ControlFlow::Exit,
						_ => {}
					}

					buffer.clear();

					// Ask for user input.
					println!("\n{}", MSG);
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
