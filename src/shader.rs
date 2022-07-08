use gl::types::*;

/// The error type for operations on *GL_SHADER* and *GL_SHADER_PROGRAM*.
/// When some of these error types occur, the *GL_DEBUG_CALLBACK* will be triggered and that will
/// print out the detailed error information if available.
#[derive(Debug)]
pub enum Error {
	/// Error during the creation/compilation of the shader program.
	Creation(String),
	/// Identifier name, for a shader program, doesn't exist.
	ShaderNotFound(String),
}

impl std::fmt::Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Error::Creation(s) => write!(f, "{}", s),
			Error::ShaderNotFound(s) => {
				write!(f, "Could not find the shader program named: '{}'.", s)
			}
		}
	}
}

/// The 3 types of supported *GL_SHADER*s.
#[derive(Debug)]
enum Type {
	Vertex,
	Geometry,
	Fragment,
}

/// Creates an individual *GL_SHADER*.
unsafe fn create_opengl_shader(
	source: &str,
	r#type: Type,
) -> Result<GLuint, Error> {
	// Create a new GL_SHADER, containing the source code for the individual shader step.
	// glCreateShader https://docs.gl/gl4/glCreateShader
	let shader_id = match r#type {
		Type::Vertex => gl::CreateShader(gl::VERTEX_SHADER),
		Type::Geometry => gl::CreateShader(gl::GEOMETRY_SHADER),
		Type::Fragment => gl::CreateShader(gl::FRAGMENT_SHADER),
	};

	// Copy the source code and compile it.
	// glShaderSource https://docs.gl/gl4/glShaderSource
	// Notes:
	// 		The source code is copied over to the gpu; it can be safely freed from memory.
	gl::ShaderSource(
		shader_id,
		1,
		&(source.as_ptr() as *const GLchar),
		&(source.len() as GLint),
	);

	// glCompileShader https://docs.gl/gl4/glCompileShader
	gl::CompileShader(shader_id);

	// Check that the GL_SHADER was compiled successfully.
	// glGetShaderIv https://docs.gl/gl4/glGetShader
	// Returns:
	// 		GL_TRUE  (1) if successful.
	// 		GL_FALSE (0) if unsuccessful.
	let mut status = 0;
	gl::GetShaderiv(shader_id, gl::COMPILE_STATUS, &mut status);
	if status == 0 {
		// ⚠ No longer need to perform this logic since a GL_DEBUG_CALLBACK has
		//    been registered.

		/* let mut length = 0;
		gl::GetShaderiv(shader_id, gl::INFO_LOG_LENGTH, &mut length);
		let mut log = String::with_capacity(length as usize);
		log.extend(std::iter::repeat('\0').take(length as usize));

		// glGetShaderInfoLog https://docs.gl/gl4/glGetShaderInfoLog
		gl::GetShaderInfoLog(
			shader_id,
			length,
			&mut length,
			log[..].as_mut_ptr() as *mut GLchar,
		);
		log.truncate(length as usize); */

		return Err(Error::Creation("Compilation Error".into()));
	}

	// Everything should have gone correctly, so return the GL_SHADER's GL_ID.
	Ok(shader_id)
}

/// Constructs a [`shader::Program`](self::Program).
///
/// This creates a new *GL_SHADER_PROGRAM*, containing one or more individual *GL_SHADER*s.
///
/// This function can fail and return an error for the following reasons:
///
/// - The given identifier was already taken.
/// - An individual shader failed to compile.
/// - A shader program failed to link.
///
/// (Aside from returning an error, OPENGL errors will be logged through the *GL_DEBUG_CALLBACK*).
pub fn create_shader(vertex: &str, geometry: Option<&str>, fragment: &str) {
	unsafe {
		// Create a new GL_SHADER_PROGRAM, to contain all of the specified GL_SHADERs.
		// glCreateProgram https://docs.gl/gl4/glCreateProgram
		let program_id = gl::CreateProgram();

		// Create the individual GL_SHADER for each of the passed in sources.
		// If the creation process fails, the error will be propagated up.
		// glAttachShader https://docs.gl/gl4/glAttachShader
		let v_shader = match create_opengl_shader(vertex, Type::Vertex) {
			Ok(v) => v,
			Err(_) => {
				return;
			}
		};
		gl::AttachShader(program_id, v_shader);

		let g_shader: Option<u32> = if let Some(source) = geometry {
			let t = match create_opengl_shader(source, Type::Geometry) {
				Ok(v) => v,
				Err(_) => {
					return;
				}
			};
			gl::AttachShader(program_id, t);
			Some(t)
		} else {
			None
		};

		let f_shader = match create_opengl_shader(fragment, Type::Fragment) {
			Ok(v) => v,
			Err(_) => {
				return;
			}
		};
		gl::AttachShader(program_id, f_shader);

		// Set the output location for the fragment shader.
		// TODO: Allow this to be configurable.
		gl::BindFragDataLocation(
			program_id,
			0,
			"out_Colour".as_ptr() as *const GLchar,
		);

		// Link the attached GL_SHADERs to the GL_SHADER_PROGRAM.
		// glLinkProgram https://docs.gl/gl4/glLinkProgram
		gl::LinkProgram(program_id);

		// Check that the GL_SHADER_PROGRAM was compiled successfully.
		// glGetShaderIv https://docs.gl/gl4/glGetShader
		// Returns:
		// 		GL_TRUE  (1) if successful.
		// 		GL_FALSE (0) if unsuccessful.
		let mut status = 0;
		gl::GetProgramiv(program_id, gl::LINK_STATUS, &mut status);
		if status == 0 {
			// ⚠ No longer need to perform this logic since a GL_DEBUG_CALLBACK has
			//    been registered.
			/* let mut length = 0;
			gl::GetProgramiv(program_id, gl::INFO_LOG_LENGTH, &mut length);
			let mut log = String::with_capacity(length as usize);
			log.extend(std::iter::repeat('\0').take(length as usize));

			gl::GetProgramInfoLog(
				program_id,
				length,
				&mut length,
				log[..].as_mut_ptr() as *mut GLchar,
			);
			log.truncate(length as usize); */

			// Since the compilation failed, clean up any created resources.
			// glDeleteShader https://docs.gl/gl4/glDeleteShader
			gl::DeleteShader(v_shader);
			if let Some(g) = g_shader {
				gl::DeleteShader(g);
			}
			gl::DeleteShader(f_shader);

			return;
		}

		// Now that the GL_SHADER_PROGRAM has been successfully linked, delete the GL_SHADERs as they are
		// no longer necessary.
		// glDeleteShader https://docs.gl/gl4/glDeleteShader
		gl::DeleteShader(v_shader);
		if let Some(g) = g_shader {
			gl::DeleteShader(g);
		}
		gl::DeleteShader(f_shader);
	}
}

/// Parse a shader file into separate raw strings.
///
/// Parses a valid shader file containing the `# VERTEX` and `# FRAGMENT`, and optionally the
/// `# GEOMETRY`, headings.
///
/// Returns as a tuple of `(vertex, Option<geometry>, fragment)`.
///
/// # Example
/// An accepted file:
/// ```glsl
/// # VERTEX
/// #version 450 core
/// ...
///
/// # FRAGMENT
/// #version 450 core
/// ...
///
/// ```
/// ```
/// // A use case.
/// let (vert, _, frag) = shader::parse_file(&file_contents);
/// ```
pub fn parse_file<'a>(content: &'a str) -> (&'a str, Option<&'a str>, &'a str) {
	let v;
	let mut g = None;
	let f;

	let c = content
		.strip_prefix("# VERTEX")
		.expect("A valid shader file. Could not match pattern: # VERTEX")
		.trim_start()
		.trim_end();

	if c.contains("# GEOMETRY") {
		let c = c.split_once("# GEOMETRY").unwrap();
		v = c.0.trim_end();

		let c = c
			.1
			.split_once("# FRAGMENT")
			.expect("A valid shader file. Could not match pattern: # FRAGMENT");
		g = Some(c.0.trim_start().trim_end());
		f = c.1.trim_start();
	} else {
		let c = c
			.split_once("# FRAGMENT")
			.expect("A valid shader file. Could not match pattern: # FRAGMENT");
		v = c.0.trim_end();
		f = c.1.trim_start();
	}

	(v, g, f)
}
