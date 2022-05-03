use crate::parser::{NumType, OpType};

#[derive(Debug, Clone)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}

#[derive(Debug, Clone)]
pub enum Expr {
	/// A literal value; either a number, a boolean.
	Lit(Lit),
	/// An identifier; could be a variable name, function name, etc.
	Ident(Ident),
	/// A negation of an expression.
	Neg(Box<Expr>),
	/// Binary expression with a left and right hand-side.
	Binary {
		left: Box<Expr>,
		op: OpType,
		right: Box<Expr>,
	},
	/// Function call.
	Fn { ident: Ident, args: Vec<Expr> },
	/// Array constructor.
	Array { type_: Type, args: Vec<Expr> },
	/// Initializer list.
	InitList(Vec<Expr>),
	/// Member access.
	Member(Vec<Ident>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
	/// An empty statement, i.e. just a `;`.
	Empty,
	/// Variable declaration.
	VarDecl {
		type_: Type,
		ident: Ident,
		value: Option<Expr>,
		is_const: bool,
	},
	/// Function declaration.
	FnDecl {
		type_: Type,
		ident: Ident,
		params: Vec<(Type, Ident)>,
		body: Vec<Stmt>,
	},
	/// Struct declaration.
	StructDecl {
		ident: Ident,
		members: Vec<(Type, Ident)>,
	},
	/// Function call (on its own, as opposed to being part of a larger expression).
	FnCall { ident: Ident, args: Vec<Expr> },
	/// Variable assignment.
	VarAssign { ident: Ident, value: Expr },
	/// Preprocessor calls.
	Preproc(Preproc),
}

#[derive(Debug, Clone)]
pub enum Preproc {
	Version {
		version: usize,
		is_core: bool,
	},
	Extension {
		name: String,
		behaviour: ExtBehaviour,
	},
	Line {
		line: usize,
		src_str: Option<usize>,
	},
	Include(String),
	UnDef(String),
	IfDef(String),
	IfnDef(String),
	Else,
	EndIf,
	Error(String),
	Pragma(String),
	Unsupported,
}

impl std::fmt::Display for Preproc {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Preproc::Version { version, is_core } => write!(
				f,
				"version: {version} profile: {}",
				if *is_core { "core" } else { "compat" }
			),
			Preproc::Extension { name, behaviour } => {
				write!(f, "ext: {name} behaviour: {behaviour:?}")
			}
			Preproc::Line { line, src_str } => write!(
				f,
				"line: {line} src: {}",
				if let Some(s) = src_str {
					format!("{s}")
				} else {
					format!(" ")
				}
			),
			Preproc::Include(s) => write!(f, "include=\"{s}\""),
			Preproc::UnDef(s) => write!(f, "UNDEF=\"{s}\""),
			Preproc::IfDef(s) => write!(f, "IFDEF=\"{s}\""),
			Preproc::IfnDef(s) => write!(f, "IFNDEF=\"{s}\""),
			Preproc::Else => write!(f, "ELSE"),
			Preproc::EndIf => write!(f, "END"),
			Preproc::Error(s) => write!(f, "error=\"{s}\""),
			Preproc::Pragma(s) => write!(f, "pragma=\"{s}\""),
			Preproc::Unsupported => write!(f, "UNSUPPORTED"),
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtBehaviour {
	Enable,
	Require,
	Warn,
	Disable,
}

/// A literal value.
#[derive(Debug, Clone, Copy)]
pub enum Lit {
	Bool(bool),
	Int(i64),
	UInt(u64),
	Float(f32),
	Double(f64),
}

impl std::fmt::Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Bool(b) => write!(f, "{}", b.to_string()),
			Self::Int(i) => write!(f, "{i}"),
			Self::UInt(u) => write!(f, "{u}"),
			Self::Float(fp) => write!(f, "{fp}"),
			Self::Double(d) => write!(f, "{d}"),
		}
	}
}

impl Lit {
	pub fn parse_num(s: &str, type_: NumType) -> Result<Self, ()> {
		// Sanity check, but this should never fail.
		if s == "" {
			return Err(());
		}
		match type_ {
			NumType::Normal => Self::parse_num_dec(s),
			NumType::Hex => Self::parse_num_hex(s),
			NumType::Oct => Self::parse_num_oct(s),
			NumType::Float => Self::parse_num_float(s),
			NumType::Double => Self::parse_num_double(s),
		}
	}

	fn parse_num_dec(s: &str) -> Result<Self, ()> {
		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 10) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 10) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_hex(s: &str) -> Result<Self, ()> {
		// Trim the '0x' part, otherwise the conversion will fail.
		let s = s.trim_start_matches("0x");

		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 16) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 16) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_oct(s: &str) -> Result<Self, ()> {
		// Trim the '0' part, because the first '0' is not part of the number itself but rather the radix.
		let s = s.trim_start_matches("0");

		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 8) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 8) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_float(s: &str) -> Result<Self, ()> {
		if let Ok(f) = s.parse::<f32>() {
			return Ok(Self::Float(f));
		}

		Err(())
	}

	fn parse_num_double(s: &str) -> Result<Self, ()> {
		// Remove the 'lf' suffix.
		let s = &s[..s.len() - 2];

		if let Ok(f) = s.parse::<f64>() {
			return Ok(Self::Double(f));
		}

		Err(())
	}
}

/// An identifier.
///
/// This can be a variable name, function name, etc.
#[derive(Debug, Clone)]
pub struct Ident(pub String);

impl std::fmt::Display for Ident {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl Ident {
	pub fn parse_name(s: &str) -> Result<Self, ()> {
		// If the string matches a primitive, then it can't be a valid name.
		match Primitive::parse(s) {
			Ok(_) => Err(()),
			Err(_) => Ok(Self(s.to_owned())),
		}
	}

	pub fn parse_struct(s: &str) -> Result<Self, ()> {
		if s.len() >= 3 && &s[0..3] == "gl_" {
			return Err(());
		}

		Ok(Self(s.to_owned()))
	}
}

/// A fundamental type.
///
/// These are the most fundamental types in the language, on which all other types are composed.
#[derive(Debug, Clone, Copy)]
pub enum Fundamental {
	Void,
	Bool,
	Int,
	Uint,
	Float,
	Double,
}

impl std::fmt::Display for Fundamental {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Fundamental::Void => write!(f, "void"),
			Fundamental::Bool => write!(f, "bool"),
			Fundamental::Int => write!(f, "int"),
			Fundamental::Uint => write!(f, "uint"),
			Fundamental::Float => write!(f, "float"),
			Fundamental::Double => write!(f, "double"),
		}
	}
}

/// A primitive language type.
///
/// ℹ The reason for the separation of this enum and the [`Fundamental`] enum is that all fundamental types (aside
/// from `void`) can be either a scalar or an n-dimensional vector. Furthermore, any of the types in this enum can
/// be on their own or as part of a n-dimensional array.
#[derive(Debug, Clone, Copy)]
pub enum Primitive {
	/// A scalar primitive type.
	Scalar(Fundamental),
	/// A n-dimensional type, where `2 <= n <= 4`.
	Vector(Fundamental, usize),
	/// A `float` matrix type.
	///
	/// - `0` - Column count,
	/// - `1` - Row count.
	Matrix(usize, usize),
	/// A `double` matrix type.
	///
	/// - `0` - Column count,
	/// - `1` - Row count.
	DMatrix(usize, usize),
}

impl std::fmt::Display for Primitive {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Primitive::Scalar(ff) => write!(f, "{ff}"),
			Primitive::Vector(ff, size) => write!(f, "{ff}-vec-{size}"),
			Primitive::Matrix(i, j) => write!(f, "float-mat-{i}x{j}"),
			Primitive::DMatrix(i, j) => write!(f, "double-mat-{i}x{j}"),
		}
	}
}

impl Primitive {
	pub fn parse(s: &str) -> Result<Self, ()> {
		match s {
			"void" => Ok(Primitive::Scalar(Fundamental::Void)),
			"bool" => Ok(Primitive::Scalar(Fundamental::Bool)),
			"int" => Ok(Primitive::Scalar(Fundamental::Int)),
			"uint" => Ok(Primitive::Scalar(Fundamental::Uint)),
			"float" => Ok(Primitive::Scalar(Fundamental::Float)),
			"double" => Ok(Primitive::Scalar(Fundamental::Double)),
			"vec2" => Ok(Primitive::Vector(Fundamental::Float, 2)),
			"vec3" => Ok(Primitive::Vector(Fundamental::Float, 3)),
			"vec4" => Ok(Primitive::Vector(Fundamental::Float, 4)),
			"bvec2" => Ok(Primitive::Vector(Fundamental::Bool, 2)),
			"bvec3" => Ok(Primitive::Vector(Fundamental::Bool, 3)),
			"bvec4" => Ok(Primitive::Vector(Fundamental::Bool, 4)),
			"ivec2" => Ok(Primitive::Vector(Fundamental::Int, 2)),
			"ivec3" => Ok(Primitive::Vector(Fundamental::Int, 3)),
			"ivec4" => Ok(Primitive::Vector(Fundamental::Int, 4)),
			"uvec2" => Ok(Primitive::Vector(Fundamental::Uint, 2)),
			"uvec3" => Ok(Primitive::Vector(Fundamental::Uint, 3)),
			"uvec4" => Ok(Primitive::Vector(Fundamental::Uint, 4)),
			"dvec2" => Ok(Primitive::Vector(Fundamental::Double, 2)),
			"dvec3" => Ok(Primitive::Vector(Fundamental::Double, 3)),
			"dvec4" => Ok(Primitive::Vector(Fundamental::Double, 4)),
			"mat2" => Ok(Primitive::Matrix(2, 2)),
			"mat2x2" => Ok(Primitive::Matrix(2, 2)),
			"mat2x3" => Ok(Primitive::Matrix(2, 3)),
			"mat2x4" => Ok(Primitive::Matrix(2, 4)),
			"mat3x2" => Ok(Primitive::Matrix(3, 2)),
			"mat3" => Ok(Primitive::Matrix(3, 3)),
			"mat3x3" => Ok(Primitive::Matrix(3, 3)),
			"mat3x4" => Ok(Primitive::Matrix(3, 4)),
			"mat4x2" => Ok(Primitive::Matrix(4, 2)),
			"mat4x3" => Ok(Primitive::Matrix(4, 3)),
			"mat4" => Ok(Primitive::Matrix(4, 4)),
			"mat4x4" => Ok(Primitive::Matrix(4, 4)),
			"dmat2" => Ok(Primitive::DMatrix(2, 2)),
			"dmat2x2" => Ok(Primitive::DMatrix(2, 2)),
			"dmat2x3" => Ok(Primitive::DMatrix(2, 3)),
			"dmat2x4" => Ok(Primitive::DMatrix(2, 4)),
			"dmat3x2" => Ok(Primitive::DMatrix(3, 2)),
			"dmat3" => Ok(Primitive::DMatrix(3, 3)),
			"dmat3x3" => Ok(Primitive::DMatrix(3, 3)),
			"dmat3x4" => Ok(Primitive::DMatrix(3, 4)),
			"dmat4x2" => Ok(Primitive::DMatrix(4, 2)),
			"dmat4x3" => Ok(Primitive::DMatrix(4, 3)),
			"dmat4" => Ok(Primitive::DMatrix(4, 4)),
			"dmat4x4" => Ok(Primitive::DMatrix(4, 4)),
			_ => Err(()),
		}
	}

	pub fn parse_var(s: &str) -> Result<Self, ()> {
		if s == "void" {
			return Err(());
		}

		Self::parse(s)
	}
}

/// A built-in language type.
#[derive(Debug, Clone)]
pub enum Type {
	/// A type which has only a single value.
	Basic(Either<Primitive, Ident>),
	/// An array type which contains zero or more values.
	Array(Either<Primitive, Ident>, Option<Either<usize, Ident>>),
	/// A 2D array type which contains zero or more values.
	///
	/// - `1` - Size of array,
	/// - `2` - Size of each element in array.
	Array2D(
		Either<Primitive, Ident>,
		Option<Either<usize, Ident>>,
		Option<Either<usize, Ident>>,
	),
	/// An n-dimensional array type which contains zero or more values.
	///
	/// - `1` - Vec containing the sizes of arrays, starting with the top-most array.
	ArrayND(Either<Primitive, Ident>, Vec<Option<Either<usize, Ident>>>),
}

impl std::fmt::Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		fn format_ident(ident: &Either<Primitive, Ident>) -> String {
			match ident {
				Either::Left(p) => format!("\x1b[91m{p}\x1b[0m"),
				Either::Right(i) => format!("\x1b[36m{i}\x1b[0m"),
			}
		}
		fn format_size(size: &Option<Either<usize, Ident>>) -> String {
			if let Some(inner) = size {
				match inner {
					Either::Left(n) => format!("{n}"),
					Either::Right(i) => format!("{i}"),
				}
			} else {
				"".to_owned()
			}
		}
		match self {
			Type::Basic(t) => write!(f, "{}", format_ident(t)),
			Type::Array(t, i) => {
				write!(f, "{}[{}]", format_ident(t), format_size(i))
			}
			Type::Array2D(t, i, j) => {
				write!(
					f,
					"{}[{}][{}]",
					format_ident(t),
					format_size(i),
					format_size(j)
				)
			}
			Type::ArrayND(t, v) => write!(f, "{}[{v:?}]", format_ident(t)),
		}
	}
}

impl Type {
	pub fn new(
		ident: Either<Primitive, Ident>,
		mut sizes: Vec<Option<Either<usize, Ident>>>,
	) -> Self {
		match sizes.len() {
			0 => Self::Basic(ident),
			1 => {
				let i = sizes.remove(0);
				Self::Array(ident, i)
			}
			2 => {
				let i = sizes.remove(0);
				let j = sizes.remove(0);
				Self::Array2D(ident, i, j)
			}
			_ => Self::ArrayND(ident, sizes),
		}
	}
}
