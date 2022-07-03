use crate::{
	lexer::{NumType, Op, Token},
	Either,
};

/// An expression which will be part of an encompassing statement. Expressions cannot exist on their own.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
	/// An expression which is incomplete, e.g. `3+5-`.
	///
	/// This token exists to allow the analyzer to gracefully deal with expression errors without affecting the
	/// ability to deal with surrounding expressions or statements. E.g.
	/// ```c
	/// int i = 3+5-;
	///
	/// // becomes
	///
	/// Expr::Binary {
	///     left: Expr::Lit(3),
	///     op: Add
	///     right: Expr::Incomplete
	/// }
	/// ```
	/// We can produce an error about the incomplete expression but still reason about the existence of `i`, such
	/// as in later uses. Obviously however, we cannot analyze whether the expression evaluates to a valid integer
	/// value.
	///
	/// This token is also used to represent unclosed delimiter groups, e.g.
	/// ```c
	/// fn(1+2
	///
	/// // or
	///
	/// i[0
	/// ```
	///
	/// Note: This token is not used for unclosed parenthesis groups, e.g.
	/// ```c
	/// (5+1
	///
	/// // becomes
	///
	/// Expr:: Binary {
	///     left: Expr::Lit(5),
	///     op: Add,
	///     right: Expr::Lit(1)
	/// }
	/// ```
	/// We produce an error about the missing parenthesis, but we can assume that the bracket group extends till
	/// the end. This is because whilst the position of the closing parenthesis may be unknown, no matter where it
	/// is placed it will not affect the analysis; either the types match or they don't. (It will affect the result
	/// of the evaluation but that is irrelevant to our analysis).
	Incomplete,
	/// An expression which is invalid when converted from a token, e.g.
	///
	/// - A token number `1.0B` cannot be converted to a valid `Lit` because `B` is not a valid suffix,.
	Invalid,
	/// A literal value; either a number or a boolean.
	Lit(Lit),
	/// An identifier; could be a variable name, function name, type name, etc.
	Ident(Ident),
	/// A prefix.
	Prefix(Box<Expr>, Op),
	/// A postfix.
	Postfix(Box<Expr>, Op),
	/// A negation.
	Neg(Box<Expr>),
	/// A bitflip.
	Flip(Box<Expr>),
	/// A not.
	Not(Box<Expr>),
	/// Binary expression with a left and right hand-side.
	Binary {
		left: Box<Expr>,
		op: Op,
		right: Box<Expr>,
	},
	/// Ternary condition.
	Ternary {
		cond: Box<Expr>,
		true_: Box<Expr>,
		false_: Box<Expr>,
	},
	/// A parenthesis group. *Note:* currently this has no real use.
	Paren(Box<Expr>),
	/// Index operator, e.g. `item[i]`.
	Index {
		item: Box<Expr>,
		i: Option<Box<Expr>>,
	},
	/// Object access.
	ObjAccess { obj: Box<Expr>, leaf: Box<Expr> },
	/// Function call.
	Fn { ident: Ident, args: Vec<Expr> },
	/// Initializer list.
	Init(Vec<Expr>),
	/// Array constructor.
	ArrInit {
		/// Contains the first part of an array constructor, e.g. `int[3]`.
		arr: Box<Expr>,
		/// Contains the expressions within the brackets i.e. `..](a, b, ...)`.
		args: Vec<Expr>,
	},
	/// A general list expression, e.g. `a, b`.
	List(Vec<Expr>),
}

impl std::fmt::Display for Expr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Incomplete => write!(f, "\x1b[31;4mINCOMPLETE\x1b[0m"),
			Expr::Invalid => write!(f, "\x1b[31;4mINVALID\x1b[0m"),
			Expr::Lit(l) => write!(f, "{l}"),
			Expr::Ident(i) => write!(f, "{i}"),
			Expr::Prefix(expr, op) => {
				write!(f, "\x1b[36mPre\x1b[0m({expr} \x1b[36m{op:?}\x1b[0m)")
			}
			Expr::Postfix(expr, op) => {
				write!(f, "\x1b[36mPost\x1b[0m({expr} \x1b[36m{op:?}\x1b[0m)")
			}
			Expr::Neg(expr) => write!(f, "\x1b[36mNeg\x1b[0m({expr})"),
			Expr::Flip(expr) => write!(f, "\x1b[36mFlip\x1b[0m({expr})"),
			Expr::Not(expr) => write!(f, "\x1b[36mNot\x1b[0m({expr})"),
			Expr::Binary { left, op, right } => {
				write!(f, "({left} \x1b[36m{op:?}\x1b[0m {right})")
			}
			Expr::Ternary {
				cond,
				true_,
				false_,
			} => write!(f, "IF({cond}) {{ {true_} }} ELSE {{ {false_} }}"),
			Expr::Paren(expr) => write!(f, "({expr})"),
			Expr::Index { item, i } => {
				write!(
					f,
					"\x1b[36mIndex\x1b[0m({item}, i: {})",
					if let Some(e) = i {
						format!("{e}")
					} else {
						format!("_")
					}
				)
			}
			Expr::ObjAccess { obj, leaf } => {
				write!(f, "\x1b[36mAccess\x1b[0m({obj} -> {leaf})")
			}
			Expr::Fn { ident, args } => {
				write!(f, "\x1b[34mCall\x1b[0m(ident: {ident}, args: [")?;
				for arg in args {
					write!(f, "{arg}, ")?;
				}
				write!(f, "])")
			}
			Expr::Init(args) => {
				write!(f, "\x1b[34mInit\x1b[0m{{")?;
				for arg in args {
					write!(f, "{arg}, ")?;
				}
				write!(f, "}}")
			}
			Expr::ArrInit { arr, args } => {
				write!(f, "\x1b[34mArr\x1b[0m(arr: {arr} args: [")?;
				for arg in args {
					write!(f, "{arg}, ")?;
				}
				write!(f, "])")
			}
			Expr::List(exprs) => {
				write!(f, "{{")?;
				for expr in exprs {
					write!(f, "{expr}, ")?;
				}
				write!(f, "}}")
			}
		}
	}
}

impl Expr {
	/// Tries to create a `Type`.
	pub fn to_type(&self) -> Option<Type> {
		Type::parse(self)
	}

	/// Tries to create a variable declarations.
	pub fn to_var_decl(&self) -> Vec<Either<Ident, (Ident, Vec<ArrSize>)>> {
		let mut idents = Vec::new();

		match self {
			Self::List(v) => {
				for expr in v {
					match Ident::from_expr(expr) {
						Some(result) => idents.push(result),
						None => {}
					}
				}
			}
			_ => match Ident::from_expr(self) {
				Some(result) => idents.push(result),
				None => {}
			},
		}

		idents
	}
}

/// A top-level statement. Some of these statements are only valid at the file top-level. Others are only valid
/// inside of functions.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
	/// An empty statement, i.e. just a `;`.
	Empty,
	/// Variable definition.
	VarDef { type_: Type, ident: Ident },
	/// Multiple variable definitions, e.g. `int a, b;`.
	VarDefs(Vec<(Type, Ident)>),
	/// Variable declaration.
	VarDecl {
		type_: Type,
		ident: Ident,
		value: Expr,
		is_const: bool, // TODO: Refactor to be a Vec<Qualifier> or something similar.
	},
	/// Multiple variable declarations, e.g. `int a, b = <EXPR>;`.
	VarDecls {
		vars: Vec<(Type, Ident)>,
		value: Expr,
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
	/// Variable assignment through `+=`/`-=`/etc. operators.
	VarEq {
		ident: Ident,
		value: Box<Expr>,
		op: Op,
	},
	/// Preprocessor calls.
	Preproc(Preproc),
	/// If statement.
	If {
		cond: Expr,
		body: Vec<Stmt>,
		else_ifs: Vec<(Expr, Vec<Stmt>)>,
		else_: Option<Vec<Stmt>>,
	},
	/// Switch statement.
	Switch {
		expr: Expr,
		/// `0` - If `None`, then this is a *default* case.
		cases: Vec<(Option<Expr>, Vec<Stmt>)>,
	},
	/// For statement.
	For {
		var: Option<Box<Stmt>>,
		cond: Option<Expr>,
		inc: Option<Expr>,
		body: Vec<Stmt>,
	},
	/// Return statement.
	Return(Option<Expr>),
	/// Break keyword.
	Break,
	/// Discard keyword.
	Discard,
}

/// A preprocessor directive.
#[derive(Debug, Clone, PartialEq)]
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
				"version: {version}, profile: {}",
				if *is_core { "core" } else { "compat" }
			),
			Preproc::Extension { name, behaviour } => {
				write!(f, "extension: {name}, behaviour: {behaviour:?}")
			}
			Preproc::Line { line, src_str } => {
				if let Some(src_str) = src_str {
					write!(f, "line: {line}, src-str: {src_str}")
				} else {
					write!(f, "line: {line}")
				}
			}
			Preproc::Include(s) => write!(f, "include: {s}"),
			Preproc::UnDef(s) => write!(f, "undef: {s}"),
			Preproc::IfDef(s) => write!(f, "ifdef: {s}"),
			Preproc::IfnDef(s) => write!(f, "ifndef: {s}"),
			Preproc::Else => write!(f, "else"),
			Preproc::EndIf => write!(f, "end"),
			Preproc::Error(s) => write!(f, "error: {s}"),
			Preproc::Pragma(s) => write!(f, "pragma: {s}"),
			Preproc::Unsupported => write!(f, "UNSUPPORTED"),
		}
	}
}

/// The valid options for the behaviour setting in a `#extension` directive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtBehaviour {
	Enable,
	Require,
	Warn,
	Disable,
}

/// A literal value.
#[derive(Debug, Clone, Copy, PartialEq)]
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
			Self::Bool(b) => write!(f, "\x1b[35m{}\x1b[0m", b.to_string()),
			Self::Int(i) => write!(f, "\x1b[35m{i}\x1b[0m"),
			Self::UInt(u) => write!(f, "\x1b[35m{u}\x1b[0m"),
			Self::Float(fp) => write!(f, "\x1b[35m{fp}\x1b[0m"),
			Self::Double(d) => write!(f, "\x1b[35m{d}\x1b[0m"),
		}
	}
}

impl Lit {
	pub fn parse(token: &Token) -> Result<Self, ()> {
		match token {
			Token::Bool(b) => Ok(Self::Bool(*b)),
			Token::Num {
				num: s,
				suffix,
				type_,
			} => Self::parse_num(&s, suffix.as_deref(), *type_),
			_ => Err(()),
		}
	}

	pub fn parse_num(
		s: &str,
		suffix: Option<&str>,
		type_: NumType,
	) -> Result<Self, ()> {
		// This can be empty, e.g. `0xu` is a `NumType::Hex` with contents `` with suffix `u`.
		if s == "" {
			return Err(());
		}
		match type_ {
			NumType::Dec => Self::parse_num_dec(s, suffix),
			NumType::Hex => Self::parse_num_hex(s, suffix),
			NumType::Oct => Self::parse_num_oct(s, suffix),
			NumType::Float => Self::parse_num_float(s, suffix),
		}
	}

	fn parse_num_dec(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 10) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 10) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_hex(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 16) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 16) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_oct(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 8) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 8) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_float(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "lf" || suffix == "LF" {
				if let Ok(f) = s.parse::<f64>() {
					return Ok(Self::Double(f));
				}
			} else if suffix == "f" || suffix == "F" {
				if let Ok(f) = s.parse::<f32>() {
					return Ok(Self::Float(f));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(f) = s.parse::<f32>() {
				return Ok(Self::Float(f));
			}
		}

		Err(())
	}
}

/// An identifier.
///
/// This can be a variable name, function name, etc.
#[derive(Debug, Clone, PartialEq)]
pub struct Ident(pub String);

impl std::fmt::Display for Ident {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "\x1b[33m{}\x1b[0m", self.0)
	}
}

impl Ident {
	fn from_expr(
		expr: &Expr,
	) -> Option<Either<Ident, (Ident, Vec<ArrSize>)>> {
		match expr {
			Expr::Ident(i) => Some(Either::Left(i.clone())),
			Expr::Index { item, i } => {
				let mut current_item = item;
				let mut stack = Vec::new();
				stack.push(i.as_deref());

				let ident = loop {
					match current_item.as_ref() {
						Expr::Ident(i) => {
							break i.clone();
						}
						Expr::Index { item, i } => {
							stack.push(i.as_deref());
							current_item = item;
						}
						_ => return None,
					};
				};

				// In the expression parser, the `[..]` brackets are right-associative, so the outer-most pair is
				// at the top, and the inner-most is at the bottom. We want to reverse this to be in line with our
				// intuition, i.e. 2nd dimension first, then 1st dimension.
				stack.reverse();

				Some(Either::Right((
					ident,
					stack.into_iter().map(|i| i.cloned()).collect(),
				)))
			}
			_ => None,
		}
	}
}

/// A fundamental type.
///
/// These are the most fundamental types in the language, on which all other types are composed.
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
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
	/// A struct type.
	Struct(Ident),
}

impl std::fmt::Display for Primitive {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Primitive::Scalar(ff) => write!(f, "{ff}"),
			Primitive::Vector(ff, size) => write!(f, "{ff}-vec-{size}"),
			Primitive::Matrix(i, j) => write!(f, "mat-{i}x{j}"),
			Primitive::DMatrix(i, j) => write!(f, "double-mat-{i}x{j}"),
			Primitive::Struct(i) => write!(f, "struct: {i}"),
		}
	}
}

impl Primitive {
	pub fn parse(ident: &Ident) -> Self {
		match ident.0.as_ref() {
			"void" => Primitive::Scalar(Fundamental::Void),
			"bool" => Primitive::Scalar(Fundamental::Bool),
			"int" => Primitive::Scalar(Fundamental::Int),
			"uint" => Primitive::Scalar(Fundamental::Uint),
			"float" => Primitive::Scalar(Fundamental::Float),
			"double" => Primitive::Scalar(Fundamental::Double),
			"vec2" => Primitive::Vector(Fundamental::Float, 2),
			"vec3" => Primitive::Vector(Fundamental::Float, 3),
			"vec4" => Primitive::Vector(Fundamental::Float, 4),
			"bvec2" => Primitive::Vector(Fundamental::Bool, 2),
			"bvec3" => Primitive::Vector(Fundamental::Bool, 3),
			"bvec4" => Primitive::Vector(Fundamental::Bool, 4),
			"ivec2" => Primitive::Vector(Fundamental::Int, 2),
			"ivec3" => Primitive::Vector(Fundamental::Int, 3),
			"ivec4" => Primitive::Vector(Fundamental::Int, 4),
			"uvec2" => Primitive::Vector(Fundamental::Uint, 2),
			"uvec3" => Primitive::Vector(Fundamental::Uint, 3),
			"uvec4" => Primitive::Vector(Fundamental::Uint, 4),
			"dvec2" => Primitive::Vector(Fundamental::Double, 2),
			"dvec3" => Primitive::Vector(Fundamental::Double, 3),
			"dvec4" => Primitive::Vector(Fundamental::Double, 4),
			"mat2" => Primitive::Matrix(2, 2),
			"mat2x2" => Primitive::Matrix(2, 2),
			"mat2x3" => Primitive::Matrix(2, 3),
			"mat2x4" => Primitive::Matrix(2, 4),
			"mat3x2" => Primitive::Matrix(3, 2),
			"mat3" => Primitive::Matrix(3, 3),
			"mat3x3" => Primitive::Matrix(3, 3),
			"mat3x4" => Primitive::Matrix(3, 4),
			"mat4x2" => Primitive::Matrix(4, 2),
			"mat4x3" => Primitive::Matrix(4, 3),
			"mat4" => Primitive::Matrix(4, 4),
			"mat4x4" => Primitive::Matrix(4, 4),
			"dmat2" => Primitive::DMatrix(2, 2),
			"dmat2x2" => Primitive::DMatrix(2, 2),
			"dmat2x3" => Primitive::DMatrix(2, 3),
			"dmat2x4" => Primitive::DMatrix(2, 4),
			"dmat3x2" => Primitive::DMatrix(3, 2),
			"dmat3" => Primitive::DMatrix(3, 3),
			"dmat3x3" => Primitive::DMatrix(3, 3),
			"dmat3x4" => Primitive::DMatrix(3, 4),
			"dmat4x2" => Primitive::DMatrix(4, 2),
			"dmat4x3" => Primitive::DMatrix(4, 3),
			"dmat4" => Primitive::DMatrix(4, 4),
			"dmat4x4" => Primitive::DMatrix(4, 4),
			_ => Primitive::Struct(ident.clone()),
		}
	}
}

type ArrSize = Option<Expr>;

/// A built-in language type.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
	/// A type which has only a single value.
	Basic(Primitive),
	/// An array type which contains zero or more values.
	Array(Primitive, ArrSize),
	/// A 2D array type which contains zero or more values.
	///
	/// - `1` - Size of the outer array,
	/// - `2` - Size of each inner array.
	Array2D(Primitive, ArrSize, ArrSize),
	/// An n-dimensional array type which contains zero or more values.
	///
	/// - `1` - Vec containing the sizes of arrays, starting with the outer-most array.
	ArrayND(Primitive, Vec<ArrSize>),
}

impl std::fmt::Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		fn format_size(i: &Option<Expr>) -> String {
			if let Some(inner) = i {
				format!("{inner}")
			} else {
				"".to_owned()
			}
		}
		match self {
			Type::Basic(t) => write!(f, "\x1b[91m{t}\x1b[0m"),
			Type::Array(t, i) => {
				write!(f, "\x1b[91m{t}\x1b[0m[{}]", format_size(i))
			}
			Type::Array2D(t, i, j) => {
				write!(
					f,
					"\x1b[91m{t}\x1b[0m[{}][{}]",
					format_size(i),
					format_size(j)
				)
			}
			Type::ArrayND(t, v) => {
				write!(f, "\x1b[91m{t}\x1b[0m")?;
				for v in v {
					if let Some(expr) = v {
						write!(f, "[{expr}]")?;
					} else {
						write!(f, "[]")?;
					}
				}
				Ok(())
			}
		}
	}
}

impl Type {
	pub fn parse(expr: &Expr) -> Option<Self> {
		match expr {
			Expr::Ident(i) => Some(Self::Basic(Primitive::parse(i))),
			Expr::Index { item, i } => {
				let mut current_item = item;
				let mut stack = Vec::new();
				stack.push(i.as_deref());

				let primitive = loop {
					match current_item.as_ref() {
						Expr::Ident(i) => {
							break Primitive::parse(i);
						}
						Expr::Index { item, i } => {
							stack.push(i.as_deref());
							current_item = item;
						}
						_ => return None,
					};
				};

				// In the expression parser, the `[..]` brackets are right-associative, so the outer-most pair is
				// at the top, and the inner-most is at the bottom. We want to reverse this to be in line with our
				// intuition, i.e. 2nd dimension first, then 1st dimension.
				stack.reverse();

				if stack.len() == 1 {
					Some(Self::Array(primitive, stack[0].cloned()))
				} else if stack.len() == 2 {
					Some(Self::Array2D(
						primitive,
						stack[0].cloned(),
						stack[1].cloned(),
					))
				} else {
					Some(Self::ArrayND(
						primitive,
						stack.into_iter().map(|i| i.cloned()).collect(),
					))
				}
			}
			_ => None,
		}
	}

	pub fn add_var_decl_arr_size(self, mut sizes: Vec<ArrSize>) -> Self {
		let primitive = match self {
			Self::Basic(p) => p,
			Self::Array(p, i) => {
				sizes.push(i);
				p
			}
			Self::Array2D(p, i, j) => {
				sizes.push(i);
				sizes.push(j);
				p
			}
			Self::ArrayND(p, mut v) => {
				sizes.append(&mut v);
				p
			}
		};

		if sizes.len() == 0 {
			Self::Basic(primitive)
		} else if sizes.len() == 1 {
			Self::Array(primitive, sizes.remove(0))
		} else if sizes.len() == 2 {
			Self::Array2D(primitive, sizes.remove(0), sizes.remove(0))
		} else {
			Self::ArrayND(primitive, sizes)
		}
	}
}
