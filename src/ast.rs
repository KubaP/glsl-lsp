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
	/// Tries to convert this `Expr` to a [`Type`], e.g. `int` or `MyStruct` or `float[3][2]`.
	pub fn to_type(&self) -> Option<Type> {
		Type::parse(self)
	}

	/// Tries to convert this `Expr` to variable definition/declaration identifiers, e.g. `my_num` or `a, b` or
	/// `c[1], p[3]`.
	///
	/// Each entry is either just an [`Ident`] if the expression is something like `my_num`, or it is an `Ident`
	/// plus one or more [`ArrSize`] if the expression is something like `a[1]` or `b[][3]`.
	pub fn to_var_def_decl_or_fn_ident(
		&self,
	) -> Vec<Either<Ident, (Ident, Vec<ArrSize>)>> {
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

type Param = (Type, Option<Ident>, Vec<Qualifier>);

/// A top-level statement. Some of these statements are only valid at the file top-level. Others are only valid
/// inside of functions.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
	/// An empty statement, i.e. just a `;`.
	Empty,
	/// Variable definition, e.g. `int a;`.
	VarDef {
		type_: Type,
		ident: Ident,
		qualifiers: Vec<Qualifier>,
	},
	/// Multiple variable definitions, e.g. `int a, b;`.
	VarDefs(Vec<(Type, Ident)>, Vec<Qualifier>),
	/// Variable declaration, e.g. `int a = <EXPR>;`.
	VarDecl {
		type_: Type,
		ident: Ident,
		value: Expr,
		qualifiers: Vec<Qualifier>,
	},
	/// Multiple variable declarations, e.g. `int a, b = <EXPR>;`.
	VarDecls {
		vars: Vec<(Type, Ident)>,
		value: Expr,
		qualifiers: Vec<Qualifier>,
	},
	/// Function definition.
	FnDef {
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
		qualifiers: Vec<Qualifier>,
	},
	/// Function declaration.
	FnDecl {
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
		body: Vec<Stmt>,
		qualifiers: Vec<Qualifier>,
	},
	/// Struct definition. *Note:* This is invalid glsl grammar.
	StructDef {
		ident: Ident,
		qualifiers: Vec<Qualifier>,
	},
	/// Struct declaration.
	StructDecl {
		ident: Ident,
		/// # Invariants
		/// These will only be of type `Stmt::VarDef` or `Stmt::VarDefs`.
		members: Vec<Stmt>,
		qualifiers: Vec<Qualifier>,
		instance: Option<Ident>,
	},
	/// General expression, e.g.
	/// 
	/// - `i + 5;`
	/// - `fn();`
	/// - `i = 5 + 1;`
	/// - `i *= fn();`
	Expr(Expr),
	/// General scope, e.g.
	/// ```glsl
	/// /* .. */
	/// {
	/// 	/* new scope */
	/// }
	/// ```
	Scope(Vec<Stmt>),
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
	/// While loop, i.e. `while ( /*..*/ ) { /*..*/ }`.
	While { cond: Expr, body: Vec<Stmt> },
	/// Do-While loop, i.e. `do { /*..*/ } while ( /*..*/ );`.
	DoWhile { cond: Expr, body: Vec<Stmt> },
	/// Return statement.
	Return(Option<Expr>),
	/// Break keyword.
	Break,
	/// Continue keyword.
	Continue,
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
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExtBehaviour {
	Enable,
	Require,
	Warn,
	Disable,
}

/// A qualifier which is associated with a definition/declaration or a parameter.
#[derive(Debug, Clone, PartialEq)]
pub enum Qualifier {
	Storage(Storage),
	Layout(Vec<Layout>),
	Interpolation(Interpolation),
	Precision,
	Invariant,
	Precise,
	Memory(Memory),
}

impl std::fmt::Display for Qualifier {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Storage(s) => write!(
				f,
				"\x1b[95m{}\x1b[0m",
				match s {
					Storage::Const => "const",
					Storage::In => "in",
					Storage::Out => "out",
					Storage::InOut => "inout",
					Storage::Attribute => "attribute",
					Storage::Uniform => "uniform",
					Storage::Varying => "varying",
					Storage::Buffer => "buffer",
					Storage::Shared => "shared",
					Storage::Centroid => "centroid",
					Storage::Sample => "sample",
					Storage::Patch => "patch",
				}
			),
			Self::Layout(v) => {
				write!(f, "\x1b[95mlayout\x1b[0m: [")?;
				for l in v {
					write!(f, "{l}, ")?;
				}
				write!(f, "]")
			}
			Self::Interpolation(i) => write!(
				f,
				"\x1b[95m{}\x1b[0m",
				match i {
					Interpolation::Smooth => "smooth",
					Interpolation::Flat => "flat",
					Interpolation::NoPerspective => "noperspective",
				}
			),
			Self::Precision => write!(f, "\x1b[90;9mprecision\x1b[0m"),
			Self::Invariant => write!(f, "\x1b[95minvariant\x1b[0m"),
			Self::Precise => write!(f, "\x1b[95mprecise\x1b[0m"),
			Self::Memory(m) => write!(
				f,
				"\x1b[95m{}\x1b[0m",
				match m {
					Memory::Coherent => "coherent",
					Memory::Volatile => "volatile",
					Memory::Restrict => "restrict",
					Memory::Readonly => "readonly",
					Memory::Writeonly => "writeonly",
				}
			),
		}
	}
}

#[derive(Debug, Clone, PartialEq)]
pub enum Storage {
	Const,
	In,
	Out,
	InOut,
	Attribute,
	Uniform,
	Varying,
	Buffer,
	Shared,
	Centroid,
	Sample,
	Patch,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Interpolation {
	Smooth,
	Flat,
	NoPerspective,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Memory {
	Coherent,
	Volatile,
	Restrict,
	Readonly,
	Writeonly,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Layout {
	Shared,
	Packed,
	Std140,
	Std430,
	RowMajor,
	ColumnMajor,
	Binding(Expr),
	Offset(Expr),
	Align(Expr),
	Location(Expr),
	Component(Expr),
	Index(Expr),
	Points,
	Lines,
	Isolines,
	Triangles,
	Quads,
	EqualSpacing,
	FractionalEvenSpacing,
	FractionalOddSpacing,
	Clockwise,
	CounterClockwise,
	PointMode,
	LinesAdjacency,
	TrianglesAdjacency,
	Invocations(Expr),
	OriginUpperLeft,
	PixelCenterInteger,
	EarlyFragmentTests,
	LocalSizeX(Expr),
	LocalSizeY(Expr),
	LocalSizeZ(Expr),
	XfbBuffer(Expr),
	XfbStride(Expr),
	XfbOffset(Expr),
	Vertices(Expr),
	LineStrip,
	TriangleStrip,
	MaxVertices(Expr),
	Stream(Expr),
	DepthAny,
	DepthGreater,
	DepthLess,
	DepthUnchanged,
}

impl std::fmt::Display for Layout {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Shared => write!(f, "shared"),
			Self::Packed => write!(f, "packed"),
			Self::Std140 => write!(f, "std140"),
			Self::Std430 => write!(f, "std430"),
			Self::RowMajor => write!(f, "row-major"),
			Self::ColumnMajor => write!(f, "column-major"),
			Self::Binding(e) => write!(f, "binding = {e}"),
			Self::Offset(e) => write!(f, "offset = {e}"),
			Self::Align(e) => write!(f, "align = {e}"),
			Self::Location(e) => write!(f, "location = {e}"),
			Self::Component(e) => write!(f, "component = {e}"),
			Self::Index(e) => write!(f, "index = {e}"),
			Self::Points => write!(f, "points"),
			Self::Lines => write!(f, "lines"),
			Self::Isolines => write!(f, "isolines"),
			Self::Triangles => write!(f, "triangles"),
			Self::Quads => write!(f, "quads"),
			Self::EqualSpacing => write!(f, "equal-spacing"),
			Self::FractionalEvenSpacing => write!(f, "fragment-even-spacing"),
			Self::FractionalOddSpacing => write!(f, "fragment-odd-spacing"),
			Self::Clockwise => write!(f, "clockwise"),
			Self::CounterClockwise => write!(f, "counter-clockwise"),
			Self::PointMode => write!(f, "point-mode"),
			Self::LinesAdjacency => write!(f, "lines-adjacency"),
			Self::TrianglesAdjacency => write!(f, "triangles-adjacency"),
			Self::Invocations(e) => write!(f, "invocations = {e}"),
			Self::OriginUpperLeft => write!(f, "origin-upper-left"),
			Self::PixelCenterInteger => write!(f, "pixel-center-integer"),
			Self::EarlyFragmentTests => write!(f, "early-fragment-tests"),
			Self::LocalSizeX(e) => write!(f, "local-size-x = {e}"),
			Self::LocalSizeY(e) => write!(f, "local-size-y = {e}"),
			Self::LocalSizeZ(e) => write!(f, "local-size-z = {e}"),
			Self::XfbBuffer(e) => write!(f, "xfb-buffer = {e}"),
			Self::XfbStride(e) => write!(f, "xfb-stride = {e}"),
			Self::XfbOffset(e) => write!(f, "xfb-offset = {e}"),
			Self::Vertices(e) => write!(f, "vertices = {e}"),
			Self::LineStrip => write!(f, "line-strip"),
			Self::TriangleStrip => write!(f, "triangle-strip"),
			Self::MaxVertices(e) => write!(f, "max-vertices = {e}"),
			Self::Stream(e) => write!(f, "stream = {e}"),
			Self::DepthAny => write!(f, "depth-any"),
			Self::DepthGreater => write!(f, "depth-greater"),
			Self::DepthLess => write!(f, "depth-less"),
			Self::DepthUnchanged => write!(f, "depth-unchanged"),
		}
	}
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
	fn from_expr(expr: &Expr) -> Option<Either<Ident, (Ident, Vec<ArrSize>)>> {
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

/// A texture type of a `sampler_` or `image_` type.
#[derive(Debug, Clone, PartialEq)]
pub enum TexType {
	D1,
	D2,
	D3,
	Cube,
	Rect2D,
	Array1D,
	Array2D,
	CubeArray,
	Buffer,
	Multisample2D,
	MultisampleArray2D,

	ShadowD1,
	ShadowD2,
	ShadowD3,
	ShadowCube,
	ShadowRect2D,
	ShadowArray1D,
	ShadowArray2D,
	ShadowCubeArray,
}

impl std::fmt::Display for TexType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			TexType::D1 => write!(f, "1D"),
			TexType::D2 => write!(f, "2D"),
			TexType::D3 => write!(f, "3D"),
			TexType::Cube => write!(f, "Cube"),
			TexType::Rect2D => write!(f, "2DRect"),
			TexType::Array1D => write!(f, "1DArray"),
			TexType::Array2D => write!(f, "2DArray"),
			TexType::CubeArray => write!(f, "CubeArray"),
			TexType::Buffer => write!(f, "Buffer"),
			TexType::Multisample2D => write!(f, "2DMS"),
			TexType::MultisampleArray2D => write!(f, "2DMSArray"),
			TexType::ShadowD1 => write!(f, "1DShadow"),
			TexType::ShadowD2 => write!(f, "2DShadow"),
			TexType::ShadowD3 => write!(f, "3DShadow"),
			TexType::ShadowCube => write!(f, "CubeShadow"),
			TexType::ShadowRect2D => write!(f, "2DRectShadow"),
			TexType::ShadowArray1D => write!(f, "1DArrayShadow"),
			TexType::ShadowArray2D => write!(f, "2DArrayShadow"),
			TexType::ShadowCubeArray => write!(f, "CubeArrayShadow"),
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
	/// A sampler type.
	///
	/// - `0` - Data type.
	/// - `1` - Texture type.
	///
	/// # Invariants
	/// - The data type is guaranteed to be one of `Fundamental::Float|Int|Uint`.
	Sampler(Fundamental, TexType),
	/// An image type.
	///
	/// - `0` - Data type.
	/// - `1` - Texture type.
	///
	/// # Invariants
	/// - The data type is guaranteed to be one of `Fundamental::Float|Int|Uint`.
	/// - The texture type is guaranteed to be none of the `TexType::Shadow*` variants.
	Image(Fundamental, TexType),
	Atomic,
}

impl std::fmt::Display for Primitive {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Primitive::Scalar(ff) => write!(f, "{ff}"),
			Primitive::Vector(ff, size) => write!(f, "{ff}-vec-{size}"),
			Primitive::Matrix(i, j) => write!(f, "mat-{i}x{j}"),
			Primitive::DMatrix(i, j) => write!(f, "double-mat-{i}x{j}"),
			Primitive::Struct(i) => write!(f, "struct: {i}"),
			Primitive::Sampler(ff, t) => {
				write!(f, "sampler-")?;
				match ff {
					Fundamental::Float => {}
					Fundamental::Int => write!(f, "int-")?,
					Fundamental::Uint => write!(f, "uint-")?,
					_ => unreachable!(),
				}
				write!(f, "{t}")
			}
			Primitive::Image(ff, t) => {
				write!(f, "image-")?;
				match ff {
					Fundamental::Float => {}
					Fundamental::Int => write!(f, "int-")?,
					Fundamental::Uint => write!(f, "uint-")?,
					_ => unreachable!(),
				}
				write!(f, "{t}")
			}
			Primitive::Atomic => write!(f, "atomic"),
		}
	}
}

impl Primitive {
	#[rustfmt::skip]
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
			"sampler1D" => Primitive::Sampler(Fundamental::Float, TexType::D1),
			"sampler2D" => Primitive::Sampler(Fundamental::Float, TexType::D2),
			"sampler3D" => Primitive::Sampler(Fundamental::Float, TexType::D3),
			"samplerCube" => Primitive::Sampler(Fundamental::Float, TexType::Cube),
			"sampler2DRect" => Primitive::Sampler(Fundamental::Float, TexType::Rect2D),
			"sampler1DArray" => Primitive::Sampler(Fundamental::Float, TexType::Array1D),
			"sampler2DArray" => Primitive::Sampler(Fundamental::Float, TexType::Array2D),
			"samplerCubeArray" => Primitive::Sampler(Fundamental::Float, TexType::CubeArray),
			"samplerBuffer" => Primitive::Sampler(Fundamental::Float, TexType::Buffer),
			"sampler2DMS" => Primitive::Sampler(Fundamental::Float, TexType::Multisample2D),
			"sampler2DMSArray" => Primitive::Sampler(Fundamental::Float, TexType::MultisampleArray2D),
			"isampler1D" => Primitive::Sampler(Fundamental::Int, TexType::D1),
			"isampler2D" => Primitive::Sampler(Fundamental::Int, TexType::D2),
			"isampler3D" => Primitive::Sampler(Fundamental::Int, TexType::D3),
			"isamplerCube" => Primitive::Sampler(Fundamental::Int, TexType::Cube),
			"isampler2DRect" => Primitive::Sampler(Fundamental::Int, TexType::Rect2D),
			"isampler1DArray" => Primitive::Sampler(Fundamental::Int, TexType::Array1D),
			"isampler2DArray" => Primitive::Sampler(Fundamental::Int, TexType::Array2D),
			"isamplerCubeArray" => Primitive::Sampler(Fundamental::Int, TexType::CubeArray),
			"isamplerBuffer" => Primitive::Sampler(Fundamental::Int, TexType::Buffer),
			"isampler2DMS" => Primitive::Sampler(Fundamental::Int, TexType::Multisample2D),
			"isampler2DMSArray" => Primitive::Sampler(Fundamental::Int, TexType::MultisampleArray2D),
			"usampler1D" => Primitive::Sampler(Fundamental::Uint, TexType::D1),
			"usampler2D" => Primitive::Sampler(Fundamental::Uint, TexType::D2),
			"usampler3D" => Primitive::Sampler(Fundamental::Uint, TexType::D3),
			"usamplerCube" => Primitive::Sampler(Fundamental::Uint, TexType::Cube),
			"usampler2DRect" => Primitive::Sampler(Fundamental::Uint, TexType::Rect2D),
			"usampler1DArray" => Primitive::Sampler(Fundamental::Uint, TexType::Array1D),
			"usampler2DArray" => Primitive::Sampler(Fundamental::Uint, TexType::Array2D),
			"usamplerCubeArray" => Primitive::Sampler(Fundamental::Uint, TexType::CubeArray),
			"usamplerBuffer" => Primitive::Sampler(Fundamental::Uint, TexType::Buffer),
			"usampler2DMS" => Primitive::Sampler(Fundamental::Uint, TexType::Multisample2D),
			"usampler2DMSArray" => Primitive::Sampler(Fundamental::Uint, TexType::MultisampleArray2D),
			"sampler1DShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowD1),
			"sampler2DShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowD2),
			"samplerCubeShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowCube),
			"sampler2DRectShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowRect2D),
			"sampler1DArrayShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowArray1D),
			"sampler2DArrayShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowArray2D),
			"samplerCubeArrayShadow" => Primitive::Sampler(Fundamental::Float, TexType::ShadowCubeArray),
			"image1D" => Primitive::Image(Fundamental::Float, TexType::D1),
			"image2D" => Primitive::Image(Fundamental::Float, TexType::D2),
			"image3D" => Primitive::Image(Fundamental::Float, TexType::D3),
			"imageCube" => Primitive::Image(Fundamental::Float, TexType::Cube),
			"image2DRect" => Primitive::Image(Fundamental::Float, TexType::Rect2D),
			"image1DArray" => Primitive::Image(Fundamental::Float, TexType::Array1D),
			"image2DArray" => Primitive::Image(Fundamental::Float, TexType::Array2D),
			"imageCubeArray" => Primitive::Image(Fundamental::Float, TexType::CubeArray),
			"imageBuffer" => Primitive::Image(Fundamental::Float, TexType::Buffer),
			"image2DMS" => Primitive::Image(Fundamental::Float, TexType::Multisample2D),
			"image2DMSArray" => Primitive::Image(Fundamental::Float, TexType::MultisampleArray2D),
			"iimage1D" => Primitive::Image(Fundamental::Int, TexType::D1),
			"iimage2D" => Primitive::Image(Fundamental::Int, TexType::D2),
			"iimage3D" => Primitive::Image(Fundamental::Int, TexType::D3),
			"iimageCube" => Primitive::Image(Fundamental::Int, TexType::Cube),
			"iimage2DRect" => Primitive::Image(Fundamental::Int, TexType::Rect2D),
			"iimage1DArray" => Primitive::Image(Fundamental::Int, TexType::Array1D),
			"iimage2DArray" => Primitive::Image(Fundamental::Int, TexType::Array2D),
			"iimageCubeArray" => Primitive::Image(Fundamental::Int, TexType::CubeArray),
			"iimageBuffer" => Primitive::Image(Fundamental::Int, TexType::Buffer),
			"iimage2DMS" => Primitive::Image(Fundamental::Int, TexType::Multisample2D),
			"iimage2DMSArray" => Primitive::Image(Fundamental::Int, TexType::MultisampleArray2D),
			"uimage1D" => Primitive::Image(Fundamental::Uint, TexType::D1),
			"uimage2D" => Primitive::Image(Fundamental::Uint, TexType::D2),
			"uimage3D" => Primitive::Image(Fundamental::Uint, TexType::D3),
			"uimageCube" => Primitive::Image(Fundamental::Uint, TexType::Cube),
			"uimage2DRect" => Primitive::Image(Fundamental::Uint, TexType::Rect2D),
			"uimage1DArray" => Primitive::Image(Fundamental::Uint, TexType::Array1D),
			"uimage2DArray" => Primitive::Image(Fundamental::Uint, TexType::Array2D),
			"uimageCubeArray" => Primitive::Image(Fundamental::Uint, TexType::CubeArray),
			"uimageBuffer" => Primitive::Image(Fundamental::Uint, TexType::Buffer),
			"uimage2DMS" => Primitive::Image(Fundamental::Uint, TexType::Multisample2D),
			"uimage2DMSArray" => Primitive::Image(Fundamental::Uint, TexType::MultisampleArray2D),
			"atomic_uint" => Primitive::Atomic,
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
