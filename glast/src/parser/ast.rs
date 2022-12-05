//! Abstract syntax tree types and functionality.
//!
//! There are a lot of types used to represent specific things. Some common ones worth mentioning:
//! - [`Node`] and [`NodeTy`] - A node representing a statement.
//! - [`Expr`] and [`ExprTy`] - A node representing an expression; this will never be found standalone but part of
//!   a `Node` of some kind.
//! - [`Ident`] - A general identifier of some kind.
//! - [`Omittable`] - A type representing optional grammar elements.
//!
//! In general, types are laid out as follows:
//! ```ignore
//! pub struct _LangFeature_ {
//!     /// The specific type of this node.
//!     pub ty: _LangFeature_Ty,
//!     /// A span of the entire node.
//!     pub span: Span
//! }
//!
//! pub enum _LangFeature_Ty {
//!     /* Actual variants are here */
//!     /* Each variant contains any necessary fields that are relevant to it */
//! }
//! ```

use crate::{
	diag::Syntax,
	lexer::{NumType, Token},
	Either, Span, Spanned,
};

/// This type represents a value which can be omitted in accordance to the GLSL specification.
///
/// This type is equivalent to [`Option`]. The reason for the two types is to differentiate when a node's field is
/// empty because it can legally be omitted, and when a node's field is empty because the parser used an error
/// recovery strategy due to a syntax error.
///
/// This type implements the [`From`] trait for conversions between [`Option`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Omittable<T> {
	/// Some value of type `T`.
	Some(T),
	/// No value.
	None,
}

/// An identifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
	pub name: String,
	pub span: Span,
}

/// A node within the abstract syntax tree.
#[derive(Debug, Clone, PartialEq)]
pub struct Node {
	pub ty: NodeTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum NodeTy {
	/// An empty statement, e.g. `;`.
	Empty,
	/// An expression statement, e.g. `5 + 1;` or `i++;`.
	Expr(Expr),
	/// A block scope, e.g. `{ int i; }`.
	Block(Scope),
	/// A variable definition, e.g. `int i;`.
	VarDef { type_: Type, ident: Ident },
	/// A variable definition containing multiple variables, e.g. `int i, j, k;`.
	VarDefs(Vec<(Type, Ident)>),
	/// A variable definition with initialization, e.g. `int i = 0;`.
	VarDefInit {
		type_: Type,
		ident: Ident,
		value: Option<Expr>,
	},
	/// A variable definition with initialization, containing multiple variables, e.g. `int i, j, k = 0;`.
	VarDefInits(Vec<(Type, Ident)>, Option<Expr>),
	/// A function declaration, e.g. `int foo(int i);`.
	FnDecl {
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
	},
	/// A function definition, e.g. `int foo(int i) { return i + 1; }`.
	FnDef {
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
		body: Scope,
	},
	/// A subroutine type declaration, e.g. `subroutine int foo(int i);`.
	SubroutineTypeDecl {
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
	},
	/// A subroutine associated function definition, e.g. `subroutine(foo) int foo_1(int i) {/*...*/}`.
	SubroutineFnDef {
		associations: Vec<Ident>,
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
		body: Option<Scope>,
	},
	/// A subroutine uniform definition, e.g. `subroutine uniform foo my_foo;`.
	SubroutineUniformDef { type_: Type, ident: Ident },
	/// A struct declaration, e.g. `struct FooBar;`. This is an illegal GLSL statement.
	StructDecl {
		qualifiers: Vec<Qualifier>,
		ident: Ident,
	},
	/// A struct definition, e.g. `struct FooBar { mat4 m; };`.
	StructDef {
		qualifiers: Vec<Qualifier>,
		ident: Ident,
		body: Scope,
		instance: Omittable<Ident>,
	},
	/// An if statement, e.g. `if (true) {/*...*/} else {/*...*/}`.
	If(Vec<IfBranch>),
	/// A switch statement, e.g. `switch (true) { default: return; }`.
	Switch {
		cond: Option<Expr>,
		cases: Vec<SwitchCase>,
	},
	/// A for loop, e.g. `for (int i = 0; i<5; i++) {/*...*/}`.
	For {
		init: Option<Box<Node>>,
		cond: Option<Box<Node>>,
		inc: Option<Box<Node>>,
		body: Option<Scope>,
	},
	/// A while loop, e.g `while (true) {/*...*/}`.
	While { cond: Option<Expr>, body: Scope },
	/// A do-while loop, e.g. `do {/*...*/} while (true);`.
	DoWhile { body: Scope, cond: Option<Expr> },
	/// A break statement, e.g. `break;`.
	Break,
	/// A continue statement, e.g. `continue;`.
	Continue,
	/// A discard statement, e.g. `discard;`.
	Discard,
	/// A return statement, e.g. `return 5;`.
	Return { value: Omittable<Expr> },
	/// An empty directive, i.e. just a `#` on it's own line.
	EmptyDirective,
	/// A version directive, e.g. `#version 450 core`.
	VersionDirective {
		version: Option<Spanned<usize>>,
		profile: Omittable<Spanned<ProfileTy>>,
	},
	/// An extension directive, e.g. `#extension all : enable`.
	ExtensionDirective {
		name: Option<Spanned<String>>,
		behaviour: Option<Spanned<BehaviourTy>>,
	},
	/// A line directive, e.g. `#line 1`.
	LineDirective {
		line: Option<Spanned<usize>>,
		src_str_num: Omittable<Spanned<usize>>,
	},
	/// A define directive, e.g. `#define TOGGLE 1`.
	DefineDirective {
		macro_: Macro,
		replacement_tokens: Vec<Spanned<Token>>,
	},
	/// An undef directive, e.g. `#undef TOGGLE`.
	UndefDirective {
		/// The name of the macro to un-define.
		name: Omittable<Ident>,
	},
	/// An error directive, e.g. `#error foo bar`.
	ErrorDirective { message: Omittable<Spanned<String>> },
	/// A pragma directive, e.g. `#pragma strict`.
	PragmaDirective { options: Omittable<Spanned<String>> },
}

/// A scope of nodes.
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
	pub contents: Vec<Node>,
	pub span: Span,
}

/// A parameter in a function definition/declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
	pub type_: Type,
	pub ident: Omittable<Ident>,
	pub span: Span,
}

/// An if-statement branch.
#[derive(Debug, Clone, PartialEq)]
pub struct IfBranch {
	pub condition: Spanned<IfCondition>,
	pub body: Option<Scope>,
	pub span: Span,
}

/// The condition of an if-statement branch.
#[derive(Debug, Clone, PartialEq)]
pub enum IfCondition {
	If(Option<Expr>),
	ElseIf(Option<Expr>),
	Else,
}

/// A switch case.
#[derive(Debug, Clone, PartialEq)]
pub struct SwitchCase {
	pub expr: Either<Option<Expr>, ()>,
	pub body: Option<Scope>,
	pub span: Span,
}

/// A type.
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
	pub ty: TypeTy,
	pub qualifiers: Vec<Qualifier>,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeTy {
	/// A type which has only a single value.
	Single(Primitive),
	/// An array type which contains zero or more values.
	Array(Primitive, ArrSize),
	/// A 2D array type which contains zero or more values.
	///
	/// - `1` - Size of the outer array.
	/// - `2` - Size of each inner array.
	Array2D(Primitive, ArrSize, ArrSize),
	/// An n-dimensional array type which contains zero or more values.
	///
	/// - `1` - Vec containing the sizes of arrays, starting with the outer-most array.
	ArrayND(Primitive, Vec<ArrSize>),
}

/// An array size.
pub type ArrSize = Omittable<Expr>;

/// A primitive language type.
///
/// The reason for the separation of this enum and the [`Fundamental`] enum is that all fundamental types (aside
/// from `void`) can be either a scalar or an n-dimensional vector. Furthermore, any of the types in this enum can
/// be on their own or as part of a n-dimensional array.
#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
	/// A scalar primitive type.
	Scalar(Fundamental),
	/// A n-dimensional primitive type, where `2 <= n <= 4`.
	Vector(Fundamental, usize),
	/// A float matrix type.
	///
	/// - `0` - Column count.
	/// - `1` - Row count.
	Matrix(usize, usize),
	/// A double matrix type.
	///
	/// - `0` - Column count.
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
	/// - The data type is guaranteed to be one of `Fundamental::Float|Int|UInt`.
	Sampler(Fundamental, TexType),
	/// An image type.
	///
	/// - `0` - Data type.
	/// - `1` - Texture type.
	///
	/// # Invariants
	/// - The data type is guaranteed to be one of `Fundamental::Float|Int|UInt`.
	/// - The texture type is guaranteed to be none of the `TexType::Shadow*` variants.
	Image(Fundamental, TexType),
	/// An atomic counter type.
	Atomic,
}

/// A fundamental type.
///
/// These are the most fundamental types in the language, on which all other types are composed.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Fundamental {
	Void,
	Bool,
	Int,
	UInt,
	Float,
	Double,
}

/// The texture type of a `sampler_`/`isampler_`/`usampler_` or `image_`/`iimage_` primitive type.
///
/// The names of the variants match the type name suffixes, but any 1D/2D/3D letters are flipped because Rust
/// typenames cannot begin with a digit.
#[derive(Debug, Clone, PartialEq)]
pub enum TexType {
	/// `_1D`
	D1,
	/// `_2D`
	D2,
	/// `_3D`
	D3,
	/// `_Cube`
	Cube,
	/// `_2DRect`
	D2Rect,
	/// `_1DArray`
	D1Array,
	/// `_2DArray`
	D2Array,
	/// `_CubeArray`
	CubeArray,
	/// `_Buffer`
	Buffer,
	/// `_2DMS`
	D2Multisample,
	/// `_2DMSArray`
	D2MultisampleArray,
	/// `_1DShadow`
	D1Shadow,
	/// `_2DShadow`
	D2Shadow,
	/// `_3DShadow`
	D3Shadow,
	/// `_CubeShadow`
	CubeShadow,
	/// `_2DRectShadow`
	D2RectShadow,
	/// `_1DArrayShadow`
	D1ArrayShadow,
	/// `_2DArrayShadow`
	D2ArrayShadow,
	/// `_CubeArrayShadow`
	CubeArrayShadow,
}

/// A type qualifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Qualifier {
	pub ty: QualifierTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum QualifierTy {
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
	Layout(Vec<Layout>),
	Flat,
	Smooth,
	NoPerspective,
	HighP,
	MediumP,
	LowP,
	Invariant,
	Precise,
	Coherent,
	Volatile,
	Restrict,
	Readonly,
	Writeonly,
}

/// An individual layout property within a layout qualifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Layout {
	pub ty: LayoutTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LayoutTy {
	Shared,
	Packed,
	Std140,
	Std430,
	RowMajor,
	ColumnMajor,
	Binding(Option<Expr>),
	Offset(Option<Expr>),
	Align(Option<Expr>),
	Location(Option<Expr>),
	Component(Option<Expr>),
	Index(Option<Expr>),
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
	LineAdjacency,
	TriangleAdjacency,
	Invocations(Option<Expr>),
	OriginUpperLeft,
	PixelCenterInteger,
	EarlyFragmentTests,
	LocalSizeX(Option<Expr>),
	LocalSizeY(Option<Expr>),
	LocalSizeZ(Option<Expr>),
	XfbBuffer(Option<Expr>),
	XfbStride(Option<Expr>),
	XfbOffset(Option<Expr>),
	Vertices(Option<Expr>),
	LineStrip,
	TriangleStrip,
	MaxVertices(Option<Expr>),
	Stream(Option<Expr>),
	DepthAny,
	DepthGreater,
	DepthLess,
	DepthUnchanged,
}

/// A GLSL profile.
#[derive(Debug, Clone, PartialEq)]
pub enum ProfileTy {
	Core,
	Compatability,
	Es,
}

/// The behaviour of a GLSL extension.
#[derive(Debug, Clone, PartialEq)]
pub enum BehaviourTy {
	Require,
	Enable,
	Warn,
	Disable,
}

/// A macro definition.
#[derive(Debug, Clone, PartialEq)]
pub enum Macro {
	/// An object-like macro.
	Object { ident: Ident },
	/// A function-like macro.
	Function { ident: Ident, params: Vec<Ident> },
}

impl<T> Omittable<T> {
	/// Returns `true` if the omittable is a [`Some`](Omittable::Some) value.
	///
	/// # Examples
	/// ```
	/// # use glast::parser::ast::Omittable::{self, Some, None};
	/// let x: Omittable<u32> = Some(2);
	/// assert_eq!(x.is_some(), true);
	///
	/// let x: Omittable<u32> = None;
	/// assert_eq!(x.is_some(), false);
	/// ```
	#[inline]
	pub const fn is_some(&self) -> bool {
		matches!(*self, Self::Some(_))
	}

	/// Returns `true` if the omittable is a [`None`](Omittable::None) value.
	///
	/// # Examples
	/// ```
	/// # use glast::parser::ast::Omittable::{self, Some, None};
	/// let x: Omittable<u32> = Some(2);
	/// assert_eq!(x.is_none(), false);
	///
	/// let x: Omittable<u32> = None;
	/// assert_eq!(x.is_none(), true);
	/// ```
	#[inline]
	pub const fn is_none(&self) -> bool {
		!self.is_some()
	}
}

impl<T> From<Option<T>> for Omittable<T> {
	fn from(opt: Option<T>) -> Self {
		match opt {
			Some(val) => Omittable::Some(val),
			None => Omittable::None,
		}
	}
}

impl Type {
	/// Tries to parse an expression into a type.
	pub fn parse(expr: &Expr) -> Option<Self> {
		match &expr.ty {
			ExprTy::Ident(i) => Some(Self {
				span: expr.span,
				ty: TypeTy::Single(Primitive::parse(i)),
				qualifiers: vec![],
			}),
			ExprTy::Index { item, i } => {
				let mut current_item = item;
				let mut stack = Vec::new();
				stack.push(i.as_deref().cloned().into());

				// Recursively look into any nested index operators until we hit an identifier.
				let primitive = loop {
					match &current_item.ty {
						ExprTy::Ident(i) => break Primitive::parse(i),
						ExprTy::Index { item, i } => {
							stack.push(i.as_deref().cloned().into());
							current_item = item;
						}
						_ => {
							// TODO: Is this possible to reach?
							return None;
						}
					}
				};

				// In the expression parser, the index operator is right-associated so the outer-most is at the top
				// and the inner-most is at the bottom. We want to reverse this so that the type array notation is
				// in line with our intuition.
				stack.reverse();

				Some(Self {
					span: expr.span,
					ty: if stack.len() == 1 {
						TypeTy::Array(primitive, stack.remove(0))
					} else if stack.len() == 2 {
						let one = stack.remove(0);
						let two = stack.remove(0);
						TypeTy::Array2D(primitive, one, two)
					} else {
						TypeTy::ArrayND(primitive, stack)
					},
					qualifiers: vec![],
				})
			}
			_ => None,
		}
	}

	/// Tries to parse an expression into information required for variable definitions/declarations.
	///
	/// If successful, this function returns `Some` where each entry in the vector is:
	/// - `0` - The variable identifier,
	/// - `1` - Any array size specifiers for that variable.
	///
	/// If the expression cannot be parsed, this function returns `None`.
	pub(crate) fn parse_var_idents(
		expr: &Expr,
	) -> Option<Vec<(Ident, Vec<ArrSize>)>> {
		fn convert(expr: &Expr) -> Option<(Ident, Vec<ArrSize>)> {
			match &expr.ty {
				ExprTy::Ident(i) => Some((i.clone(), vec![])),
				ExprTy::Index { item, i } => {
					let mut current_item = item;
					let mut stack = Vec::new();
					stack.push(i.as_deref().cloned().into());

					// Recursively look into any nested index operators until we hit an identifier.
					let ident = loop {
						match &current_item.ty {
							ExprTy::Ident(i) => break i.clone(),
							ExprTy::Index { item, i } => {
								stack.push(i.as_deref().cloned().into());
								current_item = item;
							}
							_ => {
								// TODO: Is this possible to reach?
								return None;
							}
						}
					};

					// In the expression parser, the index operator is right-associated so the outer-most is at the top
					// and the inner-most is at the bottom. We want to reverse this so that the type array notation is
					// in line with our intuition.
					stack.reverse();
					Some((ident, stack))
				}
				_ => unreachable!(),
			}
		}

		match &expr.ty {
			ExprTy::Ident(_) | ExprTy::Index { .. } => {
				convert(expr).map(|i| vec![i])
			}
			ExprTy::List { items } => {
				let mut v = Vec::new();
				for item in items {
					v.push(match convert(item) {
						Some(i) => i,
						None => return None,
					})
				}
				Some(v)
			}
			_ => None,
		}
	}
}

impl Primitive {
	/// Parses an identifier into a primitive type.
	pub fn parse(ident: &Ident) -> Self {
		match ident.name.as_ref() {
			"void" => Primitive::Scalar(Fundamental::Void),
			"bool" => Primitive::Scalar(Fundamental::Bool),
			"int" => Primitive::Scalar(Fundamental::Int),
			"uint" => Primitive::Scalar(Fundamental::UInt),
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
			"uvec2" => Primitive::Vector(Fundamental::UInt, 2),
			"uvec3" => Primitive::Vector(Fundamental::UInt, 3),
			"uvec4" => Primitive::Vector(Fundamental::UInt, 4),
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
			"samplerCube" => {
				Primitive::Sampler(Fundamental::Float, TexType::Cube)
			}
			"sampler2DRect" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2Rect)
			}
			"sampler1DArray" => {
				Primitive::Sampler(Fundamental::Float, TexType::D1Array)
			}
			"sampler2DArray" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2Array)
			}
			"samplerCubeArray" => {
				Primitive::Sampler(Fundamental::Float, TexType::CubeArray)
			}
			"samplerBuffer" => {
				Primitive::Sampler(Fundamental::Float, TexType::Buffer)
			}
			"sampler2DMS" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2Multisample)
			}
			"sampler2DMSArray" => Primitive::Sampler(
				Fundamental::Float,
				TexType::D2MultisampleArray,
			),
			"isampler1D" => Primitive::Sampler(Fundamental::Int, TexType::D1),
			"isampler2D" => Primitive::Sampler(Fundamental::Int, TexType::D2),
			"isampler3D" => Primitive::Sampler(Fundamental::Int, TexType::D3),
			"isamplerCube" => {
				Primitive::Sampler(Fundamental::Int, TexType::Cube)
			}
			"isampler2DRect" => {
				Primitive::Sampler(Fundamental::Int, TexType::D2Rect)
			}
			"isampler1DArray" => {
				Primitive::Sampler(Fundamental::Int, TexType::D1Array)
			}
			"isampler2DArray" => {
				Primitive::Sampler(Fundamental::Int, TexType::D2Array)
			}
			"isamplerCubeArray" => {
				Primitive::Sampler(Fundamental::Int, TexType::CubeArray)
			}
			"isamplerBuffer" => {
				Primitive::Sampler(Fundamental::Int, TexType::Buffer)
			}
			"isampler2DMS" => {
				Primitive::Sampler(Fundamental::Int, TexType::D2Multisample)
			}
			"isampler2DMSArray" => Primitive::Sampler(
				Fundamental::Int,
				TexType::D2MultisampleArray,
			),
			"usampler1D" => Primitive::Sampler(Fundamental::UInt, TexType::D1),
			"usampler2D" => Primitive::Sampler(Fundamental::UInt, TexType::D2),
			"usampler3D" => Primitive::Sampler(Fundamental::UInt, TexType::D3),
			"usamplerCube" => {
				Primitive::Sampler(Fundamental::UInt, TexType::Cube)
			}
			"usampler2DRect" => {
				Primitive::Sampler(Fundamental::UInt, TexType::D2Rect)
			}
			"usampler1DArray" => {
				Primitive::Sampler(Fundamental::UInt, TexType::D1Array)
			}
			"usampler2DArray" => {
				Primitive::Sampler(Fundamental::UInt, TexType::D2Array)
			}
			"usamplerCubeArray" => {
				Primitive::Sampler(Fundamental::UInt, TexType::CubeArray)
			}
			"usamplerBuffer" => {
				Primitive::Sampler(Fundamental::UInt, TexType::Buffer)
			}
			"usampler2DMS" => {
				Primitive::Sampler(Fundamental::UInt, TexType::D2Multisample)
			}
			"usampler2DMSArray" => Primitive::Sampler(
				Fundamental::UInt,
				TexType::D2MultisampleArray,
			),
			"sampler1DShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::D1Shadow)
			}
			"sampler2DShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2Shadow)
			}
			"samplerCubeShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::CubeShadow)
			}
			"sampler2DRectShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2RectShadow)
			}
			"sampler1DArrayShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::D1ArrayShadow)
			}
			"sampler2DArrayShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::D2ArrayShadow)
			}
			"samplerCubeArrayShadow" => {
				Primitive::Sampler(Fundamental::Float, TexType::CubeArrayShadow)
			}
			"image1D" => Primitive::Image(Fundamental::Float, TexType::D1),
			"image2D" => Primitive::Image(Fundamental::Float, TexType::D2),
			"image3D" => Primitive::Image(Fundamental::Float, TexType::D3),
			"imageCube" => Primitive::Image(Fundamental::Float, TexType::Cube),
			"image2DRect" => {
				Primitive::Image(Fundamental::Float, TexType::D2Rect)
			}
			"image1DArray" => {
				Primitive::Image(Fundamental::Float, TexType::D1Array)
			}
			"image2DArray" => {
				Primitive::Image(Fundamental::Float, TexType::D2Array)
			}
			"imageCubeArray" => {
				Primitive::Image(Fundamental::Float, TexType::CubeArray)
			}
			"imageBuffer" => {
				Primitive::Image(Fundamental::Float, TexType::Buffer)
			}
			"image2DMS" => {
				Primitive::Image(Fundamental::Float, TexType::D2Multisample)
			}
			"image2DMSArray" => Primitive::Image(
				Fundamental::Float,
				TexType::D2MultisampleArray,
			),
			"iimage1D" => Primitive::Image(Fundamental::Int, TexType::D1),
			"iimage2D" => Primitive::Image(Fundamental::Int, TexType::D2),
			"iimage3D" => Primitive::Image(Fundamental::Int, TexType::D3),
			"iimageCube" => Primitive::Image(Fundamental::Int, TexType::Cube),
			"iimage2DRect" => {
				Primitive::Image(Fundamental::Int, TexType::D2Rect)
			}
			"iimage1DArray" => {
				Primitive::Image(Fundamental::Int, TexType::D1Array)
			}
			"iimage2DArray" => {
				Primitive::Image(Fundamental::Int, TexType::D2Array)
			}
			"iimageCubeArray" => {
				Primitive::Image(Fundamental::Int, TexType::CubeArray)
			}
			"iimageBuffer" => {
				Primitive::Image(Fundamental::Int, TexType::Buffer)
			}
			"iimage2DMS" => {
				Primitive::Image(Fundamental::Int, TexType::D2Multisample)
			}
			"iimage2DMSArray" => {
				Primitive::Image(Fundamental::Int, TexType::D2MultisampleArray)
			}
			"uimage1D" => Primitive::Image(Fundamental::UInt, TexType::D1),
			"uimage2D" => Primitive::Image(Fundamental::UInt, TexType::D2),
			"uimage3D" => Primitive::Image(Fundamental::UInt, TexType::D3),
			"uimageCube" => Primitive::Image(Fundamental::UInt, TexType::Cube),
			"uimage2DRect" => {
				Primitive::Image(Fundamental::UInt, TexType::D2Rect)
			}
			"uimage1DArray" => {
				Primitive::Image(Fundamental::UInt, TexType::D1Array)
			}
			"uimage2DArray" => {
				Primitive::Image(Fundamental::UInt, TexType::D2Array)
			}
			"uimageCubeArray" => {
				Primitive::Image(Fundamental::UInt, TexType::CubeArray)
			}
			"uimageBuffer" => {
				Primitive::Image(Fundamental::UInt, TexType::Buffer)
			}
			"uimage2DMS" => {
				Primitive::Image(Fundamental::UInt, TexType::D2Multisample)
			}
			"uimage2DMSArray" => {
				Primitive::Image(Fundamental::UInt, TexType::D2MultisampleArray)
			}
			"atomic_uint" => Primitive::Atomic,
			_ => Primitive::Struct(ident.clone()),
		}
	}
}

/* EXPRESSION-RELATED STUFF BELOW */

/// An expression node.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
	pub ty: ExprTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprTy {
	/// A literal constant.
	Lit(Lit),
	/// An identifier.
	Ident(Ident),
	/// A prefix operator.
	Prefix { op: PreOp, expr: Option<Box<Expr>> },
	/// A postfix operator.
	Postfix { expr: Box<Expr>, op: PostOp },
	/// A binary expression.
	Binary {
		left: Box<Expr>,
		op: BinOp,
		right: Option<Box<Expr>>,
	},
	/// A ternary expression.
	Ternary {
		cond: Box<Expr>,
		true_: Option<Box<Expr>>,
		false_: Option<Box<Expr>>,
	},
	/// A set of parenthesis.
	Parens { expr: Option<Box<Expr>> },
	/// Object access.
	ObjAccess {
		obj: Box<Expr>,
		leaf: Option<Box<Expr>>,
	},
	/// An index operator.
	Index {
		item: Box<Expr>,
		i: Option<Box<Expr>>,
	},
	/// A function call.
	FnCall { ident: Ident, args: Vec<Expr> },
	/// An initializer list.
	InitList { args: Vec<Expr> },
	/// An array constructor.
	ArrConstructor {
		/// Contains the first part of an array constructor, e.g. `int[3]`.
		arr: Box<Expr>,
		args: Vec<Expr>,
	},
	/// A general list expression, e.g. `a, b`.
	List { items: Vec<Expr> },
	/// A separator.
	///
	/// This node only exists during the execution of the expression parser. It will not occur in the final AST.
	Separator,
}

/// A binary operator.
#[derive(Debug, Clone, PartialEq)]
pub struct BinOp {
	pub ty: BinOpTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinOpTy {
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	And,
	Or,
	Xor,
	LShift,
	RShift,
	Eq,
	AddEq,
	SubEq,
	MulEq,
	DivEq,
	RemEq,
	AndEq,
	OrEq,
	XorEq,
	LShiftEq,
	RShiftEq,
	EqEq,
	NotEq,
	AndAnd,
	OrOr,
	XorXor,
	Gt,
	Lt,
	Ge,
	Le,
}

/// A prefix operator.
#[derive(Debug, Clone, PartialEq)]
pub struct PreOp {
	pub ty: PreOpTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PreOpTy {
	Add,
	Sub,
	Neg,
	Flip,
	Not,
}

/// A postfix operator.
#[derive(Debug, Clone, PartialEq)]
pub struct PostOp {
	pub ty: PostOpTy,
	pub span: Span,
}
#[derive(Debug, Clone, PartialEq)]
pub enum PostOpTy {
	Add,
	Sub,
}

/// A literal constant.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Lit {
	Bool(bool),
	Int(i64),
	UInt(u64),
	Float(f32),
	Double(f64),
	/// A [`Token::Num`] which could not be parsed into a valid number.
	///
	/// This could be because:
	/// - The number is too large to be represented by the relevant GLSL type, e.g.
	///   `10000000000000000000000000000000000000`.
	/// - The number has an illegal suffix, e.g. `150abc`.
	/// - The number has no digits, e.g. `0xU`.
	InvalidNum,
}

impl Lit {
	/// Tries to parse a [`Token::Num`] or [`Token::Bool`] into a literal constant.
	///
	/// This function returns an `Err` if the token could not be parsed into a valid number. The return value
	/// contains an [`InvalidNum`](Lit::InvalidNum) literal and a relevant syntax error.
	///
	/// # Panics
	/// This function assumes the token is a `Num` or `Bool` variant.
	pub fn parse(token: &Token, span: Span) -> Result<Self, (Self, Syntax)> {
		use crate::diag::ExprDiag;

		match token {
			Token::Bool(b) => Ok(Self::Bool(*b)),
			Token::Num {
				num: s,
				suffix,
				type_,
			} => {
				let s: &str = &s;
				let suffix = suffix.as_deref();
				let type_ = *type_;
				// The contents could be empty, e.g. `0xu` is a `NumType::Hex` with contents `` with suffix `u`.
				if s == "" {
					return Err((
						Self::InvalidNum,
						Syntax::Expr(ExprDiag::EmptyNumber(span)),
					));
				}
				match type_ {
					NumType::Dec => Self::parse_num_dec(s, suffix, span),
					NumType::Hex => Self::parse_num_hex(s, suffix, span),
					NumType::Oct => Self::parse_num_oct(s, suffix, span),
					NumType::Float => Self::parse_num_float(s, suffix, span),
				}
			}
			_ => unreachable!(
				"This function should only be given a `Num` or `Bool` token."
			),
		}
	}

	fn parse_num_dec(
		s: &str,
		suffix: Option<&str>,
		span: Span,
	) -> Result<Self, (Self, Syntax)> {
		use crate::diag::ExprDiag;

		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 10) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err((
					Self::InvalidNum,
					Syntax::Expr(ExprDiag::InvalidNumber(span)),
				));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 10) {
				return Ok(Self::Int(i));
			}
		}

		Err((
			Self::InvalidNum,
			Syntax::Expr(ExprDiag::UnparsableNumber(span)),
		))
	}

	fn parse_num_hex(
		s: &str,
		suffix: Option<&str>,
		span: Span,
	) -> Result<Self, (Self, Syntax)> {
		use crate::diag::ExprDiag;

		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 16) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err((
					Self::InvalidNum,
					Syntax::Expr(ExprDiag::InvalidNumber(span)),
				));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 16) {
				return Ok(Self::Int(i));
			}
		}

		Err((
			Self::InvalidNum,
			Syntax::Expr(ExprDiag::UnparsableNumber(span)),
		))
	}

	fn parse_num_oct(
		s: &str,
		suffix: Option<&str>,
		span: Span,
	) -> Result<Self, (Self, Syntax)> {
		use crate::diag::ExprDiag;

		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 8) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err((
					Self::InvalidNum,
					Syntax::Expr(ExprDiag::InvalidNumber(span)),
				));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 8) {
				return Ok(Self::Int(i));
			}
		}

		Err((
			Self::InvalidNum,
			Syntax::Expr(ExprDiag::UnparsableNumber(span)),
		))
	}

	fn parse_num_float(
		s: &str,
		suffix: Option<&str>,
		span: Span,
	) -> Result<Self, (Self, Syntax)> {
		use crate::diag::ExprDiag;

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
				return Err((
					Self::InvalidNum,
					Syntax::Expr(ExprDiag::InvalidNumber(span)),
				));
			}
		} else {
			if let Ok(f) = s.parse::<f32>() {
				return Ok(Self::Float(f));
			}
		}

		Err((
			Self::InvalidNum,
			Syntax::Expr(ExprDiag::UnparsableNumber(span)),
		))
	}
}

/* CONDITIONAL COMPILATION STUFF BELOW */

/// A conditional directive.
#[derive(Debug, Clone, PartialEq)]
pub struct Conditional {
	pub ty: ConditionalTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConditionalTy {
	/// An `#ifdef` directive.
	IfDef { ident: Option<Ident> },
	/// An `#ifndef` directive.
	IfNotDef { ident: Option<Ident> },
	/// An `#if` directive.
	If { expr: Option<conditional::Expr> },
	/// An `#elif` directive.
	ElseIf { expr: Option<conditional::Expr> },
	/// An `#else` directive.
	Else,
	/// An `#endif` directive.
	End,
}

/// AST items for conditional directive expressions.
pub mod conditional {
	use super::Ident;
	use crate::Span;

	/// An expression node.
	#[derive(Debug, Clone, PartialEq)]
	pub struct Expr {
		pub ty: ExprTy,
		pub span: Span,
	}

	#[derive(Debug, Clone, PartialEq)]
	pub enum ExprTy {
		/// An integer literal.
		Num(usize),
		/// A prefix operator.
		Prefix { op: PreOp, expr: Option<Box<Expr>> },
		/// A binary expression.
		Binary {
			left: Box<Expr>,
			op: BinOp,
			right: Option<Box<Expr>>,
		},
		/// A set of parenthesis.
		Parens { expr: Option<Box<Expr>> },
		/// The `defined` operator.
		Defined { ident: Ident },
	}

	/// A binary operator.
	#[derive(Debug, Clone, PartialEq)]
	pub struct BinOp {
		pub ty: BinOpTy,
		pub span: Span,
	}

	#[derive(Debug, Clone, PartialEq)]
	pub enum BinOpTy {
		Add,
		Sub,
		Mul,
		Div,
		Rem,
		And,
		Or,
		Xor,
		LShift,
		RShift,
		EqEq,
		NotEq,
		AndAnd,
		OrOr,
		Gt,
		Lt,
		Ge,
		Le,
	}

	/// A prefix operator.
	#[derive(Debug, Clone, PartialEq)]
	pub struct PreOp {
		pub ty: PreOpTy,
		pub span: Span,
	}

	#[derive(Debug, Clone, PartialEq)]
	pub enum PreOpTy {
		Neg,
		Flip,
		Not,
	}
}
