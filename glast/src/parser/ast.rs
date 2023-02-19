//! Abstract syntax tree types and functionality.
//!
//! There are a lot of types used to represent specific things. Some common ones worth mentioning:
//! - [`Node`] and [`NodeTy`] - A node representing a statement.
//! - [`Expr`] and [`ExprTy`] - A node representing an expression; this will never be found standalone but part of
//!   a `Node` of some kind.
//! - [`Ident`] - A general identifier of some kind.
//! - [`Type`] and [`TypeTy`] - Type information.
//! - [`Omittable`] - An enum representing optional grammar elements. Note that this differs from an `Option` in
//!   semantic meaning; see docs for details.
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
//!
//! Since conditional compilation is resolved before the AST is generated, conditional compilation directives are
//! not part of the AST.

use super::{NodeHandle, StructHandle, VariableTableHandle};
use crate::{
	diag::Syntax,
	lexer::{NumType, Token},
	Either, Either3, NonEmpty, Span, Spanned,
};

/// This type represents a value which can be omitted in accordance to the GLSL specification.
///
/// This type is equivalent to [`Option`]. The reason for the two types is to differentiate when a node's field is
/// empty because it can legally be omitted (this type), and when a node's field is empty because the parser used
/// an error recovery strategy due to a syntax error (`Option`).
///
/// This type implements the [`From`] trait for conversions to/from [`Option`], as well as a handful of helper
/// methods which match the equivalent `Option` signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Omittable<T> {
	/// Some value of type `T`.
	Some(T),
	/// No value.
	None,
}

/// An identifier.
#[derive(Debug, Clone, PartialEq, Eq)]
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
	/// A translation unit, i.e. the entire abstract syntax tree.
	TranslationUnit(Scope),
	/// An empty statement, i.e. just `;`.
	Empty,
	/// An expression statement, e.g. `5 + 1;` or `i++;`.
	Expr(Expr),
	/// A block scope, e.g. `{ int i; }`.
	Block(Scope),
	/// A standalone type specifier, e.g. `float;`.
	TypeSpecifier(Type),
	/// One or more standalone qualifiers, e.g. `layout(points) in;`.
	Qualifiers(NonEmpty<Qualifier>),
	/// A variable definition, e.g. `int i;` or `float f = 5.0;`.
	VarDef {
		type_: Type,
		ident: Ident,
		eq_span: Omittable<Span>,
		init_expr: Omittable<Expr>,
	},
	/// A variable definition containing multiple variables, e.g. `int i, j = 1, k;`.
	VarDefs(Vec<(Type, Ident, Omittable<Span>, Omittable<Expr>)>),
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
	SubroutineFnDefAssociation {
		associations: Vec<(super::SubroutineHandle, Ident)>,
		return_type: Type,
		ident: Ident,
		params: Vec<Param>,
		body: Scope,
	},
	/// A subroutine uniform definition, e.g. `subroutine uniform foo my_foo;`.
	SubroutineUniformDef { type_: SubroutineType, ident: Ident },
	/// A subroutine uniform definition containing multiple variables, e.g. `subroutine uniform foo f1, f2;`.
	SubroutineUniformDefs(Vec<(SubroutineType, Ident)>),
	/// A struct declaration, e.g. `struct FooBar;`. This is an illegal GLSL statement, however it is modelled here
	/// for completeness sake.
	StructDecl {
		qualifiers: Omittable<NonEmpty<Qualifier>>,
		name: Ident,
	},
	/// A struct definition, e.g. `struct FooBar { mat4 m; };`.
	StructDef {
		qualifiers: Omittable<NonEmpty<Qualifier>>,
		name: Ident,
		fields: Vec<(Type, Omittable<Ident>)>,
		instances: Vec<(Ident, Omittable<Spanned<Vec<ArrSize>>>)>,
	},
	/// An interface block definition, e.g. `out V { vec2 pos; } v_out;`.
	InterfaceDef {
		qualifiers: Option<NonEmpty<Qualifier>>,
		name: Ident,
		fields: Vec<(Type, Omittable<Ident>)>,
		instances: Vec<(Ident, Omittable<Spanned<Vec<ArrSize>>>)>,
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
		init: Option<NodeHandle>,
		cond: Option<NodeHandle>,
		inc: Option<NodeHandle>,
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
	pub contents: Vec<NodeHandle>,
	pub variable_table: VariableTableHandle,
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

/// A subroutine type.
#[derive(Debug, Clone, PartialEq)]
pub struct SubroutineType {
	pub ty: SubroutineTypeTy,
	pub qualifiers: Omittable<NonEmpty<Qualifier>>,
	/// The span of the typname itself. E.g. span of `foo` in `subroutine uniform foo my_foo;`
	pub ident_span: Span,
	/// The span of the type specifier itself. E.g. span of `int[1]` in `const int[1] foo[3]`.
	pub ty_specifier_span: Span,
	/// The span of a disjointed type specifier if one is present. E.g. the span of `[3][2]` in `const int
	/// foo[3][2]`.
	pub disjointed_span: Omittable<Span>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SubroutineTypeTy {
	/// A type which has only a single value.
	Single(super::SubroutineHandle),
	/// An array type which contains zero or more values.
	Array(super::SubroutineHandle, ArrSize),
	/// A 2D array type which contains zero or more values.
	///
	/// - `1` - Size of the outer array.
	/// - `2` - Size of each inner array.
	Array2D(super::SubroutineHandle, ArrSize, ArrSize),
	/// An n-dimensional array type which contains zero or more values.
	///
	/// - `1` - Vec containing the sizes of arrays, starting with the outer-most array.
	ArrayND(super::SubroutineHandle, Vec<ArrSize>),
}

/// A type.
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
	pub ty: TypeTy,
	pub qualifiers: Omittable<NonEmpty<Qualifier>>,
	/// The span of the type specifier itself. E.g. span of `int` in `const int foo[3]`.
	pub ty_specifier_span: Span,
	/// The span of a disjointed type specifier if one is present. E.g. the span of `[3][2]` in `const int
	/// foo[3][2]`.
	pub disjointed_span: Omittable<Span>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeTy {
	/// A type which has only a single value.
	Single(Either<Primitive, StructHandle>),
	/// An array type which contains zero or more values.
	Array(Either<Primitive, StructHandle>, ArrSize),
	/// A 2D array type which contains zero or more values.
	///
	/// - `1` - Size of the outer array.
	/// - `2` - Size of each inner array.
	Array2D(Either<Primitive, StructHandle>, ArrSize, ArrSize),
	/// An n-dimensional array type which contains zero or more values.
	///
	/// - `1` - Vec containing the sizes of arrays, starting with the outer-most array.
	ArrayND(Either<Primitive, StructHandle>, Vec<ArrSize>),
}

/// An array size.
pub type ArrSize = Omittable<Expr>;

/// A primitive language type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Primitive {
	Void,
	Bool,
	Int,
	Uint,
	Float,
	Double,
	Vec2,
	Vec3,
	Vec4,
	BVec2,
	BVec3,
	BVec4,
	IVec2,
	IVec3,
	IVec4,
	UVec2,
	UVec3,
	UVec4,
	DVec2,
	DVec3,
	DVec4,
	Mat2x2,
	Mat2x3,
	Mat2x4,
	Mat3x2,
	Mat3x3,
	Mat3x4,
	Mat4x2,
	Mat4x3,
	Mat4x4,
	DMat2x2,
	DMat2x3,
	DMat2x4,
	DMat3x2,
	DMat3x3,
	DMat3x4,
	DMat4x2,
	DMat4x3,
	DMat4x4,
	Sampler1d,
	Sampler2d,
	Sampler3d,
	SamplerCube,
	Sampler2dRect,
	Sampler1dArray,
	Sampler2dArray,
	SamplerCubeArray,
	SamplerBuffer,
	Sampler2dms,
	Sampler2dmsArray,
	ISampler1d,
	ISampler2d,
	ISampler3d,
	ISamplerCube,
	ISampler2dRect,
	ISampler1dArray,
	ISampler2dArray,
	ISamplerCubeArray,
	ISamplerBuffer,
	ISampler2dms,
	ISampler2dmsArray,
	USampler1d,
	USampler2d,
	USampler3d,
	USamplerCube,
	USampler2dRect,
	USampler1dArray,
	USampler2dArray,
	USamplerCubeArray,
	USamplerBuffer,
	USampler2dms,
	USampler2dmsArray,
	Sampler1dShadow,
	Sampler2dShadow,
	SamplerCubeShadow,
	Sampler2dRectShadow,
	Sampler1dArrayShadow,
	Sampler2dArrayShadow,
	SamplerCubeArrayShadow,
	Image1d,
	Image2d,
	Image3d,
	ImageCube,
	Image2dRect,
	Image1dArray,
	Image2dArray,
	ImageCubeArray,
	ImageBuffer,
	Image2dms,
	Image2dmsArray,
	IImage1d,
	IImage2d,
	IImage3d,
	IImageCube,
	IImage2dRect,
	IImage1dArray,
	IImage2dArray,
	IImageCubeArray,
	IImageBuffer,
	IImage2dms,
	IImage2dmsArray,
	UImage1d,
	UImage2d,
	UImage3d,
	UImageCube,
	UImage2dRect,
	UImage1dArray,
	UImage2dArray,
	UImageCubeArray,
	UImageBuffer,
	UImage2dms,
	UImage2dmsArray,
	AtomicUint,
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

	#[inline]
	pub fn as_ref(&self) -> Omittable<&T> {
		match self {
			Self::Some(x) => Omittable::Some(&x),
			Self::None => Omittable::None,
		}
	}

	#[inline]
	pub fn as_mut(&mut self) -> Omittable<&mut T> {
		match self {
			Self::Some(x) => Omittable::Some(x),
			Self::None => Omittable::None,
		}
	}

	/// Maps an `Omittable<T>` to an `Omittable<U>` by applying a function to a contained value.
	#[inline]
	pub fn map<U, F>(self, f: F) -> Omittable<U>
	where
		F: FnOnce(T) -> U,
	{
		match self {
			Self::Some(x) => Omittable::Some(f(x)),
			Self::None => Omittable::None,
		}
	}

	/// Applies a function to the contained value, or returns the provided default.
	#[inline]
	pub fn map_or<U, F>(self, default: U, f: F) -> U
	where
		F: FnOnce(T) -> U,
	{
		match self {
			Self::Some(x) => f(x),
			Self::None => default,
		}
	}

	/// Returns the contained [`Some`](Omittable::Some) value, or panics.
	///
	/// # Panics
	/// Panics if self is [`None`](Omittable::None).
	#[inline]
	pub fn unwrap(self) -> T {
		match self {
			Self::Some(x) => x,
			Self::None => {
				panic!("called `Omittable::unwrap()` on a `None` value")
			}
		}
	}

	/// Returns the contained [`Some`](Omittable::Some) value or a provided default.
	#[inline]
	pub fn unwrap_or(self, default: T) -> T {
		match self {
			Self::Some(x) => x,
			Self::None => default,
		}
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
	/// Returns the type handle of this type.
	pub(crate) fn type_handle(&self) -> Either<Primitive, StructHandle> {
		match self.ty {
			TypeTy::Single(e) => e,
			TypeTy::Array(e, _) => e,
			TypeTy::Array2D(e, _, _) => e,
			TypeTy::ArrayND(e, _) => e,
		}
	}

	/// Returns whether this type is an array.
	pub(crate) fn is_array(&self) -> bool {
		match self.ty {
			TypeTy::Single(_) => false,
			TypeTy::Array(_, _)
			| TypeTy::Array2D(_, _, _)
			| TypeTy::ArrayND(_, _) => true,
		}
	}

	pub(crate) fn span_start(&self) -> usize {
		if let Omittable::Some(qualifiers) = &self.qualifiers {
			qualifiers.first().span.start
		} else {
			self.ty_specifier_span.start
		}
	}
}

impl SubroutineType {
	pub(crate) fn handle(&self) -> super::SubroutineHandle {
		match self.ty {
			SubroutineTypeTy::Single(h)
			| SubroutineTypeTy::Array(h, _)
			| SubroutineTypeTy::Array2D(h, _, _)
			| SubroutineTypeTy::ArrayND(h, _) => h,
		}
	}

	pub(crate) fn span_start(&self) -> usize {
		if let Omittable::Some(qualifiers) = &self.qualifiers {
			qualifiers.first().span.start
		} else {
			self.ty_specifier_span.start
		}
	}
}

impl Primitive {
	/// Tries to parse an identifier into a primitive type.
	pub fn parse(ident: &Ident) -> Option<Self> {
		match ident.name.as_ref() {
			"void" => Some(Primitive::Void),
			"bool" => Some(Primitive::Bool),
			"int" => Some(Primitive::Int),
			"uint" => Some(Primitive::Uint),
			"float" => Some(Primitive::Float),
			"double" => Some(Primitive::Double),
			"vec2" => Some(Primitive::Vec2),
			"vec3" => Some(Primitive::Vec3),
			"vec4" => Some(Primitive::Vec4),
			"bvec2" => Some(Primitive::BVec2),
			"bvec3" => Some(Primitive::BVec3),
			"bvec4" => Some(Primitive::BVec4),
			"ivec2" => Some(Primitive::IVec2),
			"ivec3" => Some(Primitive::IVec3),
			"ivec4" => Some(Primitive::IVec4),
			"uvec2" => Some(Primitive::UVec2),
			"uvec3" => Some(Primitive::UVec3),
			"uvec4" => Some(Primitive::UVec4),
			"dvec2" => Some(Primitive::DVec2),
			"dvec3" => Some(Primitive::DVec3),
			"dvec4" => Some(Primitive::DVec4),
			"mat2" => Some(Primitive::Mat2x2),
			"mat2x2" => Some(Primitive::Mat2x2),
			"mat2x3" => Some(Primitive::Mat2x3),
			"mat2x4" => Some(Primitive::Mat2x4),
			"mat3x2" => Some(Primitive::Mat3x2),
			"mat3" => Some(Primitive::Mat3x3),
			"mat3x3" => Some(Primitive::Mat3x3),
			"mat3x4" => Some(Primitive::Mat3x4),
			"mat4x2" => Some(Primitive::Mat4x2),
			"mat4x3" => Some(Primitive::Mat4x3),
			"mat4" => Some(Primitive::Mat4x4),
			"mat4x4" => Some(Primitive::Mat4x4),
			"dmat2" => Some(Primitive::DMat2x2),
			"dmat2x2" => Some(Primitive::DMat2x2),
			"dmat2x3" => Some(Primitive::DMat2x3),
			"dmat2x4" => Some(Primitive::DMat2x4),
			"dmat3x2" => Some(Primitive::DMat3x2),
			"dmat3" => Some(Primitive::DMat3x3),
			"dmat3x3" => Some(Primitive::DMat3x3),
			"dmat3x4" => Some(Primitive::DMat3x4),
			"dmat4x2" => Some(Primitive::DMat4x2),
			"dmat4x3" => Some(Primitive::DMat4x3),
			"dmat4" => Some(Primitive::DMat4x4),
			"dmat4x4" => Some(Primitive::DMat4x4),
			"sampler1D" => Some(Primitive::Sampler1d),
			"sampler2D" => Some(Primitive::Sampler2d),
			"sampler3D" => Some(Primitive::Sampler3d),
			"samplerCube" => Some(Primitive::SamplerCube),
			"sampler2DRect" => Some(Primitive::Sampler2dRect),
			"sampler1DArray" => Some(Primitive::Sampler1dArray),
			"sampler2DArray" => Some(Primitive::Sampler2dArray),
			"samplerCubeArray" => Some(Primitive::SamplerCubeArray),
			"samplerBuffer" => Some(Primitive::SamplerBuffer),
			"sampler2DMS" => Some(Primitive::Sampler2dms),
			"sampler2DMSArray" => Some(Primitive::Sampler2dmsArray),
			"isampler1D" => Some(Primitive::ISampler1d),
			"isampler2D" => Some(Primitive::ISampler2d),
			"isampler3D" => Some(Primitive::ISampler3d),
			"isamplerCube" => Some(Primitive::ISamplerCube),
			"isampler2DRect" => Some(Primitive::ISampler2dRect),
			"isampler1DArray" => Some(Primitive::ISampler1dArray),
			"isampler2DArray" => Some(Primitive::ISampler2dArray),
			"isamplerCubeArray" => Some(Primitive::ISamplerCubeArray),
			"isamplerBuffer" => Some(Primitive::ISamplerBuffer),
			"isampler2DMS" => Some(Primitive::ISampler2dms),
			"isampler2DMSArray" => Some(Primitive::ISampler2dmsArray),
			"usampler1D" => Some(Primitive::USampler1d),
			"usampler2D" => Some(Primitive::USampler2d),
			"usampler3D" => Some(Primitive::USampler3d),
			"usamplerCube" => Some(Primitive::USamplerCube),
			"usampler2DRect" => Some(Primitive::USampler2dRect),
			"usampler1DArray" => Some(Primitive::USampler1dArray),
			"usampler2DArray" => Some(Primitive::USampler2dArray),
			"usamplerCubeArray" => Some(Primitive::USamplerCubeArray),
			"usamplerBuffer" => Some(Primitive::USamplerBuffer),
			"usampler2DMS" => Some(Primitive::USampler2dms),
			"usampler2DMSArray" => Some(Primitive::USampler2dmsArray),
			"sampler1DShadow" => Some(Primitive::Sampler1dShadow),
			"sampler2DShadow" => Some(Primitive::Sampler2dShadow),
			"samplerCubeShadow" => Some(Primitive::SamplerCubeShadow),
			"sampler2DRectShadow" => Some(Primitive::Sampler2dRectShadow),
			"sampler1DArrayShadow" => Some(Primitive::Sampler1dArrayShadow),
			"sampler2DArrayShadow" => Some(Primitive::Sampler2dArrayShadow),
			"samplerCubeArrayShadow" => Some(Primitive::SamplerCubeArrayShadow),
			"image1D" => Some(Primitive::Image1d),
			"image2D" => Some(Primitive::Image2d),
			"image3D" => Some(Primitive::Image3d),
			"imageCube" => Some(Primitive::ImageCube),
			"image2DRect" => Some(Primitive::Image2dRect),
			"image1DArray" => Some(Primitive::Image1dArray),
			"image2DArray" => Some(Primitive::Image2dArray),
			"imageCubeArray" => Some(Primitive::ImageCubeArray),
			"imageBuffer" => Some(Primitive::ImageBuffer),
			"image2DMS" => Some(Primitive::Image2dms),
			"image2DMSArray" => Some(Primitive::Image2dmsArray),
			"iimage1D" => Some(Primitive::IImage1d),
			"iimage2D" => Some(Primitive::IImage2d),
			"iimage3D" => Some(Primitive::IImage3d),
			"iimageCube" => Some(Primitive::IImageCube),
			"iimage2DRect" => Some(Primitive::IImage2dRect),
			"iimage1DArray" => Some(Primitive::IImage1dArray),
			"iimage2DArray" => Some(Primitive::IImage2dArray),
			"iimageCubeArray" => Some(Primitive::IImageCubeArray),
			"iimageBuffer" => Some(Primitive::IImageBuffer),
			"iimage2DMS" => Some(Primitive::IImage2dms),
			"iimage2DMSArray" => Some(Primitive::IImage2dmsArray),
			"uimage1D" => Some(Primitive::UImage1d),
			"uimage2D" => Some(Primitive::UImage2d),
			"uimage3D" => Some(Primitive::UImage3d),
			"uimageCube" => Some(Primitive::UImageCube),
			"uimage2DRect" => Some(Primitive::UImage2dRect),
			"uimage1DArray" => Some(Primitive::UImage1dArray),
			"uimage2DArray" => Some(Primitive::UImage2dArray),
			"uimageCubeArray" => Some(Primitive::UImageCubeArray),
			"uimageBuffer" => Some(Primitive::UImageBuffer),
			"uimage2DMS" => Some(Primitive::UImage2dms),
			"uimage2DMSArray" => Some(Primitive::UImage2dmsArray),
			"atomic_uint" => Some(Primitive::AtomicUint),
			_ => None,
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
	/// An expression that wasn't syntactically well formed in some way.
	Invalid,
	/// A literal constant.
	Lit(Lit),
	/// A variable.
	Local {
		name: Ident,
		handle: super::VariableHandle,
	},
	/// A prefix operation.
	Prefix { op: PreOp, expr: Box<Expr> },
	/// A postfix operation.
	Postfix { expr: Box<Expr>, op: PostOp },
	/// A binary operation.
	Binary {
		left: Box<Expr>,
		op: BinOp,
		right: Box<Expr>,
	},
	/// A ternary operation.
	Ternary {
		cond: Box<Expr>,
		true_: Box<Expr>,
		false_: Box<Expr>,
	},
	/// An expression wrapped within parenthesis.
	Parens { expr: Box<Expr> },
	/// Object access.
	ObjAccess {
		/// The root object that is accessed.
		///
		/// # Invariants
		/// This will be one of the following:
		/// - `ExprTy::Local`,
		/// - `ExprTy::FnCall` (currently unimplemented),
		/// - `ExprTy::SubroutineCall`,
		/// - `ExprTy::StructConstructor`.
		obj: Box<Expr>,
		/// - `A` - struct field,
		/// - `B` - `length()` method (only on supported types),
		/// - `C` - swizzle (only on vectors).
		leafs: Vec<(Ident, Either3<super::StructFieldHandle, (), Swizzle>)>,
	},
	/// An index operation.
	Index {
		item: Box<Expr>,
		i: Omittable<Box<Expr>>,
	},
	/// A function call.
	FnCall {
		name: Ident,
		handle: super::FunctionHandle,
		args: Vec<Expr>,
	},
	/// A subroutine call.
	SubroutineCall {
		name: Ident,
		handle: super::SubroutineHandle,
		args: Vec<Expr>,
	},
	/// A struct constructor.
	StructConstructor {
		name: Ident,
		handle: super::StructHandle,
		args: Vec<Expr>,
	},
	/// An initializer list.
	Initializer { args: Vec<Expr> },
	/// An array constructor.
	ArrConstructor { type_: Box<Type>, args: Vec<Expr> },
	/// A general list expression, e.g. `a, b`.
	List { items: Vec<Expr> },
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

/// A vector swizzle.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Swizzle {
	/// The buffer of swizzle components. Each value represents one axis component.
	///
	/// Only the values within the `[0..len]` range are relevant, anything outside can be disgarded. The reason
	/// this is done this way is in order to have a fixed length array and avoid allocating a vec on the heap.
	pub buf: [Axis; 4],
	/// Number of swizzle components. This is the length of `buf` that should be read, e.g. `buf[0..len]`.
	///
	/// # Invariants
	/// Has a value in the range `[1, 4]`.
	pub len: u8,
	pub span: Span,
}

/// Describes an axis.
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Axis {
	X = 0,
	Y = 1,
	Z = 2,
	W = 3,
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

/// AST items for conditional directive expressions.
pub(crate) mod conditional {
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
