use crate::cst::{Expr, ExprTy};

// Re-export shared types. This is to make things clearer. If you're operating on the AST, you only import from the
// ast module as opposed to importing some stuff from here and some stuff from cst, and maybe even some stuff from
// lexer.
pub use crate::cst::Ident;

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

/// A texture type of a `sampler_` or `image_` primitive type.
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
	/// An atomic counter type.
	Atomic,
}

impl Primitive {
	#[rustfmt::skip]
	pub fn parse(ident: &Ident) -> Self {
		match ident.name.as_ref() {
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

pub type ArrSize = Option<Expr>;

/// A language type.
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

impl Type {
	/// Tries to parse an [`Expr`] into a `Type`, e.g. `int` or `MyStruct` or `float[3][2]`.
	pub fn parse(expr: &Expr) -> Option<Self> {
		match &expr.ty {
			ExprTy::Ident(i) => Some(Self::Basic(Primitive::parse(i))),
			ExprTy::Index { item, i, .. } => {
				let mut current_item = item;
				let mut stack = Vec::new();
				stack.push(i.as_deref());

				let primitive = loop {
					match &current_item.ty {
						ExprTy::Ident(i) => {
							break Primitive::parse(i);
						}
						ExprTy::Index { item, i, .. } => {
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
