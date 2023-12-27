use super::{
	ast, Ctx, FunctionHandle, NodeHandle, StructHandle, SubroutineUniformHandle,
};
use crate::{
	syntax::{SyntaxModifiers, SyntaxType},
	Either, Either3, Span,
};
use tinyvec::{tiny_vec, TinyVec};

/// A struct symbol.
#[derive(Debug)]
pub struct StructSymbol {
	/// Handle to the `StructDecl` or `StructDef` node, or to an `InterfaceDef` node if `self.is_interface = true`.
	pub def_node: NodeHandle,
	/// The name.
	pub name: String,
	/// The fields. Unlike the node itself, which can contain any child nodes within, this only contains field
	/// information and nothing else.
	pub fields: Vec<StructField>,
	/// All references to this struct. This includes the name in the struct declaration/definition itself.
	pub refs: Vec<Span>,
	/// Whether this struct is an interface block.
	pub is_interface: bool,
}

/// An interface block symbol.
///
/// Unlike the [`StructSymbol`], this symbol does not have references because interface block names cannot be used
/// anywhere else in the same shader. An interface block **is not** a type, unlike a struct.
#[derive(Debug)]
pub struct InterfaceSymbol {
	/// Handle to the `InterfaceDef` node.
	pub def_node: NodeHandle,
	/// The name.
	pub name: String,
	/// The fields. Unlike the node itself, which can contain any child nodes within, this only contains field
	/// information and nothing else.
	pub fields: Vec<StructField>,
}

/// A field within a struct symbol.
#[derive(Debug)]
pub struct StructField {
	/// The type.
	pub type_: Type,
	/// The name. A field can lack a name, in which case it is un-referencable and really just in the struct
	/// definition for padding purposes.
	pub name: ast::Omittable<String>,
	/// All references to this field. This includes the field name itself.
	pub refs: Vec<Span>,
}

/// A function symbol.
#[derive(Debug)]
pub struct FunctionSymbol {
	/// Whether this function is built-in.
	pub built_in: bool,
	/// The name.
	pub name: String,
	/// All function signatures that share this name. If there is more than one signature, that means this function
	/// is overloaded.
	pub signatures: Vec<FunctionSignature>,
	/// All references of this function. This includes the name in all signature declarations/definitions
	/// themselves.
	pub refs: Vec<Span>,
}

/// A function signature. There can be more than one function signature for a given function symbol if that symbol
/// is overloaded.
#[derive(Debug)]
pub struct FunctionSignature {
	/// Handles to any `FnDecl` nodes.
	pub decl_nodes: Vec<NodeHandle>,
	/// Handle to a `FnDef` node, or to a `SubroutineFnDefAssociation` node (only if this symbol is sourced from a
	/// [`SubroutineSymbol`]). Only one definition is allowed per function signature.
	pub def_node: Option<NodeHandle>,
	/// The name.
	pub name: String,
	/// The parameters for this overload.
	pub params: Vec<FunctionParam>,
	/// The return type for this overload.
	pub return_type: Type,
}

/// A parameter within a function symbol.
#[derive(Debug, PartialEq)]
pub struct FunctionParam {
	/// The type.
	pub type_: Type,
	/// The name. A parameter can lack a name, in which case it is un-referencable.
	pub name: ast::Omittable<String>,
	/// All references to this parameter. This includes the parameter name itself.
	pub refs: Vec<Span>,
}

/// A subroutine symbol.
#[derive(Debug)]
pub struct SubroutineSymbol {
	/// Handle to a `SubroutineTypeDecl` node.
	pub decl_node: NodeHandle,
	/// The name
	pub name: String,
	/// The parameters.
	pub params: Vec<FunctionParam>,
	/// The return type.
	pub return_type: Type,
	/// All uniforms for this subroutine.
	pub uniforms: Vec<SubroutineUniformHandle>,
	/// All associated functions for this subroutine.
	pub associated_fns: Vec<FunctionHandle>,
	/// All references to this subroutine type. This includes the name in the subroutine type declaration itself.
	pub refs: Vec<Span>,
}

/// A subroutine uniform symbol. This is handled separately from a [`VariableSymbol`] because, unlike normal
/// variables, this is treated as a callable function, i.e. a subroutine uniform `my_choice` is used/referenced by
/// `my_choice()`.
#[derive(Debug)]
pub struct SubroutineUniformSymbol {
	/// Handle to a `SubroutineUniformDef`/`SubroutineUniformDefs` node.
	pub def_node: NodeHandle,
	/// The type. Contains a handle to the [`SubroutineSymbol`].
	pub type_: ast::SubroutineType,
	/// The name of the subroutine uniform.
	pub name: String,
	/// All references to this callable uniform variable. This includes the name in the variable definition itself.
	pub refs: Vec<Span>,
}

/// A variable symbol table.
pub type VariableSymbolTable = Vec<VariableSymbol>;

/// A variable symbol.
#[derive(Debug)]
pub struct VariableSymbol {
	/// Handle to one of the following nodes:
	/// - `VarDef`/`VarDefs`/`VarDefInit`/`VarDefsInits`,
	/// - `StructDef`; means that at least `node.instances[0]` exists.
	/// - `FnDef`; means that at least `node.params[0]` exists.
	/// - `InterfaceDef`;
	pub def_node: NodeHandle,
	/// The type.
	pub type_: Type,
	/// The name.
	pub name: String,
	/// The syntax highlighting token for this variable. The information for this could be found just by looking
	/// through the `type_` and `def_node` fields, but by storing it here we remove lookup costs.
	pub syntax: (SyntaxType, SyntaxModifiers),
	/// All references to this variable. This includes the name in the variable definition itself.
	pub refs: Vec<Span>,
}

/// A type.
///
/// Similar to NaNs in floating point numbers, a not-a-type is still represented as a `Type` rather than as an
/// `Option<Type>` or `Result<Type, E>`. This is because we only check the validity of a type at its creation (and
/// emit appropriate diagnostics). Afterwards, during typechecking, any checks on a not-a-type always evaluate to
/// false, and any comparisons/coercions against a not-a-type evaluate to the other type (i.e. similar to the
/// coercion of the `!` rust type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
	/* not-a-type is marked by `ty = Either::Right(StructHandle(usize::MAX))` */
	/// The typename. Either a primitive or a handle to a struct.
	pub ty: Either<ast::Primitive, StructHandle>,
	/// The array sizes in descending order; highest dimension first, lowest dimension last.
	pub arr: TinyVec<[usize; 3]>,
	/* Should be optimized to an 11-field bitfield */
	pub is_const: bool,
	pub is_in: bool,
	pub is_out: bool,
	pub is_param_in: bool,
	pub is_param_out: bool,
	pub is_param_inout: bool,
	pub is_coherent: bool,
	pub is_volatile: bool,
	pub is_restrict: bool,
	pub is_readonly: bool,
	pub is_writeonly: bool,
}

impl Type {
	/// Constructs a new type from a primitive.
	pub fn new_prim(p: ast::Primitive) -> Self {
		Self {
			ty: Either::Left(p),
			arr: TinyVec::new(),
			is_const: false,
			is_in: false,
			is_out: false,
			is_param_in: false,
			is_param_out: false,
			is_param_inout: false,
			is_coherent: false,
			is_volatile: false,
			is_restrict: false,
			is_readonly: false,
			is_writeonly: false,
		}
	}

	/// Constructs a new type from a struct handle.
	pub fn new_struct(handle: StructHandle) -> Self {
		Self {
			ty: Either::Right(handle),
			arr: TinyVec::new(),
			is_const: false,
			is_in: false,
			is_out: false,
			is_param_in: false,
			is_param_out: false,
			is_param_inout: false,
			is_coherent: false,
			is_volatile: false,
			is_restrict: false,
			is_readonly: false,
			is_writeonly: false,
		}
	}

	/// Constructs a new non-a-type.
	pub fn new_nat() -> Self {
		Self {
			ty: Either::Right(StructHandle(usize::MAX)),
			arr: TinyVec::new(),
			is_const: false,
			is_in: false,
			is_out: false,
			is_param_in: false,
			is_param_out: false,
			is_param_inout: false,
			is_coherent: false,
			is_volatile: false,
			is_restrict: false,
			is_readonly: false,
			is_writeonly: false,
		}
	}

	/// Returns whether this is not-a-type.
	pub fn is_not_a_type(&self) -> bool {
		match &self.ty {
			Either::Left(_) => false,
			Either::Right(handle) => handle.0 == usize::MAX,
		}
	}

	/// Returns whether this type is an array.
	pub fn is_array(&self) -> bool {
		!self.is_not_a_type() && !self.arr.is_empty()
	}

	pub fn is_component_bool(&self) -> bool {
		use ast::Primitive;

		!self.is_not_a_type()
			&& match self.ty {
				Either::Left(p) => match p {
					Primitive::Bool
					| Primitive::BVec2
					| Primitive::BVec3
					| Primitive::BVec4 => true,
					_ => false,
				},
				Either::Right(_) => false,
			}
	}

	pub fn is_component_numeric(&self) -> bool {
		use ast::Primitive;

		!self.is_not_a_type()
			&& match self.ty {
				Either::Left(p) => match p {
					Primitive::Int
					| Primitive::Uint
					| Primitive::Float
					| Primitive::Double
					| Primitive::IVec2
					| Primitive::IVec3
					| Primitive::IVec4
					| Primitive::UVec2
					| Primitive::UVec3
					| Primitive::UVec4
					| Primitive::Vec2
					| Primitive::Vec3
					| Primitive::Vec4
					| Primitive::DVec2
					| Primitive::DVec3
					| Primitive::DVec4
					| Primitive::Mat2x2
					| Primitive::Mat2x3
					| Primitive::Mat2x4
					| Primitive::Mat3x2
					| Primitive::Mat3x3
					| Primitive::Mat3x4
					| Primitive::Mat4x2
					| Primitive::Mat4x3
					| Primitive::Mat4x4
					| Primitive::DMat2x2
					| Primitive::DMat2x3
					| Primitive::DMat2x4
					| Primitive::DMat3x2
					| Primitive::DMat3x3
					| Primitive::DMat3x4
					| Primitive::DMat4x2
					| Primitive::DMat4x3
					| Primitive::DMat4x4 => true,
					_ => false,
				},
				Either::Right(_) => false,
			}
	}

	/// Returns whether this type is a struct.
	pub fn is_struct(&self) -> bool {
		!self.is_not_a_type()
			&& match self.ty {
				Either::Left(_) => false,
				Either::Right(_) => true,
			}
	}

	/// Tests whether this type is identical to the other type.
	pub fn is_identical_to(&self, other: &Type) -> bool {
		!self.is_not_a_type() && self == other
	}

	/// Tests whether this type can be coerced into the other type.
	pub fn can_be_coerced_into(&self, other: &Type) -> bool {
		use ast::Primitive;

		if self.is_not_a_type() || other.is_not_a_type() {
			return true;
		}

		if !self.arr.is_empty() || !other.arr.is_empty() {
			return false;
		}

		let (s, o) = match (self.ty, other.ty) {
			(Either::Left(s), Either::Left(o)) => (s, o),
			_ => return false,
		};

		if s == o {
			return true;
		}

		match (s, o) {
			(Primitive::Int, Primitive::Uint)
			| (Primitive::Int, Primitive::Float)
			| (Primitive::Uint, Primitive::Float)
			| (Primitive::Int, Primitive::Double)
			| (Primitive::Uint, Primitive::Double)
			| (Primitive::Float, Primitive::Double) => true,
			(Primitive::IVec2, Primitive::UVec2)
			| (Primitive::IVec3, Primitive::UVec3)
			| (Primitive::IVec4, Primitive::UVec4)
			| (Primitive::IVec2, Primitive::Vec2)
			| (Primitive::IVec3, Primitive::Vec3)
			| (Primitive::IVec4, Primitive::Vec4)
			| (Primitive::UVec2, Primitive::Vec2)
			| (Primitive::UVec3, Primitive::Vec3)
			| (Primitive::UVec4, Primitive::Vec4)
			| (Primitive::IVec2, Primitive::DVec2)
			| (Primitive::IVec3, Primitive::DVec3)
			| (Primitive::IVec4, Primitive::DVec4)
			| (Primitive::UVec2, Primitive::DVec2)
			| (Primitive::UVec3, Primitive::DVec3)
			| (Primitive::UVec4, Primitive::DVec4)
			| (Primitive::Vec2, Primitive::DVec2)
			| (Primitive::Vec3, Primitive::DVec3)
			| (Primitive::Vec4, Primitive::DVec4) => true,
			(Primitive::Mat2x2, Primitive::DMat2x2)
			| (Primitive::Mat2x3, Primitive::DMat2x3)
			| (Primitive::Mat2x4, Primitive::DMat2x4)
			| (Primitive::Mat3x2, Primitive::DMat3x2)
			| (Primitive::Mat3x3, Primitive::DMat3x3)
			| (Primitive::Mat3x4, Primitive::DMat3x4)
			| (Primitive::Mat4x2, Primitive::DMat4x2)
			| (Primitive::Mat4x3, Primitive::DMat4x3)
			| (Primitive::Mat4x4, Primitive::DMat4x4) => true,
			_ => false,
		}
	}

	/// Tests whether this type can be passed into a parameter.
	pub fn can_be_passed_into(&self, param: &Type) -> bool {
		if self.is_not_a_type() || param.is_not_a_type() {
			return true;
		}
		todo!()
	}

	/// Returns a common type that both types can be coerced to. If there is no common type, this function returns
	/// an `Err`.
	///
	/// # Invariants
	/// This function assumes that the types are not identical.
	pub fn coerce_binary_types(a: &Self, b: &Self) -> Result<Self, ()> {
		use ast::Primitive;

		match (a.is_not_a_type(), b.is_not_a_type()) {
			(true, true) => return Ok(Type::new_nat()),
			(true, false) => return Ok(b.clone()),
			(false, true) => return Ok(a.clone()),
			_ => {}
		}

		if !a.arr.is_empty() || !b.arr.is_empty() {
			return Err(());
		}

		let (a, b) = match (a.ty, b.ty) {
			(Either::Left(s), Either::Left(o)) => (s, o),
			_ => return Err(()),
		};

		if a == b {
			return Ok(Type::new_prim(a));
		}

		let coerce = |a, b| match (a, b) {
			(Primitive::Int, Primitive::Uint) => Ok(Primitive::Uint),
			(Primitive::Int, Primitive::Float)
			| (Primitive::Uint, Primitive::Float) => Ok(Primitive::Float),
			(Primitive::Int, Primitive::Double)
			| (Primitive::Uint, Primitive::Double)
			| (Primitive::Float, Primitive::Double) => Ok(Primitive::Double),
			(Primitive::IVec2, Primitive::UVec2) => Ok(Primitive::UVec2),
			(Primitive::IVec3, Primitive::UVec3) => Ok(Primitive::UVec3),
			(Primitive::IVec4, Primitive::UVec4) => Ok(Primitive::UVec4),
			(Primitive::IVec2, Primitive::Vec2) => Ok(Primitive::Vec2),
			(Primitive::IVec3, Primitive::Vec3) => Ok(Primitive::Vec3),
			(Primitive::IVec4, Primitive::Vec4) => Ok(Primitive::Vec4),
			(Primitive::UVec2, Primitive::Vec2) => Ok(Primitive::Vec2),
			(Primitive::UVec3, Primitive::Vec3) => Ok(Primitive::Vec3),
			(Primitive::UVec4, Primitive::Vec4) => Ok(Primitive::Vec4),
			(Primitive::IVec2, Primitive::DVec2) => Ok(Primitive::DVec2),
			(Primitive::IVec3, Primitive::DVec3) => Ok(Primitive::DVec3),
			(Primitive::IVec4, Primitive::DVec4) => Ok(Primitive::DVec4),
			(Primitive::UVec2, Primitive::DVec2) => Ok(Primitive::DVec2),
			(Primitive::UVec3, Primitive::DVec3) => Ok(Primitive::DVec3),
			(Primitive::UVec4, Primitive::DVec4) => Ok(Primitive::DVec4),
			(Primitive::Vec2, Primitive::DVec2) => Ok(Primitive::DVec2),
			(Primitive::Vec3, Primitive::DVec3) => Ok(Primitive::DVec3),
			(Primitive::Vec4, Primitive::DVec4) => Ok(Primitive::DVec4),
			(Primitive::Mat2x2, Primitive::DMat2x2) => Ok(Primitive::DMat2x2),
			(Primitive::Mat2x3, Primitive::DMat2x3) => Ok(Primitive::DMat2x3),
			(Primitive::Mat2x4, Primitive::DMat2x4) => Ok(Primitive::DMat2x4),
			(Primitive::Mat3x2, Primitive::DMat3x2) => Ok(Primitive::DMat3x2),
			(Primitive::Mat3x3, Primitive::DMat3x3) => Ok(Primitive::DMat3x3),
			(Primitive::Mat3x4, Primitive::DMat3x4) => Ok(Primitive::DMat3x4),
			(Primitive::Mat4x2, Primitive::DMat4x2) => Ok(Primitive::DMat4x2),
			(Primitive::Mat4x3, Primitive::DMat4x3) => Ok(Primitive::DMat4x3),
			(Primitive::Mat4x4, Primitive::DMat4x4) => Ok(Primitive::DMat4x4),
			_ => Err(()),
		};

		// The check only goes one way, so if it fails at first we want to try with the types ordered the other way
		// around.
		match coerce(a, b) {
			Ok(p) => Ok(Type::new_prim(p)),
			Err(_) => match coerce(b, a) {
				Ok(p) => Ok(Type::new_prim(p)),
				Err(_) => Err(()),
			},
		}
	}

	pub fn can_apply_postop(&self) -> bool {
		self.is_component_numeric()
	}

	pub fn can_apply_preop(&self, op: ast::PreOpTy) -> bool {
		use ast::PreOpTy;
		use ast::Primitive;

		let Either::Left(ty) = self.ty else {
			// Structs categorically cannot have operators applied to them.
			return false;
		};

		match op {
			PreOpTy::Add | PreOpTy::Sub | PreOpTy::Neg => {
				self.is_component_numeric()
			}
			PreOpTy::Flip => match ty {
				Primitive::Int
				| Primitive::Uint
				| Primitive::IVec2
				| Primitive::IVec3
				| Primitive::IVec4
				| Primitive::UVec2
				| Primitive::UVec3
				| Primitive::UVec4 => true,
				_ => false,
			},
			PreOpTy::Not => match ty {
				Primitive::Bool => true,
				_ => false,
			},
		}
	}

	pub fn index_into(&self) -> Result<Self, ()> {
		if self.is_array() {
			let mut new = self.clone();
			new.arr.pop();
			Ok(new)
		} else {
			Err(())
		}
	}

	pub fn type_name(&self, ctx: &Ctx) -> String {
		if self.is_not_a_type() {
			return "{unknown}".to_owned();
		}

		match self.ty {
			Either::Left(prim) => format!("{prim}"),
			Either::Right(handle) => ctx.structs[handle.0].name.clone(),
		}
	}
}

impl From<ast::Type> for Type {
	fn from(value: ast::Type) -> Self {
		let ast::Type {
			ty,
			qualifiers,
			ty_specifier_span,
			disjointed_span,
		} = value;
		let (ty, arr) = match ty {
			ast::TypeTy::Single(h) => (h, TinyVec::new()),
			ast::TypeTy::Array(h, x) => (h, tiny_vec!(0)),
			ast::TypeTy::Array2D(h, x, y) => (h, tiny_vec!(0, 0)),
			ast::TypeTy::ArrayND(h, arr) => {
				let mut v = TinyVec::new();
				v.resize_with(arr.len(), || 0);
				(h, v)
			}
		};
		Self {
			ty,
			arr,
			is_const: false,
			is_in: false,
			is_out: false,
			is_param_in: false,
			is_param_out: false,
			is_param_inout: false,
			is_coherent: false,
			is_volatile: false,
			is_restrict: false,
			is_readonly: false,
			is_writeonly: false,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use ast::Primitive;

	macro_rules! prim {
		($prim:expr) => {
			Type {
				ty: Either::Left($prim),
				arr: TinyVec::new(),
				is_const: false,
				is_in: false,
				is_out: false,
				is_param_in: false,
				is_param_out: false,
				is_param_inout: false,
				is_coherent: false,
				is_volatile: false,
				is_restrict: false,
				is_readonly: false,
				is_writeonly: false,
			}
		};
	}
	#[test]
	fn type_coercions() {
		assert!(
			prim!(Primitive::Int).can_be_coerced_into(&prim!(Primitive::Uint))
		);
		assert!(
			prim!(Primitive::Int).can_be_coerced_into(&prim!(Primitive::Float))
		);
		assert!(prim!(Primitive::Int)
			.can_be_coerced_into(&prim!(Primitive::Double)));
	}
}
