use crate::parser::OpType;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
	/// A literal value, either a number, a boolean or an identifier.
	Literal(String),
	/// A negation of an expression.
	Neg(Box<Expr>),
	/// Binary expression with a left and right hand-side.
	Binary {
		left: Box<Expr>,
		op: OpType,
		right: Box<Expr>,
	},
	/// Variable declaration.
	VarDecl {
		type_: String,
		ident: String,
		value: Box<Expr>,
	},
	// Function declaration.
	FnDecl {
		type_: String,
		ident: String,
		body: Vec<Expr>,
	}
}
