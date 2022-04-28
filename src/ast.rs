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
}
