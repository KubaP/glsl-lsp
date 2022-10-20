use crate::span::Span;

/// A node within the abstract syntax tree.
#[derive(Debug, Clone, PartialEq)]
pub struct Node {
	pub ty: NodeTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum NodeTy {
	/// An empty statement, i.e. `;`.
	Empty,
	/// A break control-flow statement, i.e. `break;`.
	Break,
	/// A continue control-flow statement, i.e. `continue;`.
	Continue,
	/// A discard control-flow statement, i.e. `discard;`.
	Discard,
}
