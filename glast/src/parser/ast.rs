//! Types and functionality related to the Abstract Syntax Tree.

use crate::{
	diag::Syntax,
	lexer::{NumType, Token},
	Span,
};

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
	/// A return control-flow statement, i.e. `return 5;`.
	Return { value: Option<Expr> },
}

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

/// An identifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
	pub name: String,
	// TODO: Remove this extra unnecessary span.
	pub span: Span,
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
	///   `10000000000000000000000000000000000000`,
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
