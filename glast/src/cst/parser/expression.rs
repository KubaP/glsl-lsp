#[cfg(test)]
mod arr_init_tests;
#[cfg(test)]
mod bin_op_tests;
#[cfg(test)]
mod fn_tests;
#[cfg(test)]
mod index_tests;
#[cfg(test)]
mod init_list_tests;
#[cfg(test)]
mod list_tests;
#[cfg(test)]
mod lit_tests;
#[cfg(test)]
mod object_access_tests;
#[cfg(test)]
mod paren_tests;
#[cfg(test)]
mod post_op_tests;
#[cfg(test)]
mod pre_op_tests;
#[cfg(test)]
mod ternary_tests;

#[cfg(test)]
macro_rules! assert_expr {
	($source:expr, $rest:expr) => {
		let mut walker = Walker {
			token_stream: parse_from_str($source),
			cursor: 0,
		};
		assert_eq!(
			expr_parser(&mut walker, Mode::Default, &[]).0.unwrap(),
			$rest
		);
	};
}
#[cfg(test)]
pub(self) use assert_expr;

use super::Walker;
use crate::{
	cst::{
		BinOp, BinOpTy, Comment, Comments, Expr, ExprTy, Ident, List, Lit,
		PostOp, PostOpTy, PreOp, PreOpTy,
	},
	error::SyntaxErr,
	log,
	span::{span, Span},
	token::{self, Token},
	Either,
};
use std::collections::VecDeque;

/*
Useful links related to expression parsing:

https://petermalmgren.com/three-rust-parsers/
	- recursive descent parser

https://wcipeg.com/wiki/Shunting_yard_algorithm
	- shunting yard overview & algorithm extensions

https://erikeidt.github.io/The-Double-E-Method
	- stateful shunting yard for unary support

https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
https://matklad.github.io/2020/04/15/from-pratt-to-dijkstra.html
	- two parter, first writing a pratt parser, and then refactoring into a shunting yard parser with a slightly
	  different approach
*/

/// Tries to parse an expression beginning at the current position.
pub(super) fn expr_parser(
	walker: &mut Walker,
	mode: Mode,
	end_tokens: &[Token],
) -> (Option<Expr>, Vec<SyntaxErr>) {
	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		// If we are at the end of the token stream, we can return early with nothing.
		None => return (None, vec![]),
	};

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: VecDeque::new(),
		comments: Vec::new(),
		start_position,
		mode,
		errors: Vec::new(),
	};

	parser.parse(walker, end_tokens);
	(parser.create_ast(), parser.errors)
}

/// Tries to parse an expression beginning at the current position.
/// 
/// This returns:
/// - `0` - An expression if one exists under the cursor,
/// - `1` - Any comments after the expression. If no expression was found, these could be comments found under the
///   cursor,
/// - `2` - Any syntax errors found whilst parsing.
pub(super) fn expr_parser_2(
	walker: &mut Walker,
	mode: Mode,
	end_tokens: &[Token],
) -> (Option<Expr>, Comments, Vec<SyntaxErr>) {
	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		// If we are at the end of the token stream, we can return early with nothing.
		None => return (None, vec![], vec![]),
	};

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: VecDeque::new(),
		comments: Vec::new(),
		start_position,
		mode,
		errors: Vec::new(),
	};

	parser.parse(walker, end_tokens);
	(parser.create_ast(), parser.comments, parser.errors)
}

/// Sets the behaviour of the expression parser.
#[derive(Debug, PartialEq, Eq)]
pub enum Mode {
	/// The default behaviour, which can be used to parse any valid expressions, including those that can form
	/// entire statements, such as `i = 5`.
	Default,
	/// Disallows top-level lists, i.e. upon encountering the first comma (`,`) outside of a group, the parser will
	/// return. E.g. `a, b` would return but `(a, b)` wouldn't.
	DisallowTopLevelList,
	/// Disallows treating assignments as a valid expression, i.e. upon encountering the first `Token::Eq` (`=`),
	/// the parser will return.
	BreakAtEq,
	/// Stops parsing after taking one unit, without producing a lot of the syntax errors that are normally
	/// produced. This mode is mostly useful to take single "expressions", for example, taking a single unit as a
	/// parameter type, and then another single unit as the parameter identifier.
	///
	/// This mode stops parsing at the following:
	/// - missing binary operators, e.g. `int i` or `int (` or `int {`,
	/// - commas in a top-level list, e.g. `int, i` but not `int[a, b]`,
	/// - unmatched closing delimiters, e.g. `int[])` or `int }`,
	/// - equals sign binary operator, e.g. `i = 5`.
	///
	/// In this mode, none of those scenarios generate a syntax error.
	///
	/// E.g. in `int[3],` the parser would break after the end of the index operator.
	///
	/// E.g. in `(float) f`, the parser would break after the end of the parenthesis.
	///
	/// E.g. in `i + 5, b`, the parser would break after the 5.
	///
	/// E.g. in `i = 5`, the parser would break after i.
	///
	/// E.g. in `{1} 2`, the parser would break after the end of the initializer list.
	///
	/// Note that this mode still composes with `end_tokens`, so if that, for example, contains `[Token::LBrace]`,
	/// then `{1} 2` would immediately break and return no expression.
	TakeOneUnit,
}

/// A node; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Node {
	ty: NodeTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum NodeTy {
	Lit(Lit, Comments),
	Ident(Ident, Comments),
	Separator(Comments),
	Invalid(Comments),
}

/// A node operator; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Op {
	ty: OpTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum OpTy {
	/* BINARY OPERATORS */
	/* - `0` - Whether to consume a node for the right-hand side expression. */
	/* - `1` - Any comments before the operator. */
	Add(bool, Comments),
	Sub(bool, Comments),
	Mul(bool, Comments),
	Div(bool, Comments),
	Rem(bool, Comments),
	And(bool, Comments),
	Or(bool, Comments),
	Xor(bool, Comments),
	LShift(bool, Comments),
	RShift(bool, Comments),
	Eq(bool, Comments),
	AddEq(bool, Comments),
	SubEq(bool, Comments),
	MulEq(bool, Comments),
	DivEq(bool, Comments),
	RemEq(bool, Comments),
	AndEq(bool, Comments),
	OrEq(bool, Comments),
	XorEq(bool, Comments),
	LShiftEq(bool, Comments),
	RShiftEq(bool, Comments),
	EqEq(bool, Comments),
	NotEq(bool, Comments),
	AndAnd(bool, Comments),
	OrOr(bool, Comments),
	XorXor(bool, Comments),
	Gt(bool, Comments),
	Lt(bool, Comments),
	Ge(bool, Comments),
	Le(bool, Comments),
	/// - `0` - Whether to consume a node for the leaf expression (after the `.`).
	/// - `1` - Any comments before the `.`
	ObjAccess(bool, Comments),
	/// - `0` - Whether to consume a node for the if expression (after the `?`).
	/// - `1` - Any comments before the `?`
	TernaryQ(bool, Comments),
	/// - `0` - Whether to consume a node for the else expression (after the `:`).
	/// - `1` - Any comments before the `:`
	TernaryC(bool, Comments),
	/* PREFIX OPERATORS */
	/* - `0` - Whether to consume a node for the expression. */
	/* - `1` - Any comments before the operator. */
	AddPre(bool, Comments),
	SubPre(bool, Comments),
	Neg(bool, Comments),
	Flip(bool, Comments),
	Not(bool, Comments),
	/* POSTFIX OPERATORS */
	/* - `0` - Any comments before the operator. */
	AddPost(Comments),
	SubPost(Comments),
	/* GROUP BEGINNING DELIMITERS */
	/// The `(` token.
	/// - `0` - Any comments before the operator.
	ParenStart(Comments),
	/// The `(` token.
	/// - `0` - Any comments before the operator.
	FnCallStart(Comments),
	/// The `[` token.
	/// - `0` - Any comments before the operator.
	IndexStart(Comments),
	/// The `{` token.
	/// - `0` - Any comments before the operator.
	InitStart(Comments),
	/// The `(` token.
	/// - `0` - Any comments before the operator.
	ArrInitStart(Comments),
	/* GROUPS */
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis,
	/// - `1` - The span of the opening parenthesis,
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present,
	/// - `3` - Any comments before the opening parenthesis,
	/// - `4` - Any comments before the closing parenthesis.
	Paren(bool, Span, Span, Comments, Comments),
	/// A function call. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the function identifier node, so it
	///   will always be `1` or greater,
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present,
	/// - `3` - Any comments before the opening parenthesis,
	/// - `4` - Any comments before the closing parenthesis.
	FnCall(usize, Span, Span, Comments, Comments),
	/// An index operator. This operator spans from the opening bracket to the closing bracket.
	///
	/// - `0` - Whether to consume a node for the expression within the `[...]` brackets,
	/// - `1` - The span of the opening bracket,
	/// - `2` - The span of the closing bracket. If this is zero-width, that means there is no `]` token present,
	/// - `3` - Any comments before the opening bracket,
	/// - `4` - Any comments before the closing bracket.
	Index(bool, Span, Span, Comments, Comments),
	/// An initializer list. This operator spans from the opening brace to the closing brace.
	///
	/// - `0` - The number of nodes to consume for the arguments,
	/// - `1` - The span of the opening brace,
	/// - `2` - The span of the closing brace. If this is zero-width, that means there is no `}` token present,
	/// - `3` - Any comments before the opening brace,
	/// - `4` - Any comments before the closing brace.
	Init(usize, Span, Span, Comments, Comments),
	/// An array initializer. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the index expression node, so it
	///   will always be `1` or greater.
	/// - `1` - The span of the opening parenthesis,
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present,
	/// - `3` - Any comments before the opening parenthesis,
	/// - `4` - Any comments before the closing parenthesis.
	ArrInit(usize, Span, Span, Comments, Comments),
	/// A general list **outside** of function calls, initializer lists and array constructors.
	///
	/// - `0` - The number of nodes to consume for the arguments.
	List(usize),
}

impl Op {
	/// Converts from a lexer `OpTy` token to the `Op2` type used in this expression parser.
	fn from_token(token: token::OpTy, span: Span, comments: Comments) -> Self {
		Self {
			span,
			ty: match token {
				token::OpTy::Add => OpTy::Add(false, comments),
				token::OpTy::Sub => OpTy::Sub(false, comments),
				token::OpTy::Mul => OpTy::Mul(false, comments),
				token::OpTy::Div => OpTy::Div(false, comments),
				token::OpTy::Rem => OpTy::Rem(false, comments),
				token::OpTy::And => OpTy::And(false, comments),
				token::OpTy::Or => OpTy::Or(false, comments),
				token::OpTy::Xor => OpTy::Xor(false, comments),
				token::OpTy::LShift => OpTy::LShift(false, comments),
				token::OpTy::RShift => OpTy::RShift(false, comments),
				token::OpTy::Eq => OpTy::Eq(false, comments),
				token::OpTy::AddEq => OpTy::AddEq(false, comments),
				token::OpTy::SubEq => OpTy::SubEq(false, comments),
				token::OpTy::MulEq => OpTy::MulEq(false, comments),
				token::OpTy::DivEq => OpTy::DivEq(false, comments),
				token::OpTy::RemEq => OpTy::RemEq(false, comments),
				token::OpTy::AndEq => OpTy::AndEq(false, comments),
				token::OpTy::OrEq => OpTy::OrEq(false, comments),
				token::OpTy::XorEq => OpTy::XorEq(false, comments),
				token::OpTy::LShiftEq => OpTy::LShiftEq(false, comments),
				token::OpTy::RShiftEq => OpTy::RShiftEq(false, comments),
				token::OpTy::EqEq => OpTy::EqEq(false, comments),
				token::OpTy::NotEq => OpTy::NotEq(false, comments),
				token::OpTy::AndAnd => OpTy::AndAnd(false, comments),
				token::OpTy::OrOr => OpTy::OrOr(false, comments),
				token::OpTy::XorXor => OpTy::XorXor(false, comments),
				token::OpTy::Gt => OpTy::Gt(false, comments),
				token::OpTy::Lt => OpTy::Lt(false, comments),
				token::OpTy::Ge => OpTy::Ge(false, comments),
				token::OpTy::Le => OpTy::Le(false, comments),
				token::OpTy::Not
				| token::OpTy::Flip
				| token::OpTy::AddAdd
				| token::OpTy::SubSub => {
					// These tokens are handled by individual branches in the main parser loop.
					unreachable!("[Op::from_token] Given a `token` which should never be handled by this function.")
				}
			},
		}
	}

	/// Returns the precedence of this operator.
	#[rustfmt::skip]
	fn precedence(&self) -> usize {
		match &self.ty {
			OpTy::ObjAccess(_, _) => 33,
			OpTy::AddPost(_) | OpTy::SubPost(_) => 31,
			OpTy::AddPre(_, _)
			| OpTy::SubPre(_, _)
			| OpTy::Neg(_, _)
			| OpTy::Flip(_, _)
			| OpTy::Not(_, _) => 29,
			OpTy::Mul(_, _) | OpTy::Div(_, _) | OpTy::Rem(_, _) => 27,
			OpTy::Add(_, _) | OpTy::Sub(_, _) => 25,
			OpTy::LShift(_, _) | OpTy::RShift(_, _) => 23,
			OpTy::Lt(_, _) | OpTy::Gt(_, _) | OpTy::Le(_, _) | OpTy::Ge(_, _) => 21,
			OpTy::EqEq(_, _) | OpTy::NotEq(_, _) => 19,
			OpTy::And(_, _) => 17,
			OpTy::Xor(_, _) => 15,
			OpTy::Or(_, _) => 13,
			OpTy::AndAnd(_, _) => 11,
			OpTy::XorXor(_, _) => 9,
			OpTy::OrOr(_, _) => 7,
			OpTy::TernaryQ(_, _) => 5,
			OpTy::TernaryC(_, _) => 3,
			OpTy::Eq(_, _)
			| OpTy::AddEq(_, _)
			| OpTy::SubEq(_, _)
			| OpTy::MulEq(_, _)
			| OpTy::DivEq(_, _)
			| OpTy::RemEq(_, _)
			| OpTy::AndEq(_, _)
			| OpTy::XorEq(_, _)
			| OpTy::OrEq(_, _)
			| OpTy::LShiftEq(_, _)
			| OpTy::RShiftEq(_, _) => 1,
			// These are never directly checked for precedence, but rather have special branches.
			_ => panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
		}
	}

	fn to_bin_op(self) -> (BinOp, Comments) {
		let (ty, comments) = match self.ty {
				OpTy::Add(_, comments) => (BinOpTy::Add, comments),
				OpTy::Sub(_, comments) => (BinOpTy::Sub, comments),
				OpTy::Mul(_, comments) => (BinOpTy::Mul, comments),
				OpTy::Div(_, comments) => (BinOpTy::Div, comments),
				OpTy::Rem(_, comments) => (BinOpTy::Rem, comments),
				OpTy::And(_, comments) => (BinOpTy::And, comments),
				OpTy::Or(_, comments) => (BinOpTy::Or, comments),
				OpTy::Xor(_, comments) => (BinOpTy::Xor, comments),
				OpTy::LShift(_, comments) => (BinOpTy::LShift, comments),
				OpTy::RShift(_, comments) => (BinOpTy::RShift, comments),
				OpTy::Eq(_, comments) => (BinOpTy::Eq, comments),
				OpTy::AddEq(_, comments) => (BinOpTy::AddEq, comments),
				OpTy::SubEq(_, comments) => (BinOpTy::SubEq, comments),
				OpTy::MulEq(_, comments) => (BinOpTy::MulEq, comments),
				OpTy::DivEq(_, comments) => (BinOpTy::DivEq, comments),
				OpTy::RemEq(_, comments) => (BinOpTy::RemEq, comments),
				OpTy::AndEq(_, comments) => (BinOpTy::AndEq, comments),
				OpTy::OrEq(_, comments) => (BinOpTy::OrEq, comments),
				OpTy::XorEq(_, comments) => (BinOpTy::XorEq, comments),
				OpTy::LShiftEq(_, comments) => (BinOpTy::LShiftEq, comments),
				OpTy::RShiftEq(_, comments) => (BinOpTy::RShiftEq, comments),
				OpTy::EqEq(_, comments) => (BinOpTy::EqEq, comments),
				OpTy::NotEq(_, comments) => (BinOpTy::NotEq, comments),
				OpTy::AndAnd(_, comments) => (BinOpTy::AndAnd, comments),
				OpTy::OrOr(_, comments) => (BinOpTy::OrOr, comments),
				OpTy::XorXor(_, comments) => (BinOpTy::XorXor, comments),
				OpTy::Gt(_, comments) => (BinOpTy::Gt, comments),
				OpTy::Lt(_, comments) => (BinOpTy::Lt, comments),
				OpTy::Ge(_, comments) => (BinOpTy::Ge, comments),
				OpTy::Le(_, comments) => (BinOpTy::Le, comments),
				_ => unreachable!("[Op::to_bin_op] Given a `ty` which should not be handled here.")
			};

		(
			BinOp {
				span: self.span,
				ty,
			},
			comments,
		)
	}
}

/// An open grouping of items.
#[derive(Debug, PartialEq)]
enum Group {
	/// A parenthesis group.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis,
	/// - `1` - The span of the opening parenthesis.
	Paren(bool, Span),
	/// A function call.
	///
	/// - `0` - The number of expressions to consume for the arguments,
	/// - `1` - The span of the opening parenthesis.
	FnCall(usize, Span),
	/// An index operator.
	///
	/// - `0` - Whether this group has an inner expression within the brackets.
	/// - `1` - The span of the opening bracket.
	Index(bool, Span),
	/// An initializer list.
	///
	/// - `0` - The number of expressions to consume for the arguments,
	/// - `1` - The span of the opening brace.
	Init(usize, Span),
	/// An array constructor.
	///
	/// - `0` - The number of expressions to consume for the arguments,
	/// - `1` - The span of the opening parenthesis.
	ArrInit(usize, Span),
	/// A general list **outside** of function calls, initializer lists and array constructors.
	///
	/// - `0` - The number of expressions to consume for the arguments,
	/// - `1` - The starting position of this list.
	///
	/// # Invariants
	/// This group only exists if the outer `Group` is not of type `Group::FnCall|Init|ArrInit|List`. (You can't
	/// have a list within a list since there are no delimiters, and commas within the other groups won't create an
	/// inner list but rather increase the arity).
	List(usize, usize),
	/// A ternary expression.
	Ternary,
}

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Node, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The top-most entry is the group being currently parsed.
	groups: VecDeque<Group>,
	comments: Vec<(Comment, Span)>,
	/// The start position of the first item in this expression.
	start_position: usize,
	/// The behavioural mode of the parser.
	mode: Mode,
	/// Syntax errors encountered during the parser execution.
	errors: Vec<SyntaxErr>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Op) {
		if let OpTy::TernaryC(_, _) = op.ty {
			// This completes the ternary.
			match self.groups.pop_back() {
				Some(group) => match group {
					Group::Ternary => {}
					_ => panic!("Should be in ternary group"),
				},
				None => panic!("Should be in ternary group"),
			};
		}

		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			match back.ty {
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				OpTy::ParenStart(_)
				| OpTy::IndexStart(_)
				| OpTy::FnCallStart(_)
				| OpTy::InitStart(_)
				| OpTy::ArrInitStart(_) => break,
				_ => {}
			}

			match (&op.ty, &back.ty) {
				// This is done to make `ObjAccess` right-associative.
				(OpTy::ObjAccess(_, _), OpTy::ObjAccess(_, _)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					break;
				}
				// These are done to make the ternary operator right-associate correctly. This is slightly more
				// complex since the ternary is made of two distinct "operators", the `?` and `:`.
				(OpTy::TernaryC(_, _), OpTy::TernaryQ(_, _)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					break;
				}
				(OpTy::TernaryC(_, _), OpTy::TernaryC(_, _)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					continue;
				}
				(_, _) => {}
			}

			if op.precedence() < back.precedence() {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
			} else {
				// If the precedence is greater, we aren't going to be moving any operators to the stack anymore,
				// so we can exit the loop.
				break;
			}
		}
		self.operators.push_back(op);
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::Paren`].
	///
	/// `end_span` is the span which marks the end of this parenthesis group. It may be the span of the `)` token,
	/// or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_bracket(
		&mut self,
		group: Group,
		end_span: Span,
		end_comments: Comments,
	) {
		if let Group::Paren(has_inner, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnCallStart(_) => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Paren)!"),
						OpTy::IndexStart(_) => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Paren)!"),
						OpTy::InitStart(_) => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Paren)!"),
						OpTy::ArrInitStart(_) => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Paren)!"),
						_ => {}
					}
				}

				if let OpTy::ParenStart(l_comments) = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::Paren(
							has_inner,
							l_paren,
							end_span,
							l_comments,
							end_comments,
						),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::Fn`].
	///
	/// `end_span` is the span which marks the end of this function call group. It may be the span of the `)` token,
	/// or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_fn(
		&mut self,
		group: Group,
		end_span: Span,
		end_comments: Comments,
	) {
		if let Group::FnCall(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart(_) => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Fn)!"),
						OpTy::IndexStart(_) => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Fn)!"),
						OpTy::InitStart(_) => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Fn)!"),
						OpTy::ArrInitStart(_) => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Fn)!"),
						_ => {}
					}
				}

				if let OpTy::FnCallStart(l_comments) = op.ty {
					// The first expression will always be the `Expr::Ident` containing the function identifier,
					// hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::FnCall(
							count + 1,
							l_paren,
							end_span,
							l_comments,
							end_comments,
						),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::Index`].
	///
	/// `end_span` is the span which marks the end of this index group. It may be a span of the `]` token, or it
	/// may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_index(
		&mut self,
		group: Group,
		end_span: Span,
		end_comments: Comments,
	) {
		if let Group::Index(contains_i, l_bracket) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op .ty{
						OpTy::ParenStart(_) => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Index)!"),
						OpTy::FnCallStart(_) => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Index)!"),
						OpTy::InitStart(_) => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Index)!"),
						OpTy::ArrInitStart(_) => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Index)!"),
						_ => {}
					}
				}

				if let OpTy::IndexStart(l_comments) = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_bracket.start, end_span.end),
						ty: OpTy::Index(
							contains_i,
							l_bracket,
							end_span,
							l_comments,
							end_comments,
						),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::Init`].
	///
	/// `end_span` is the span which marks the end of this initializer list group. It may be a span of the `}`
	/// token, or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_init(
		&mut self,
		group: Group,
		end_span: Span,
		end_comments: Comments,
	) {
		if let Group::Init(count, l_brace) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart(_) => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Init)!"),
						OpTy::IndexStart(_) => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Init)!"),
						OpTy::FnCallStart(_) => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Init)!"),
						OpTy::ArrInitStart(_) => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Init)!"),
						_ => {}
					}
				}

				if let OpTy::InitStart(l_comments) = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_brace.start, end_span.end),
						ty: OpTy::Init(
							count,
							l_brace,
							end_span,
							l_comments,
							end_comments,
						),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::ArrInit`].
	///
	/// `end_span` is the span which marks the end of this array constructor group. It may be a span of the `)`
	/// token, or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_arr_init(
		&mut self,
		group: Group,
		end_span: Span,
		end_comments: Comments,
	) {
		if let Group::ArrInit(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart(_) => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::ArrInit)!"),
						OpTy::IndexStart(_) => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::ArrInit)!"),
						OpTy::FnCallStart(_) => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::ArrInit)!"),
						OpTy::InitStart(_) => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::ArrInit)!"),
						_ => {}
					}
				}

				if let OpTy::ArrInitStart(l_comments) = op.ty {
					// The first expression will always be the `Expr::Index` containing the identifier/item and the
					// array index, hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::ArrInit(
							count + 1,
							l_paren,
							end_span,
							l_comments,
							end_comments,
						),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `group` is of type [`Group::List`].
	///
	/// `span_end` is the position which marks the end of this list group.
	fn collapse_list(&mut self, group: Group, span_end: usize) {
		if let Group::List(count, start_pos) = group {
			while self.operators.back().is_some() {
				let op = self.operators.back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnCallStart(_) => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::List)!"),
						OpTy::InitStart(_) => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::List)!"),
						OpTy::ArrInitStart(_) => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::List)!"),
						_ => {}
					}
				}

				// Lists don't have a starting delimiter, so we consume until we encounter another group-start
				// delimiter (and if there are none, we just end up consuming the rest of the operator stack).
				// Since lists cannnot exist within a `Group::FnCall|Init|ArrInit`, we don't check for those start
				// delimiters.
				match op.ty {
					OpTy::ParenStart(_) | OpTy::IndexStart(_) => break,
					_ => {
						// Any other operators get moved, since we are moving everything until we hit the start
						// delimiter.
						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
				}
			}
			self.stack.push_back(Either::Right(Op {
				span: Span::new(start_pos, span_end),
				ty: OpTy::List(count),
			}));
		} else {
			unreachable!()
		}
	}

	/// Registers the end of a bracket, function call or array constructor group, popping any operators until the
	/// start of the group is reached.
	fn end_bracket_fn(
		&mut self,
		end_span: Span,
		r_comments: Comments,
	) -> Result<(), ()> {
		let current_group = match self.groups.back() {
			Some(t) => t,
			None => {
				// Since we have no groups, that means we have a lonely `)`. This means we want to stop parsing
				// further tokens.
				return Err(());
			}
		};

		match current_group {
			Group::Paren(_, _) => {}
			Group::FnCall(_, _) | Group::ArrInit(_, _) => {}
			_ => {
				// The current group is not a bracket/function/array constructor group, so we need to check whether
				// there is one at all.

				if self.exists_paren_fn_group() {
					// We have at least one other group to close before we can close the bracket/function/array
					// constructor group.
					'inner: while let Some(current_group) = self.groups.back() {
						match current_group {
							Group::Init(_, _) => {
								log!("Unclosed `}}` initializer list found!");
								let current_group =
									self.groups.pop_back().unwrap();
								self.collapse_init(
									current_group,
									span(
										end_span.end_at_previous().end,
										end_span.end_at_previous().end,
									),
									vec![],
								);
							}
							Group::Index(_, _) => {
								log!("Unclosed `]` index operator found!");
								let current_group =
									self.groups.pop_back().unwrap();
								self.collapse_index(
									current_group,
									end_span.start_zero_width(),
									vec![],
								)
							}
							Group::List(_, _) => {
								let current_group =
									self.groups.pop_back().unwrap();

								self.collapse_list(
									current_group,
									end_span.end_at_previous().end,
								);
							}
							Group::Ternary => {
								'tern: while let Some(op) =
									self.operators.back()
								{
									if let OpTy::TernaryQ(_, _) = op.ty {
										let moved =
											self.operators.pop_back().unwrap();
										self.stack
											.push_back(Either::Right(moved));
										break 'tern;
									} else {
										let moved =
											self.operators.pop_back().unwrap();
										self.stack
											.push_back(Either::Right(moved));
									}
								}

								self.groups.pop_back();
							}
							Group::Paren(_, _)
							| Group::FnCall(_, _)
							| Group::ArrInit(_, _) => break 'inner,
						}
					}
				} else {
					// Since we don't have a parenthesis/function/array constructor group at all, that means we
					// have a lonely `)`. This means we want to stop parsing further tokens.
					return Err(());
				}
			}
		}

		let group = self.groups.pop_back().unwrap();
		match group {
			Group::Paren(_, _) => {
				self.collapse_bracket(group, end_span, r_comments)
			}
			Group::FnCall(_, _) => {
				self.collapse_fn(group, end_span, r_comments)
			}
			Group::ArrInit(_, _) => {
				self.collapse_arr_init(group, end_span, r_comments)
			}
			// Either the inner-most group is already a parenthesis-delimited group, or we've closed all inner
			// groups and are now at a parenthesis-delimited group, hence this branch will never occur.
			_ => unreachable!(),
		}
		Ok(())
	}

	/// Registers the end of an index operator group, popping any operators until the start of the index group is
	/// reached.
	///
	/// `end_span` is a span which ends at the end of this index operator. (The start value is irrelevant).
	fn end_index(
		&mut self,
		end_span: Span,
		r_comments: Comments,
	) -> Result<(), ()> {
		let current_group = match self.groups.back() {
			Some(t) => t,
			None => {
				// Since we have no groups, that means we have a lonely `]`. This means we want to stop parsing
				// further tokens.
				return Err(());
			}
		};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Index(
				false,
				Span::new_zero_width(0),
			)) {
			// The current group is not an index group, so we need to check whether there is one at all.

			if self.exists_index_group() {
				// We have at least one other group to close before we can close the index group.
				'inner: while let Some(current_group) = self.groups.back() {
					match current_group {
						Group::Paren(_, _) => {
							log!("Unclosed `)` parenthesis found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_bracket(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::FnCall(_, _) => {
							log!("Unclosed `)` function call found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_fn(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::Init(_, _) => {
							log!("Unclosed `}}` initializer list found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_init(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::ArrInit(_, _) => {
							log!("Unclosed `)` array constructor found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_arr_init(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::Ternary => {
							'tern: while let Some(op) = self.operators.back() {
								if let OpTy::TernaryQ(_, _) = op.ty {
									let moved =
										self.operators.pop_back().unwrap();
									self.stack.push_back(Either::Right(moved));
									break 'tern;
								} else {
									let moved =
										self.operators.pop_back().unwrap();
									self.stack.push_back(Either::Right(moved));
								}
							}

							self.groups.pop_back();
						}
						Group::List(_, _) => {
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_list(
								current_group,
								end_span.end_at_previous().end,
							)
						}
						Group::Index(_, _) => break 'inner,
					}
				}
			} else {
				// Since we don't have an index group at all, that means we have a lonely `]`. This means we want
				// to stop parsing further tokens.
				return Err(());
			}
		}

		let group = self.groups.pop_back().unwrap();
		self.collapse_index(group, end_span, r_comments);
		Ok(())
	}

	/// Registers the end of an initializer list group, popping any operators until the start of the group is
	/// reached.
	fn end_init(
		&mut self,
		end_span: Span,
		r_comments: Comments,
	) -> Result<(), ()> {
		let current_group = match self.groups.back() {
			Some(t) => t,
			None => {
				// Since we have no groups, that means we have a lonely `}`. This means we want to stop parsing
				// further tokens.
				return Err(());
			}
		};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Init(0, Span::new_zero_width(0)))
		{
			// The current group is not an initializer group, so we need to check whether there is one at all.

			if self.exists_init_group() {
				// We have at least one other group to close before we can close the initializer group.
				'inner: while let Some(current_group) = self.groups.back() {
					match current_group {
						Group::Paren(_, _) => {
							log!("Unclosed `)` parenthesis found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_bracket(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::Index(_, _) => {
							log!("Unclosed `]` index operator found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_index(
								current_group,
								end_span.start_zero_width(),
								vec![],
							);
						}
						Group::FnCall(_, _) => {
							log!("Unclosed `)` function call found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_fn(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::ArrInit(_, _) => {
							log!("Unclosed `)` array constructor found!");
							let current_group = self.groups.pop_back().unwrap();
							self.collapse_arr_init(
								current_group,
								span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
								vec![],
							);
						}
						Group::Ternary => {
							'tern: while let Some(op) = self.operators.back() {
								if let OpTy::TernaryQ(_, _) = op.ty {
									let moved =
										self.operators.pop_back().unwrap();
									self.stack.push_back(Either::Right(moved));
									break 'tern;
								} else {
									let moved =
										self.operators.pop_back().unwrap();
									self.stack.push_back(Either::Right(moved));
								}
							}

							self.groups.pop_back();
						}
						// See `List` documentation.
						Group::List(_, _) => unreachable!(),
						Group::Init(_, _) => break 'inner,
					}
				}
			} else {
				// Since we don't have an initializer group at all, that means we have a lonely `}`. This means we
				// want to stop parsing further tokens.
				return Err(());
			}
		}

		let group = self.groups.pop_back().unwrap();
		self.collapse_init(group, end_span, r_comments);
		Ok(())
	}

	/// Registers the end of a sub-expression, popping any operators until the start of the group (or expression)
	/// is reached.
	fn register_arity_argument(&mut self, end_span: Span) {
		while let Some(group) = self.groups.back_mut() {
			match group {
				Group::FnCall(count, _)
				| Group::Init(count, _)
				| Group::ArrInit(count, _) => {
					// We want to move all existing operators up to the function call, initializer list, or array
					// constructor start delimiter to the stack, to clear it for the next expression.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						match back.ty {
							OpTy::FnCallStart(_)
							| OpTy::InitStart(_)
							| OpTy::ArrInitStart(_) => break,
							_ => {}
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}

					*count += 1;
					return;
				}
				Group::List(count, _) => {
					while self.operators.back().is_some() {
						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}

					*count += 1;
					return;
				}
				// We collapse the entire group since commas aren't allowed within parenthesis or index
				// operators. We continue looping until we either come across a delimited arity group, such as
				// a function call, or if have no such group we create a top-level list group.
				// We want to move all existing operators up to the function call, initializer list, or array
				// constructor start delimiter to the stack, to clear it for the next expression.
				Group::Paren(_, _) => {
					let group = self.groups.pop_back().unwrap();
					self.collapse_bracket(group, end_span, vec![]);
				}
				Group::Index(_, _) => {
					let group = self.groups.pop_back().unwrap();
					self.collapse_index(group, end_span, vec![]);
				}
				Group::Ternary => {
					'tern: while let Some(op) = self.operators.back() {
						if let OpTy::TernaryQ(_, _) = op.ty {
							let moved = self.operators.pop_back().unwrap();
							self.stack.push_back(Either::Right(moved));
							break 'tern;
						} else {
							let moved = self.operators.pop_back().unwrap();
							self.stack.push_back(Either::Right(moved));
						}
					}

					self.groups.pop_back();
				}
			}
		}

		// Since we are outside of any group, we can just push all the operators to the stack to clear it for
		// the next expression. We also push a new list group. Since list groups don't have a start delimiter,
		// we can only do it now that we've encountered a comma in an otherwise ungrouped expression.
		while self.operators.back().is_some() {
			let moved = self.operators.pop_back().unwrap();
			self.stack.push_back(Either::Right(moved));
		}
		self.groups.push_back(Group::List(
			if self.stack.is_empty() && self.operators.is_empty() {
				0
			} else {
				1
			},
			self.start_position,
		))
	}

	/// Increases the arity of the current function.
	fn increase_arity(&mut self) {
		if let Some(current_group) = self.groups.back_mut() {
			match current_group {
				Group::Paren(has_inner, _) => {
					debug_assert!(!*has_inner, "[ShuntingYard::increase_arity] Increasing the arity on a `Group::Paren` which is already at `1`.");
					*has_inner = true;
				}
				Group::FnCall(count, _)
				| Group::Init(count, _)
				| Group::ArrInit(count, _)
				| Group::List(count, _) => {
					*count += 1;
				}
				_ => {}
			}
		}
		// TODO: Should this be unreachable?
		log!("Found an incomplete function call, initializer list, array constructor or general list expression!");
	}

	/// Sets the toggle on the last operator that it has a right-hand side operand (if applicable).
	fn set_op_rhs_toggle(&mut self) {
		if let Some(op) = self.operators.back_mut() {
			match &mut op.ty {
				OpTy::Add(b, _)
				| OpTy::Sub(b, _)
				| OpTy::Mul(b, _)
				| OpTy::Div(b, _)
				| OpTy::Rem(b, _)
				| OpTy::And(b, _)
				| OpTy::Or(b, _)
				| OpTy::Xor(b, _)
				| OpTy::LShift(b, _)
				| OpTy::RShift(b, _)
				| OpTy::Eq(b, _)
				| OpTy::AddEq(b, _)
				| OpTy::SubEq(b, _)
				| OpTy::MulEq(b, _)
				| OpTy::DivEq(b, _)
				| OpTy::RemEq(b, _)
				| OpTy::AndEq(b, _)
				| OpTy::OrEq(b, _)
				| OpTy::XorEq(b, _)
				| OpTy::LShiftEq(b, _)
				| OpTy::RShiftEq(b, _)
				| OpTy::EqEq(b, _)
				| OpTy::NotEq(b, _)
				| OpTy::AndAnd(b, _)
				| OpTy::OrOr(b, _)
				| OpTy::XorXor(b, _)
				| OpTy::Gt(b, _)
				| OpTy::Lt(b, _)
				| OpTy::Ge(b, _)
				| OpTy::Le(b, _)
				| OpTy::AddPre(b, _)
				| OpTy::SubPre(b, _)
				| OpTy::Neg(b, _)
				| OpTy::Flip(b, _)
				| OpTy::Not(b, _)
				| OpTy::TernaryQ(b, _)
				| OpTy::TernaryC(b, _)
				| OpTy::ObjAccess(b, _) => *b = true,
				_ => {}
			}
		}
		if let Some(group) = self.groups.back_mut() {
			match group {
				Group::Paren(b, _) | Group::Index(b, _) => *b = true,
				_ => {}
			}
		}
	}

	/// Returns whether we have just started to parse a function, i.e. `..fn(<HERE>`
	fn just_started_fn_arr_init(&self) -> bool {
		let stack_span = self.stack.back().map(|i| match i {
			Either::Left(e) => e.span,
			Either::Right(op) => op.span,
		});
		let op_span = match self.operators.back() {
			Some(op) => match op.ty {
				OpTy::FnCallStart(_) | OpTy::ArrInitStart(_) => op.span,
				_ => return false,
			},
			None => return false,
		};

		match (stack_span, op_span) {
			(Some(stack), op_span) => op_span.is_after(&stack),
			(None, _op_span) => true,
		}
	}

	/// Returns whether we have just started to parse an initializer list, i.e. `..{<HERE>`
	fn just_started_init(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::Init(count, _) => *count == 0,
				_ => false,
			}
		} else {
			false
		}
	}

	fn just_started_paren(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::Paren(has_inner, _) => *has_inner == false,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we are currently in an initializer list parsing group, i.e. `{..<HERE>`
	fn is_in_init(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::Init(_, _) => true,
				_ => false,
			}
		} else {
			false
		}
	}

	fn is_in_ternary(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::Ternary => true,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we are currently in a function call, initializer list or array constructor group.
	fn is_in_variable_arg_group(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::FnCall(_, _)
				| Group::Init(_, _)
				| Group::ArrInit(_, _)
				| Group::List(_, _) => true,
				Group::Ternary => {
					for group in self.groups.iter().rev() {
						match group {
							Group::FnCall(_, _)
							| Group::Init(_, _)
							| Group::ArrInit(_, _)
							| Group::List(_, _) => return true,
							_ => {}
						}
					}
					false
				}
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether an open parenthesis, function call or array constructor group exists.
	fn exists_paren_fn_group(&self) -> bool {
		for group in self.groups.iter() {
			match group {
				Group::Paren(_, _)
				| Group::FnCall(_, _)
				| Group::ArrInit(_, _) => return true,
				_ => {}
			}
		}
		false
	}

	/// Returns whether an open index operator group exists.
	fn exists_index_group(&self) -> bool {
		for group in self.groups.iter() {
			if let Group::Index(_, _) = group {
				return true;
			}
		}
		false
	}

	/// Returns whether an open initializer list group exists.
	fn exists_init_group(&self) -> bool {
		for group in self.groups.iter() {
			if let Group::Init(_, _) = group {
				return true;
			}
		}
		false
	}

	/// Returns the [`Span`] of the last item on the stack or operator stack.
	fn get_previous_span(&self) -> Option<Span> {
		let stack_span = self.stack.back().map(|i| match i {
			Either::Left(e) => e.span,
			Either::Right(op) => op.span,
		});
		let op_span = self.operators.back().map(|op| op.span);

		match (stack_span, op_span) {
			(Some(stack), Some(op)) => {
				if stack.is_after(&op) {
					stack_span
				} else {
					op_span
				}
			}
			(Some(_), None) => stack_span,
			(None, Some(_)) => op_span,
			(None, None) => None,
		}
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse(&mut self, walker: &mut Walker, end_tokens: &[Token]) {
		#[derive(PartialEq)]
		enum State {
			/// We are looking for either a) a prefix operator, b) an atom, c) bracket group start, d) function
			/// call group start, e) initializer list group start.
			Operand,
			/// We are looking for either a) a postfix operator, b) an index operator start or end, c) a binary
			/// operator, d) bracket group end, e) function call group end, f) initializer list group end, g) a
			/// comma, h) end of expression.
			AfterOperand,
		}
		let mut state = State::Operand;

		#[derive(PartialEq)]
		enum Start {
			/// Nothing.
			None,
			/// We have found an `ident`; we can start a function call assuming we find `(` next. If we encounter a
			/// `[` next, we want to store the `possible_delim_start` value with the `Index` group, in case we have
			/// an array constructor after the index.
			FnOrArr,
			/// We have found an `Expr::Index`; we can start an array constructor assuming we find `(` next.
			ArrInit,
			/// We have found a `[`. If the next token is a `]` we have an empty index operator.
			EmptyIndex,
		}
		let mut can_start = Start::None;

		#[derive(PartialEq)]
		enum Arity {
			/// On the first iteration of the parsing loop.
			None,
			/// Signifies that the previous token can end an argument in an arity group, for example:
			/// ```text
			/// fn( 1+1, 5
			///        ^ signifies the end
			/// ```
			/// Or when dealing with error recovery of missing commas:
			/// ```text
			/// { 1+1 5
			///     ^ signifies the end, (missing comma afterwards though)
			/// ```
			PotentialEnd,
			/// Signifies that the previous token cannot end an argument in an arity group, for example:
			/// ```text
			/// fn( 1 + 6
			///       ^ expects a rhs,
			///           so the 6 is treated as part of the same argument
			/// ```
			/// The only exception is if the current token is a comma (`,`), in which case it always ends the
			/// argument in an arity group.
			Operator,
		}
		// The state of arity manipulation set in the previous iteration of the loop.
		let mut arity_state = Arity::None;

		// Whether we have just started an arity group. This is set to `true` right after we have an opening
		// delimiter to an arity group, such as `(` or `{`. This is also set to `true` at the beginning here, in
		// order to correctly handle the case where we encounter a comma `,` as the first token in this expression.
		let mut just_started_arity_group = true;

		'main: while !walker.is_done() {
			let (token, span) = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break 'main,
			};

			// If the current token is one which signifies the end of the current expression, we stop parsing.
			if end_tokens.contains(token) {
				// We may be given a `)` token to break parsing at, but take this example: `while ((true))`.
				// As part of the while statement parser, we've already consumed the first `(`. We then start
				// the rest in here, and we start a parenthesis group with the `true` token within it. But then we
				// encounter the first `)` and immediately break, leaving an incomplete expression and syntax
				// errors where they shouldn't be.
				//
				// So instead, we only break if we encounter these closing delimiter tokens assuming we don't have
				// the relevant group open.
				if *token == Token::RParen && self.exists_paren_fn_group() {
				} else if *token == Token::RBracket && self.exists_index_group()
				{
				} else if *token == Token::RBrace && self.exists_init_group() {
				} else {
					break 'main;
				}
			}

			match token {
				Token::LineComment(str) => {
					self.comments.push((Comment::Line(str.clone()), *span));
				}
				Token::BlockComment {
					str,
					contains_eof: _,
				} => self.comments.push((Comment::Block(str.clone()), *span)),
				Token::Num { .. } | Token::Bool(_)
					if state == State::Operand =>
				{
					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `fn(10, 5` or `fn(10 5` or `{1+1  100`
					// but not:
					// `10 5` or `fn(10 + 5`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(match Lit::parse(token) {
						Ok(l) => Either::Left(Node {
							ty: NodeTy::Lit(
								l,
								std::mem::take(&mut self.comments),
							),
							span: *span,
						}),
						Err(_) => Either::Left(Node {
							ty: NodeTy::Invalid(std::mem::take(
								&mut self.comments,
							)),
							span: *span,
						}),
					});

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					state = State::AfterOperand;

					can_start = Start::None;

					self.set_op_rhs_toggle();
				}
				Token::Num { .. } | Token::Bool(_)
					if state == State::AfterOperand =>
				{
					if self.mode == Mode::TakeOneUnit {
						break 'main;
					}

					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `fn(10, 5` or `fn(10 5` or `{1+1  100`
					// but not:
					// `a b` or `fn(10 + 5`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					} else {
						// We are not in a delimited arity group. We don't perform error recovery because in this
						// situation it's not as obvious what the behaviour should be, so we avoid any surprises.
						self.errors.push(
							SyntaxErr::ExprFoundOperandAfterOperand(
								self.get_previous_span().unwrap(),
								*span,
							),
						);
						break 'main;
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(match Lit::parse(token) {
						Ok(l) => Either::Left(Node {
							ty: NodeTy::Lit(
								l,
								std::mem::take(&mut self.comments),
							),
							span: *span,
						}),
						Err(_) => Either::Left(Node {
							ty: NodeTy::Invalid(std::mem::take(
								&mut self.comments,
							)),
							span: *span,
						}),
					});

					can_start = Start::None;

					// We don't change state since even though we found an operand instead of an operator, after
					// this operand we will still be expecting an operator.
				}
				Token::Ident(s) if state == State::Operand => {
					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `fn(10, i` or `fn(10 i` or `{1+1  i`
					// but not:
					// `a i` or `fn(10 + i`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Ident(
							Ident {
								name: s.clone(),
								span: *span,
							},
							std::mem::take(&mut self.comments),
						),
						span: *span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + i` instead of `..10 i`.
					state = State::AfterOperand;

					// After an identifier, we may start a function call, or eventually an array constructor.
					can_start = Start::FnOrArr;

					self.set_op_rhs_toggle();
				}
				Token::Ident(s) if state == State::AfterOperand => {
					if self.mode == Mode::TakeOneUnit {
						break 'main;
					}

					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `fn(10, 5` or `fn(10 5` or `{1+1  100`
					// but not:
					// `a b` or `fn(10 + 5`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					} else {
						// We are not in a delimited arity group. We don't perform error recovery because in this
						// situation it's not as obvious what the behaviour should be, so we avoid any surprises.
						self.errors.push(
							SyntaxErr::ExprFoundOperandAfterOperand(
								self.get_previous_span().unwrap(),
								*span,
							),
						);
						break 'main;
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Ident(
							Ident {
								name: s.clone(),
								span: *span,
							},
							std::mem::take(&mut self.comments),
						),
						span: *span,
					}));

					// After an identifier, we may start a function call.
					can_start = Start::FnOrArr;

					// We don't change state since even though we found an operand instead of an operator, after
					// this operand we will still be expecting an operator.
				}
				Token::Op(op) if state == State::Operand => {
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == token::OpTy::Eq
					{
						break 'main;
					}

					match op {
						token::OpTy::Sub
						| token::OpTy::Not
						| token::OpTy::Flip
						| token::OpTy::AddAdd
						| token::OpTy::SubSub => {
							// If we previously had a token which can end an argument of an arity group, and we are
							// in a delimited arity group, we want to increase the arity, for example:
							// `fn(10, !true` or `fn(10 !true` or `{1+1  !true`
							// but not:
							// `a !true` or `fn(10 + !true`
							if self.is_in_variable_arg_group()
								&& arity_state == Arity::PotentialEnd
							{
								self.register_arity_argument(
									span.start_zero_width(),
								);
								arity_state = Arity::Operator;
							}

							self.set_op_rhs_toggle();
						}
						_ => {
							self.errors.push(
								SyntaxErr::ExprInvalidPrefixOperator(*span),
							);
							break 'main;
						}
					}

					let comments = std::mem::take(&mut self.comments);
					match op {
						// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
						// state since after a prefix operator, we are still looking for an operand atom.
						token::OpTy::Sub => self.push_operator(Op {
							span: *span,
							ty: OpTy::Neg(false, comments),
						}),
						token::OpTy::Not => self.push_operator(Op {
							span: *span,
							ty: OpTy::Not(false, comments),
						}),
						token::OpTy::Flip => self.push_operator(Op {
							span: *span,
							ty: OpTy::Flip(false, comments),
						}),
						token::OpTy::AddAdd => self.push_operator(Op {
							span: *span,
							ty: OpTy::AddPre(false, comments),
						}),
						token::OpTy::SubSub => self.push_operator(Op {
							span: *span,
							ty: OpTy::SubPre(false, comments),
						}),
						_ => {
							unreachable!()
						}
					}

					can_start = Start::None;
				}
				Token::Op(op) if state == State::AfterOperand => {
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == token::OpTy::Eq
					{
						break 'main;
					}

					match op {
						token::OpTy::Flip | token::OpTy::Not => {
							self.errors.push(
								SyntaxErr::ExprInvalidBinOrPostOperator(*span),
							);
							break 'main;
						}
						// These operators are postfix operators. We don't switch state since after a postfix
						// operator, we are still looking for a binary operator or the end of expression, i.e.
						// `..i++ - i` rather than `..i++ i`.
						token::OpTy::AddAdd => {
							let comments = std::mem::take(&mut self.comments);
							self.push_operator(Op {
								span: *span,
								ty: OpTy::AddPost(comments),
							});
						}
						token::OpTy::SubSub => {
							let comments = std::mem::take(&mut self.comments);
							self.push_operator(Op {
								span: *span,
								ty: OpTy::SubPost(comments),
							});
						}
						// Any other operators can be part of a binary expression. We switch state since after a
						// binary operator we are expecting an operand.
						_ => {
							let comments = std::mem::take(&mut self.comments);
							self.push_operator(Op::from_token(
								*op, *span, comments,
							));
							state = State::Operand;
						}
					}

					arity_state = Arity::Operator;

					can_start = Start::None;
				}
				Token::LParen if state == State::Operand => {
					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `fn(10, (` or `fn(10 (` or `{1+1  (`
					// but not:
					// `a (` or `fn(10 + (`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::Operator;

					self.set_op_rhs_toggle();

					let comments = std::mem::take(&mut self.comments);
					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::ParenStart(comments),
					});
					self.groups.push_back(Group::Paren(false, *span));

					can_start = Start::None;

					// We don't switch state since after a `(`, we are expecting an operand, i.e.
					// `..+ ( 1 *` rather than `..+ ( *`.
				}
				Token::LParen if state == State::AfterOperand => {
					if can_start == Start::FnOrArr {
						// We have `ident(` which makes this a function call.
						let comments = std::mem::take(&mut self.comments);
						self.operators.push_back(Op {
							span: *span,
							ty: OpTy::FnCallStart(comments),
						});
						self.groups.push_back(Group::FnCall(0, *span));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `fn( 1..` rather than`fn( +..`.1
						state = State::Operand;

						// We unset this flag, since this flag is only used to detect the `ident` -> `(` token
						// chain.
						can_start = Start::None;

						just_started_arity_group = true;
					} else if can_start == Start::ArrInit {
						// We have `ident[...](` which makes this an array constructor.
						let comments = std::mem::take(&mut self.comments);
						self.operators.push_back(Op {
							span: *span,
							ty: OpTy::ArrInitStart(comments),
						});
						self.groups.push_back(Group::ArrInit(0, *span));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `int[]( 1,..` rather than`int[]( +1,..`.
						state = State::Operand;

						// We unset this flag, since this flag is only used to detect the `..]` -> `(` token chain.
						can_start = Start::None;

						just_started_arity_group = true;
					} else {
						// We have something like `..5 (`.
						if self.is_in_variable_arg_group()
							&& arity_state == Arity::PotentialEnd
						{
							self.register_arity_argument(
								span.start_zero_width(),
							);
						} else {
							// We are not in a delimited arity group. We don't perform error recovery because in
							// this situation it's not as obvious what the behaviour should be, so we avoid any
							// surprises.
							if self.mode != Mode::TakeOneUnit {
								self.errors.push(
									SyntaxErr::ExprFoundOperandAfterOperand(
										self.get_previous_span().unwrap(),
										*span,
									),
								);
							}
							break 'main;
						}

						self.set_op_rhs_toggle();

						let comments = std::mem::take(&mut self.comments);
						self.operators.push_back(Op {
							span: *span,
							ty: OpTy::ParenStart(comments),
						});
						self.groups.push_back(Group::Paren(false, *span));

						state = State::Operand;

						can_start = Start::None;
					}
					arity_state = Arity::Operator;
				}
				Token::RParen if state == State::AfterOperand => {
					if !self.just_started_fn_arr_init()
						&& self.is_in_variable_arg_group()
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					let comments = std::mem::take(&mut self.comments);
					match self.end_bracket_fn(*span, comments) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					can_start = Start::None;

					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`.
				}
				Token::RParen if state == State::Operand => {
					if self.is_in_variable_arg_group()
						&& !just_started_arity_group
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					let prev_op_span = self.get_previous_span();
					let empty_group = self.just_started_paren();

					let comments = std::mem::take(&mut self.comments);
					match self.end_bracket_fn(*span, comments) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					self.errors.push(if empty_group {
						SyntaxErr::ExprFoundEmptyParenGroup(Span::new_between(
							prev_op_span.unwrap(),
							*span,
						))
					} else {
						SyntaxErr::ExprFoundRParenInsteadOfOperand(
							prev_op_span.unwrap(),
							*span,
						)
					});

					state = State::AfterOperand;

					can_start = Start::None;
				}
				Token::LBracket if state == State::AfterOperand => {
					// We switch state since after a `[`, we are expecting an operand, i.e.
					// `i[5 +..` rather than `i[+..`.
					let comments = std::mem::take(&mut self.comments);
					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::IndexStart(comments),
					});
					self.groups.push_back(Group::Index(false, *span));

					state = State::Operand;

					arity_state = Arity::Operator;

					can_start = Start::EmptyIndex;
				}
				Token::LBracket if state == State::Operand => {
					if self.mode != Mode::TakeOneUnit {
						self.errors.push(
							SyntaxErr::ExprFoundLBracketInsteadOfOperand(
								self.get_previous_span(),
								*span,
							),
						);
					}
					break 'main;
				}
				Token::RBracket if state == State::AfterOperand => {
					// We don't switch state since after a `]`, we are expecting an operator, i.e.
					// `..] + 5` instead of `..] 5`.
					let comments = std::mem::take(&mut self.comments);
					match self.end_index(*span, comments) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					// After an index `ident[..]` we may have an array constructor.
					can_start = Start::ArrInit;

					arity_state = Arity::PotentialEnd;
				}
				Token::RBracket if state == State::Operand => {
					if can_start == Start::EmptyIndex {
						let comments = std::mem::take(&mut self.comments);
						match self.end_index(*span, comments) {
							Ok(_) => {}
							Err(_) => {
								break 'main;
							}
						}
					} else {
						let prev_op_span = self.get_previous_span();

						let comments = std::mem::take(&mut self.comments);
						match self.end_index(*span, comments) {
							Ok(_) => {}
							Err(_) => {
								break 'main;
							}
						}

						self.errors.push(
							SyntaxErr::ExprFoundRBracketInsteadOfOperand(
								prev_op_span.unwrap(),
								*span,
							),
						);
					}
					// We switch state since after a `]`, we are expecting an operator, i.e.
					// `..[] + 5` rather than `..[] 5`.
					state = State::AfterOperand;

					arity_state = Arity::PotentialEnd;
				}
				Token::LBrace if state == State::Operand => {
					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `{10, {` or `{10 {` or `{1+1  {`
					// but not:
					// `a {` or `fn{10 + {`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::Operator;

					self.set_op_rhs_toggle();

					let comments = std::mem::take(&mut self.comments);
					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::InitStart(comments),
					});
					self.groups.push_back(Group::Init(0, *span));

					can_start = Start::None;

					just_started_arity_group = true;

					// We don't switch state since after a `{`, we are expecting an operand, i.e.
					// `..+ {1,` rather than `..+ {,`.
				}
				Token::LBrace if state == State::AfterOperand => {
					// If we previously had a token which can end an argument of an arity group, and we are in a
					// delimited arity group, we want to increase the arity, for example:
					// `{10, {` or `{10 {` or `{1+1  {`
					// but not:
					// `a {` or `fn{10 + {`
					if self.is_in_variable_arg_group()
						&& arity_state == Arity::PotentialEnd
					{
						self.register_arity_argument(span.start_zero_width());
					} else {
						if self.mode != Mode::TakeOneUnit {
							self.errors.push(
								SyntaxErr::ExprFoundOperandAfterOperand(
									self.get_previous_span().unwrap(),
									*span,
								),
							);
						}
						break 'main;
					}
					arity_state = Arity::Operator;

					self.set_op_rhs_toggle();

					let comments = std::mem::take(&mut self.comments);
					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::InitStart(comments),
					});
					self.groups.push_back(Group::Init(0, *span));

					state = State::Operand;

					can_start = Start::None;

					just_started_arity_group = true;
				}
				Token::RBrace if state == State::AfterOperand => {
					if self.is_in_variable_arg_group() {
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					let comments = std::mem::take(&mut self.comments);
					match self.end_init(*span, comments) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					can_start = Start::None;

					// We don't switch state since after a `}`, we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
				}
				Token::RBrace if state == State::Operand => {
					if self.is_in_variable_arg_group()
						&& !just_started_arity_group
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					let prev_op_span = self.get_previous_span();
					let empty_group = self.just_started_init();

					// This is valid, i.e. `{}`, or `{1, }`.
					let comments = std::mem::take(&mut self.comments);
					match self.end_init(*span, comments) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					self.errors.push(if empty_group {
						SyntaxErr::ExprFoundEmptyInitializerGroup(
							Span::new_between(prev_op_span.unwrap(), *span),
						)
					} else {
						SyntaxErr::ExprFoundRBraceInsteadOfOperand(
							prev_op_span.unwrap(),
							*span,
						)
					});

					// We switch state since after an init list we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
					state = State::AfterOperand;

					can_start = Start::None;
				}
				Token::Comma if state == State::AfterOperand => {
					if (self.mode == Mode::DisallowTopLevelList
						|| self.mode == Mode::TakeOneUnit)
						&& self.groups.is_empty()
					{
						break 'main;
					}

					if arity_state == Arity::PotentialEnd {
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(Either::Left(Node {
						span: *span,
						ty: NodeTy::Separator(std::mem::take(
							&mut self.comments,
						)),
					}));

					// We switch state since after a comma (which delineates an expression), we're effectively
					// starting a new expression which must start with an operand, i.e.
					// `.., 5 + 6` instead of `.., + 6`.
					state = State::Operand;

					can_start = Start::None;
				}
				Token::Comma if state == State::Operand => {
					if (self.mode == Mode::DisallowTopLevelList
						|| self.mode == Mode::TakeOneUnit)
						&& self.groups.is_empty()
					{
						break 'main;
					}

					// This is an error, e.g. `..+ ,` instead of `..+ 1,`.
					// We only create this error if there is something before this comma, because if there isn't,
					// the list analysis will produce an error anyway, and we don't want two errors for the same
					// incorrect syntax.
					if !self.operators.is_empty() {
						self.errors.push(
							SyntaxErr::ExprFoundCommaInsteadOfOperand(
								self.get_previous_span().unwrap(),
								*span,
							),
						);
					} else if !self.stack.is_empty() {
						if let Some(Either::Left(Node {
							span: _,
							ty: NodeTy::Separator(_),
						})) = self.stack.back()
						{
						} else {
							self.errors.push(
								SyntaxErr::ExprFoundCommaInsteadOfOperand(
									self.get_previous_span().unwrap(),
									*span,
								),
							);
						}
					}

					if can_start == Start::EmptyIndex {
						match self.groups.back_mut() {
							Some(g) => match g {
								Group::Index(contains_i, _) => {
									*contains_i = false;
								}
								_ => unreachable!(),
							},
							_ => unreachable!(),
						}
					}

					if !just_started_arity_group
						|| self.is_in_variable_arg_group() == false
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(Either::Left(Node {
						span: *span,
						ty: NodeTy::Separator(std::mem::take(
							&mut self.comments,
						)),
					}));

					can_start = Start::None;
				}
				Token::Dot if state == State::AfterOperand => {
					// We don't need to consider arity because a dot after an operand will always be a valid object
					// access notation, and in the alternate branch we don't recover from the error.

					let comments = std::mem::take(&mut self.comments);
					self.push_operator(Op {
						span: *span,
						ty: OpTy::ObjAccess(false, comments),
					});

					// We switch state since after an object access we are execting an operand, such as:
					// `foo. bar()`.
					state = State::Operand;

					can_start = Start::None;
				}
				Token::Dot if state == State::Operand => {
					// We have encountered something like: `foo + . ` or `foo.bar(). . `.
					//
					// We do not recover from this error because we currently mandate that the `ExprTy::ObjAccess`
					// node has a left-hand side.
					//
					// MAYBE: Should we make this a recoverable situation? (If so we need to consider arity)

					self.errors.push(SyntaxErr::ExprFoundDotInsteadOfOperand(
						self.get_previous_span(),
						*span,
					));
					break 'main;
				}
				Token::Question => {
					if state == State::Operand {
						// We have encountered something like: `foo + ?`.
						self.errors.push(
							SyntaxErr::ExprFoundQuestionInsteadOfOperand(
								self.get_previous_span(),
								*span,
							),
						);
					}

					let comments = std::mem::take(&mut self.comments);
					self.push_operator(Op {
						span: *span,
						ty: OpTy::TernaryQ(false, comments),
					});
					self.groups.push_back(Group::Ternary);

					// We switch state since after the `?` we are expecting an operand, such as:
					// `foo ? bar`.
					state = State::Operand;

					can_start = Start::None;

					arity_state = Arity::Operator;
				}
				Token::Colon => {
					if !self.is_in_ternary() {
						break 'main;
					}

					if state == State::Operand {
						// We have encountered something like: `foo ? a + :`.
						self.errors.push(
							SyntaxErr::ExprFoundColonInsteadOfOperand(
								self.get_previous_span(),
								*span,
							),
						);
					}

					let comments = std::mem::take(&mut self.comments);
					self.push_operator(Op {
						span: *span,
						ty: OpTy::TernaryC(false, comments),
					});

					// We switch state since after the `:` we are expecting an operand, such as:
					// `foo ? bar : baz2`.
					state = State::Operand;

					can_start = Start::None;

					arity_state = Arity::Operator;
				}
				_ => {
					// We have encountered an unexpected token that's not allowed to be part of an expression.
					self.errors.push(SyntaxErr::ExprFoundInvalidToken(*span));
					break 'main;
				}
			}

			// Reset the flag. This is a separate statement because otherwise this assignment would have to be in
			// _every_ single branch other than the l_paren branch and this is just cleaner/more maintainable.
			match token {
				Token::LParen | Token::LBrace => {}
				_ => just_started_arity_group = false,
			}

			walker.advance();
		}

		if !self.groups.is_empty() {
			// The end position of this expression will be the end position of the last parsed item.
			let group_end = self.get_previous_span().unwrap().end_zero_width();

			// Close any open groups.
			//
			// Note: we don't take ownership of the group because the individual `collapse_*()` methods do that.
			while let Some(group) = self.groups.back_mut() {
				match group {
					Group::FnCall(_, _)
					| Group::Init(_, _)
					| Group::ArrInit(_, _) => {
						if !just_started_arity_group {
							self.register_arity_argument(group_end);
						}
					}
					// A list always goes to the end of the expression, so we never increment the counter in the
					// main loop, hence we must always do it here.
					Group::List(count, _) => *count += 1,
					_ => {}
				}

				// After the first iteration, reset to false because if there are more groups, then they definitely
				// have at least one argument; this empty group.
				just_started_arity_group = false;

				let group = self.groups.pop_back().unwrap();
				match group {
					Group::Paren(_, l_paren) => {
						self.errors.push(SyntaxErr::ExprUnclosedParenthesis(
							l_paren, group_end,
						));
						self.collapse_bracket(group, group_end, vec![]);
					}
					Group::Index(_, l_bracket) => {
						self.errors.push(SyntaxErr::ExprUnclosedIndexOperator(
							l_bracket, group_end,
						));
						self.collapse_index(group, group_end, vec![])
					}
					Group::FnCall(_, l_paren) => {
						self.errors.push(SyntaxErr::ExprUnclosedFunctionCall(
							l_paren, group_end,
						));
						self.collapse_fn(group, group_end, vec![])
					}
					Group::Init(_, l_brace) => {
						self.errors.push(
							SyntaxErr::ExprUnclosedInitializerList(
								l_brace, group_end,
							),
						);
						self.collapse_init(group, group_end, vec![])
					}
					Group::ArrInit(_, l_paren) => {
						self.errors.push(
							SyntaxErr::ExprUnclosedArrayConstructor(
								l_paren, group_end,
							),
						);
						self.collapse_arr_init(group, group_end, vec![])
					}
					Group::List(_, _) => {
						self.collapse_list(group, group_end.end)
					}
					Group::Ternary => {}
				}
			}
		}

		// If there is an open group, then all of the operators will have been already moved as part of the
		// collapsing functions. However, if we didn't need to close any groups, we may have leftover operators
		// which still need moving.
		while let Some(op) = self.operators.pop_back() {
			self.stack.push_back(Either::Right(op));
		}
	}

	/// Converts the internal RPN stack into a singular `Expr` node, which contains the entire expression.
	fn create_ast(&mut self) -> Option<Expr> {
		let mut stack: VecDeque<Expr> = VecDeque::new();

		// We have "parsed" the token stream and we immediately hit a token which cannot be part of an expression.
		// Hence, there is no expression to return at all.
		if self.stack.len() == 0 {
			return None;
		}

		let pop_back = |stack: &mut VecDeque<Expr>| stack.pop_back().unwrap();

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the n-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(item) = self.stack.pop_front() {
			match item {
				Either::Left(node) => match node.ty {
					NodeTy::Lit(lit, comments) => {
						stack.push_back(Expr {
							span: node.span,
							ty: ExprTy::Lit {
								comments_before: comments,
								lit,
							},
						});
					}
					NodeTy::Ident(ident, comments) => {
						stack.push_back(Expr {
							span: node.span,
							ty: ExprTy::Ident {
								comments_before: comments,
								ident,
							},
						});
					}
					NodeTy::Separator(comments) => {
						stack.push_back(Expr {
							span: node.span,
							ty: ExprTy::Separator {
								comments_before: comments,
							},
						});
					}
					NodeTy::Invalid(comments) => {
						stack.push_back(Expr {
							span: node.span,
							ty: ExprTy::Invalid {
								comments_before: comments,
							},
						});
					}
				},
				/* Either::Left(node) => match node.ty {
					ExprTy::LineComment(_) | ExprTy::BlockComment(_) => {
						let mut comments = VecDeque::new();
						comments.push_front(node);
						'comments: while let Some(e) = self.stack.front() {
							match e {
								Either::Left(e) => match e.ty {
									ExprTy::LineComment(_)
									| ExprTy::BlockComment(_) => match self.stack.pop_front().unwrap() {
										Either::Left(e) => {
											comments.push_front(e);
										}
										Either::Right(_) => unreachable!(),
									},
									_ => break 'comments,
								},
								Either::Right(_) => unreachable!(),
							}
						}

						match self.stack.pop_front().unwrap() {
							Either::Left(e) => stack.push_back(e),
							Either::Right(_) => unreachable!(),
						}
						stack.append(&mut comments);
					}
					_ => {
						stack.push_back(node);
					}
				}, */
				Either::Right(op) => match op.ty {
					OpTy::AddPre(has_operand, comments) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};
						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								comments_before: comments,
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Add,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::SubPre(has_operand, comments) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};
						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								comments_before: comments,
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Sub,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::AddPost(comments) => {
						let expr = pop_back(&mut stack);
						let span = Span::new(expr.span.start, op.span.end);
						stack.push_back(Expr {
							span,
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								comments_before_op: comments,
								op: PostOp {
									ty: PostOpTy::Add,
									span: op.span,
								},
							},
						});
					}
					OpTy::SubPost(comments) => {
						let expr = pop_back(&mut stack);
						let span = Span::new(expr.span.start, op.span.end);
						stack.push_back(Expr {
							span,
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								comments_before_op: comments,
								op: PostOp {
									ty: PostOpTy::Sub,
									span: op.span,
								},
							},
						});
					}
					OpTy::Neg(has_operand, comments) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};
						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								comments_before: comments,
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Neg,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Flip(has_operand, comments) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};
						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								comments_before: comments,
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Flip,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Not(has_operand, comments) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};
						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								comments_before: comments,
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Not,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::TernaryQ(has_rhs, comments) => {
						let last = pop_back(&mut stack);
						let (cond, true_) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let span = if let Some(ref true_) = true_ {
							Span::new(cond.span.start, true_.span.end)
						} else {
							Span::new(cond.span.start, op.span.end)
						};

						stack.push_back(Expr {
							ty: ExprTy::Ternary {
								cond: Box::from(cond),
								comments_before_question: comments,
								question: op.span,
								true_: true_.map(|e| Box::from(e)),
								comments_before_colon: vec![],
								colon: None,
								false_: None,
							},
							span,
						});
					}
					OpTy::TernaryC(has_rhs, comments) => {
						let last = pop_back(&mut stack);
						let (prev, false_) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let (cond, comments_before_question, question, true_) =
							match prev.ty {
								ExprTy::Ternary {
									cond,
									comments_before_question,
									question,
									true_,
									comments_before_colon: _,
									colon: _,
									false_: _,
								} => (
									cond,
									comments_before_question,
									question,
									true_,
								),
								// Panics: `prev` is guaranteed to be a `ExprTy::Ternary` which only has the `cond`,
								// `question` and `true_` fields filled in.
								_ => unreachable!(),
							};

						let span = if let Some(ref false_) = false_ {
							Span::new(prev.span.start, false_.span.end)
						} else {
							Span::new(prev.span.start, op.span.end)
						};

						stack.push_back(Expr {
							ty: ExprTy::Ternary {
								cond,
								comments_before_question,
								question,
								true_,
								comments_before_colon: comments,
								colon: Some(op.span),
								false_: false_.map(|e| Box::from(e)),
							},
							span,
						});
					}
					OpTy::Paren(
						has_inner,
						l_span,
						end,
						l_comments,
						r_comments,
					) => {
						let expr = if has_inner {
							Some(pop_back(&mut stack))
						} else {
							None
						};

						stack.push_back(Expr {
							span: op.span,
							ty: ExprTy::Paren {
								comments_before: l_comments,
								l_paren: l_span,
								expr: expr.map(|e| Box::from(e)),
								comments_before_r: r_comments,
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::FnCall(
						count,
						l_paren,
						end,
						l_comments,
						r_comments,
					) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}
						// Get the identifier (which is the first expression).
						let (comments_before, ident) = match temp.pop_front().unwrap().ty {
							ExprTy::Ident{ comments_before,ident} => (comments_before, ident),
							_ => panic!("The first expression of a function call operator is not an identifier!")
						};

						// Construct a proper comma-separated list.
						let mut args = List::new();
						while let Some(arg) = temp.pop_front() {
							match arg.ty {
								ExprTy::Separator { comments_before } => args
									.push_separator(comments_before, arg.span),
								_ => args.push_item(arg),
							}
						}

						args.analyze_syntax_errors_fn_arr_init(
							&mut self.errors,
							l_paren,
						);

						stack.push_back(Expr {
							span: Span::new(ident.span.start, end.end),
							ty: ExprTy::Fn {
								comments_before,
								ident,
								comments_before_l: l_comments,
								l_paren,
								args,
								comments_before_r: r_comments,
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::Index(
						contains_i,
						l_bracket,
						end,
						l_comments,
						r_comments,
					) => {
						let i = if contains_i {
							Some(Box::from(pop_back(&mut stack)))
						} else {
							None
						};
						let expr = pop_back(&mut stack);
						stack.push_back(Expr {
							span: Span::new(expr.span.start, end.end),
							ty: ExprTy::Index {
								item: Box::from(expr),
								comments_before_l: l_comments,
								l_bracket,
								i,
								comments_before_r: r_comments,
								r_bracket: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::Init(
						count,
						l_brace,
						r_brace,
						l_comments,
						r_comments,
					) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						// Construct a proper comma-separated list.
						let mut args = List::new();
						while let Some(arg) = temp.pop_front() {
							match arg.ty {
								ExprTy::Separator { comments_before } => args
									.push_separator(comments_before, arg.span),
								_ => args.push_item(arg),
							}
						}

						args.analyze_syntax_errors_init(
							&mut self.errors,
							l_brace,
						);

						stack.push_back(Expr {
							ty: ExprTy::Init {
								comments_before: l_comments,
								l_brace,
								args,
								comments_before_r: r_comments,
								r_brace: if r_brace.is_zero_width() {
									None
								} else {
									Some(r_brace)
								},
							},
							span: op.span,
						});
					}
					OpTy::ArrInit(
						count,
						l_paren,
						end,
						l_comments,
						r_comments,
					) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						// Get the index operator (which is the first expression).
						let arr = temp.pop_front().unwrap();
						match arr.ty {
							ExprTy::Index { .. } => {}
							_ => {
								panic!("The first expression of an array constructor operator is not an `Expr::Index`!");
							}
						}

						// Construct a proper comma-separated list.
						let mut args = List::new();
						while let Some(arg) = temp.pop_front() {
							match arg.ty {
								ExprTy::Separator { comments_before } => args
									.push_separator(comments_before, arg.span),
								_ => args.push_item(arg),
							}
						}

						args.analyze_syntax_errors_fn_arr_init(
							&mut self.errors,
							l_paren,
						);

						stack.push_back(Expr {
							span: Span::new(arr.span.start, end.end),
							ty: ExprTy::ArrInit {
								arr: Box::from(arr),
								comments_before_l: l_comments,
								l_paren,
								args,
								comments_before_r: r_comments,
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::List(count) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						// Construct a proper comma-separated list.
						let mut args = List::new();
						while let Some(arg) = temp.pop_front() {
							match arg.ty {
								ExprTy::Separator { comments_before } => args
									.push_separator(comments_before, arg.span),
								_ => args.push_item(arg),
							}
						}

						args.analyze_syntax_errors_list(&mut self.errors);

						stack.push_back(Expr {
							ty: ExprTy::List(args),
							span: op.span,
						});
					}
					OpTy::ObjAccess(has_rhs, comments) => {
						let last = pop_back(&mut stack);
						let (left, right) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let span = if let Some(ref right) = right {
							Span::new(left.span.start, right.span.end)
						} else {
							Span::new(left.span.start, op.span.end)
						};

						stack.push_back(Expr {
							ty: ExprTy::ObjAccess {
								obj: Box::from(left),
								comments_before_dot: comments,
								dot: op.span,
								leaf: right.map(|e| Box::from(e)),
							},
							span,
						});
					}
					OpTy::Add(has_rhs, _)
					| OpTy::Sub(has_rhs, _)
					| OpTy::Mul(has_rhs, _)
					| OpTy::Div(has_rhs, _)
					| OpTy::Rem(has_rhs, _)
					| OpTy::And(has_rhs, _)
					| OpTy::Or(has_rhs, _)
					| OpTy::Xor(has_rhs, _)
					| OpTy::LShift(has_rhs, _)
					| OpTy::RShift(has_rhs, _)
					| OpTy::EqEq(has_rhs, _)
					| OpTy::NotEq(has_rhs, _)
					| OpTy::Gt(has_rhs, _)
					| OpTy::Lt(has_rhs, _)
					| OpTy::Ge(has_rhs, _)
					| OpTy::Le(has_rhs, _)
					| OpTy::AndAnd(has_rhs, _)
					| OpTy::OrOr(has_rhs, _)
					| OpTy::XorXor(has_rhs, _)
					| OpTy::Eq(has_rhs, _)
					| OpTy::AddEq(has_rhs, _)
					| OpTy::SubEq(has_rhs, _)
					| OpTy::MulEq(has_rhs, _)
					| OpTy::DivEq(has_rhs, _)
					| OpTy::RemEq(has_rhs, _)
					| OpTy::AndEq(has_rhs, _)
					| OpTy::OrEq(has_rhs, _)
					| OpTy::XorEq(has_rhs, _)
					| OpTy::LShiftEq(has_rhs, _)
					| OpTy::RShiftEq(has_rhs, _) => {
						let last = pop_back(&mut stack);
						let (left, right) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let span = if let Some(ref right) = right {
							Span::new(left.span.start, right.span.end)
						} else {
							Span::new(left.span.start, op.span.end)
						};

						let (bin_op, comments) = op.to_bin_op();

						stack.push_back(Expr {
							ty: ExprTy::Binary {
								left: Box::from(left),
								comments_before_op: comments,
								op: bin_op,
								right: right.map(|e| Box::from(e)),
							},
							span,
						});
					}
					_ => {
						panic!("Invalid operator {op:?} in shunting yard stack. This operator should never be present in the final RPN output stack.");
					}
				},
			}
		}

		if stack.len() > 1 {
			let expr = pop_back(&mut stack);
			stack.push_back(expr);
		}

		#[cfg(debug_assertions)]
		if stack.len() != 1 {
			panic!("After processing the shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap())
	}
}

/*
#[test]
#[rustfmt::skip]
fn binaries() {
	// Single operator
	assert_expr!("5 + 1", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})
		},
		span: span(0, 5)
	});
	assert_expr!("ident * 100.4", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "ident".into(), span: span(0, 5)}), span: span(0, 5)}),
			op: Op{ty: OpTy::Mul, span: span(6, 7)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Float(100.4)), span: span(8, 13)})
		},
		span: span(0, 13)
	});
	assert_expr!("30 << 8u", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(30)), span: span(0, 2)}),
			op: Op{ty: OpTy::LShift, span: span(3, 5)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::UInt(8)), span: span(6, 8)})
		},
		span: span(0, 8),
	});

	// Multiple operators
	assert_expr!("5 + 1 / 3", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
					op: Op{ty: OpTy::Div, span: span(6, 7)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)})
				},
				span: span(4, 9),
			})
		},
		span: span(0, 9),
	});
	assert_expr!("5 * 4 * 3", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Mul, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(4)), span: span(4, 5)}),
					op: Op{ty: OpTy::Mul, span: span(6, 7)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)})
				},
				span: span(4, 9),
			})
		},
		span: span(0, 9),
	});
	assert_expr!("5 + 1 / 3 * i", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
					op: Op{ty: OpTy::Div, span: span(6, 7)},
					right: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)}),
							op: Op{ty: OpTy::Mul, span: span(10, 11)},
							right: Box::from(Expr{ty:ExprTy::Ident(Ident{name: "i".into(), span: span(12, 13)}), span: span(12, 13)})
						},
						span: span(8, 13)
					})
				},
				span: span(4, 13),
			})
		},
		span: span(0, 13),
	});
	assert_expr!("5 + 1 == true * i", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
					op: Op{ty: OpTy::Add, span: span(2, 3)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})
				},
				span: span(0, 5),
			}),
			op: Op{ty: OpTy::EqEq, span: span(6, 8)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(9, 13)}),
					op: Op{ty: OpTy::Mul, span: span(14, 15)},
					right: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(16, 17)}), span: span(16, 17)})
				},
				span: span(9, 17),
			})
		},
		span: span(0, 17)
	});
}

#[test]
#[rustfmt::skip]
fn unaries() {
	// Single operator
	assert_expr!("-5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("~5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Flip, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("!5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Not, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("++5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 3),
	});
	assert_expr!("--5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
			op: Op{ty: OpTy::Sub, span: span(0, 2)},
		},
		span: span(0, 3),
	});
	assert_expr!("5++", Expr {
		ty: ExprTy::Postfix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(1, 3)},
		},
		span: span(0, 3),
	});
	assert_expr!("5--", Expr {
		ty: ExprTy::Postfix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Sub, span: span(1, 3)},
		},
		span: span(0, 3),
	});

	// Multiple operators
	assert_expr!("- -5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty:ExprTy::Lit(Lit::Int(5)), span: span(3, 4)}),
					op: Op{ty: OpTy::Neg, span: span(2, 3)},
				},
				span: span(2, 4),
			}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 4),
	});
	assert_expr!("- - -5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr {
						ty: ExprTy::Prefix {
							expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(5, 6)}),
							op: Op{ty: OpTy::Neg, span: span(4, 5)},
						},
						span: span(4, 6),
					}),
					op: Op{ty: OpTy::Neg, span: span(2, 3)},
				},
				span: span(2, 6),
			}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 6),
	});
	assert_expr!("!!5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty:ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
					op: Op{ty: OpTy::Not, span: span(1, 2)},
				},
				span: span(1, 3),
			}),
			op: Op{ty: OpTy::Not, span: span(0, 1)},
		},
		span: span(0, 3),
	});
	assert_expr!("++++5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr {
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(4, 5)}),
					op: Op{ty: OpTy::Add, span: span(2, 4)},
				},
				span: span(2, 5),
			}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 5),
	});
	assert_expr!("++5--", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr {
				ty: ExprTy::Postfix {
					expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
					op: Op{ty: OpTy::Sub, span: span(3, 5)},
				},
				span: span(2, 5),
			}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 5),
	});
}

#[test]
#[rustfmt::skip]
fn complex() {
	assert_expr!("func(i[9], foo-- -6)", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "func".into(), span: span(0, 4)},
			args: vec![
				Expr {
					ty: ExprTy::Index {
						item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(5, 6)}), span: span(5, 6)}),
						i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(9)), span: span(7, 8)})),
						op: span(6, 9),
					},
					span: span(5, 9),
				},
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr {
							ty: ExprTy::Postfix {
								expr: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "foo".into(), span: span(11, 14)}), span: span(11, 14)}),
								op: Op{ty: OpTy::Sub, span: span(14, 16)},
							},
							span: span(11, 16),
						}),
						op: Op{ty: OpTy::Sub, span: span(17, 18)},
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(6)), span: span(18, 19)}),
					},
					span: span(11, 19),
				}

			]
		},
		span: span(0, 20),
	});
	assert_expr!("true << i[func((1 + 2) * 5.0)]", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(0, 4)}),
			op: Op{ty: OpTy::LShift, span: span(5, 7)},
			right: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(8, 9)}), span: span(8, 9)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "func".into(), span: span(10, 14)},
							args: vec![
								Expr {
									ty: ExprTy::Binary {
										left: Box::from(Expr {
											ty: ExprTy::Paren {
												expr: Box::from(Expr {
													ty: ExprTy::Binary {
														left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(16, 17)}),
														op: Op{ty: OpTy::Add, span: span(18, 19)},
														right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(20, 21)}),
													},
													span: span(16, 21),
												}),
												left: span(15, 16),
												right: span(21, 22),
											},
											span: span(15, 22),
										}),
										op: Op{ty: OpTy::Mul, span: span(23, 24)},
										right: Box::from(Expr{ty: ExprTy::Lit(Lit::Float(5.0)), span: span(25, 28)}),
									},
									span: span(15, 28),
								}
							],
						},
						span: span(10, 29),
					})),
					op: span(9, 30),
				},
				span: span(8, 30),
			}),
		},
		span: span(0, 30),
	});
	assert_expr!("{1.0, true, func(i[0], 100u)}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Float(1.0)), span: span(1, 4)},
			Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(6, 10)},
			Expr {
				ty: ExprTy::Fn {
					ident: Ident{name: "func".into(), span: span(12, 16)},
					args: vec![
						Expr {
							ty: ExprTy::Index {
								item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(17, 18)}), span: span(17, 18)}),
								i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(0)), span: span(19, 20)})),
								op: span(18, 21),
							},
							span: span(17, 21),
						},
						Expr{ty: ExprTy::Lit(Lit::UInt(100)), span: span(23, 27)},
					]
				},
				span: span(12, 28),
			}
		]),
		span: span(0, 29),
	});
	assert_expr!("mat2[]({vec2(1, 2), vec2(3, 4)})", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "mat2".into(), span: span(0, 4)}), span: span(0, 4)}),
					i: None,
					op: span(4, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr {
				ty: ExprTy::Init(vec![
					Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "vec2".into(), span: span(8, 12)},
							args: vec![
								Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(13, 14)},
								Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(16, 17)},
							],
						},
						span: span(8, 18),
					},
					Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "vec2".into(), span: span(20, 24)},
							args: vec![
								Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(25, 26)},
								Expr{ty: ExprTy::Lit(Lit::Int(4)), span: span(28, 29)},
							],
						},
						span: span(20, 30),
					},
				]),
				span: span(7, 31),
			}],
		},
		span: span(0, 32),
	});
}
 */
