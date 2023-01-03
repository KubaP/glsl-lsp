//! The parser for general expressions.

use super::{
	ast::{
		BinOp, BinOpTy, Expr, ExprTy, Ident, Lit, PostOp, PostOpTy, PreOp,
		PreOpTy,
	},
	SyntaxModifiers, SyntaxToken, SyntaxType, Walker,
};
use crate::{
	diag::{ExprDiag, Semantic, Syntax},
	lexer::{self, Token},
	Either, Span,
};
use std::collections::VecDeque;

/*
Useful reading links related to expression parsing:

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
///
/// - `end_tokens` - Any tokens which, when encountered, will immediately stop the parser without producing syntax
///   errors.
pub(super) fn expr_parser<'a, P: super::TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	mode: Mode,
	end_tokens: impl AsRef<[Token]>,
) -> (Option<Expr>, Vec<Syntax>, Vec<Semantic>, Vec<SyntaxToken>) {
	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		// If we are at the end of the token stream, we can return early with nothing.
		None => return (None, vec![], vec![], vec![]),
	};

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: Vec::new(),
		start_position,
		mode,
		syntax_diags: Vec::new(),
		semantic_diags: Vec::new(),
		syntax_tokens: Vec::new(),
	};
	parser.parse(walker, end_tokens.as_ref());

	(
		parser.create_ast(),
		parser.syntax_diags,
		parser.semantic_diags,
		parser.syntax_tokens,
	)
}

/// Configures the behaviour of the expression parser.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum Mode {
	/// The default behaviour which can be used to parse any valid expressions, including those that can form
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
	Lit(Lit),
	Ident(Ident),
	Separator,
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
	Add(bool),
	Sub(bool),
	Mul(bool),
	Div(bool),
	Rem(bool),
	And(bool),
	Or(bool),
	Xor(bool),
	LShift(bool),
	RShift(bool),
	Eq(bool),
	AddEq(bool),
	SubEq(bool),
	MulEq(bool),
	DivEq(bool),
	RemEq(bool),
	AndEq(bool),
	OrEq(bool),
	XorEq(bool),
	LShiftEq(bool),
	RShiftEq(bool),
	EqEq(bool),
	NotEq(bool),
	AndAnd(bool),
	OrOr(bool),
	XorXor(bool),
	Gt(bool),
	Lt(bool),
	Ge(bool),
	Le(bool),
	/// - `0` - Whether to consume a node for the leaf expression (after the `.`).
	ObjAccess(bool),
	/// - `0` - Whether to consume a node for the if expression (after the `?`).
	TernaryQ(bool),
	/// - `0` - Whether to consume a node for the else expression (after the `:`).
	TernaryC(bool),
	/* PREFIX OPERATORS */
	/* - `0` - Whether to consume a node for the expression. */
	AddPre(bool),
	SubPre(bool),
	Neg(bool),
	Flip(bool),
	Not(bool),
	/* POSTFIX OPERATORS */
	AddPost,
	SubPost,
	/* GROUP BEGINNING DELIMITERS */
	/// The `(` token.
	ParenStart,
	/// The `(` token.
	FnCallStart,
	/// The `[` token.
	IndexStart,
	/// The `{` token.
	InitStart,
	/// The `(` token.
	ArrInitStart,
	/* GROUPS */
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis.
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	Paren(bool, Span, Span),
	/// A function call. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the function identifier node, so it
	///   will always be `1` or greater.
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	FnCall(usize, Span, Span),
	/// An index operator. This operator spans from the opening bracket to the closing bracket.
	///
	/// - `0` - Whether to consume a node for the expression within the `[...]` brackets.
	/// - `1` - The span of the opening bracket.
	/// - `2` - The span of the closing bracket. If this is zero-width, that means there is no `]` token present.
	Index(bool, Span, Span),
	/// An initializer list. This operator spans from the opening brace to the closing brace.
	///
	/// - `0` - The number of nodes to consume for the arguments.
	/// - `1` - The span of the opening brace.
	/// - `2` - The span of the closing brace. If this is zero-width, that means there is no `}` token present.
	Init(usize, Span, Span),
	/// An array initializer. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the index expression node, so it
	///   will always be `1` or greater.
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	ArrInit(usize, Span, Span),
	/// A general list **outside** of function calls, initializer lists and array constructors.
	///
	/// - `0` - The number of nodes to consume for the arguments.
	List(usize),
}

impl Op {
	/// Converts from a lexer `OpTy` token to the `Op` type used in this expression parser.
	fn from_token(token: lexer::OpTy, span: Span) -> Self {
		Self {
			span,
			ty: match token {
				lexer::OpTy::Add => OpTy::Add(false),
				lexer::OpTy::Sub => OpTy::Sub(false),
				lexer::OpTy::Mul => OpTy::Mul(false),
				lexer::OpTy::Div => OpTy::Div(false),
				lexer::OpTy::Rem => OpTy::Rem(false),
				lexer::OpTy::And => OpTy::And(false),
				lexer::OpTy::Or => OpTy::Or(false),
				lexer::OpTy::Xor => OpTy::Xor(false),
				lexer::OpTy::LShift => OpTy::LShift(false),
				lexer::OpTy::RShift => OpTy::RShift(false),
				lexer::OpTy::Eq => OpTy::Eq(false),
				lexer::OpTy::AddEq => OpTy::AddEq(false),
				lexer::OpTy::SubEq => OpTy::SubEq(false),
				lexer::OpTy::MulEq => OpTy::MulEq(false),
				lexer::OpTy::DivEq => OpTy::DivEq(false),
				lexer::OpTy::RemEq => OpTy::RemEq(false),
				lexer::OpTy::AndEq => OpTy::AndEq(false),
				lexer::OpTy::OrEq => OpTy::OrEq(false),
				lexer::OpTy::XorEq => OpTy::XorEq(false),
				lexer::OpTy::LShiftEq => OpTy::LShiftEq(false),
				lexer::OpTy::RShiftEq => OpTy::RShiftEq(false),
				lexer::OpTy::EqEq => OpTy::EqEq(false),
				lexer::OpTy::NotEq => OpTy::NotEq(false),
				lexer::OpTy::AndAnd => OpTy::AndAnd(false),
				lexer::OpTy::OrOr => OpTy::OrOr(false),
				lexer::OpTy::XorXor => OpTy::XorXor(false),
				lexer::OpTy::Gt => OpTy::Gt(false),
				lexer::OpTy::Lt => OpTy::Lt(false),
				lexer::OpTy::Ge => OpTy::Ge(false),
				lexer::OpTy::Le => OpTy::Le(false),
				lexer::OpTy::Not
				| lexer::OpTy::Flip
				| lexer::OpTy::AddAdd
				| lexer::OpTy::SubSub => {
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
			OpTy::ObjAccess(_) => 33,
			OpTy::AddPost | OpTy::SubPost => 31,
			OpTy::AddPre(_)
			| OpTy::SubPre(_)
			| OpTy::Neg(_)
			| OpTy::Flip(_)
			| OpTy::Not(_) => 29,
			OpTy::Mul(_) | OpTy::Div(_) | OpTy::Rem(_) => 27,
			OpTy::Add(_) | OpTy::Sub(_) => 25,
			OpTy::LShift(_) | OpTy::RShift(_) => 23,
			OpTy::Lt(_) | OpTy::Gt(_) | OpTy::Le(_) | OpTy::Ge(_) => 21,
			OpTy::EqEq(_) | OpTy::NotEq(_) => 19,
			OpTy::And(_) => 17,
			OpTy::Xor(_) => 15,
			OpTy::Or(_) => 13,
			OpTy::AndAnd(_) => 11,
			OpTy::XorXor(_) => 9,
			OpTy::OrOr(_) => 7,
			OpTy::TernaryQ(_) => 5,
			OpTy::TernaryC(_) => 3,
			OpTy::Eq(_)
			| OpTy::AddEq(_)
			| OpTy::SubEq(_)
			| OpTy::MulEq(_)
			| OpTy::DivEq(_)
			| OpTy::RemEq(_)
			| OpTy::AndEq(_)
			| OpTy::XorEq(_)
			| OpTy::OrEq(_)
			| OpTy::LShiftEq(_)
			| OpTy::RShiftEq(_) => 1,
			// These are never directly checked for precedence, but rather have special branches.
			_ => unreachable!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
		}
	}

	fn to_bin_op(self) -> BinOp {
		let ty = match self.ty {
				OpTy::Add(_) => BinOpTy::Add,
				OpTy::Sub(_) => BinOpTy::Sub,
				OpTy::Mul(_) => BinOpTy::Mul,
				OpTy::Div(_) => BinOpTy::Div,
				OpTy::Rem(_) => BinOpTy::Rem,
				OpTy::And(_) => BinOpTy::And,
				OpTy::Or(_) => BinOpTy::Or,
				OpTy::Xor(_) => BinOpTy::Xor,
				OpTy::LShift(_) => BinOpTy::LShift,
				OpTy::RShift(_) => BinOpTy::RShift,
				OpTy::Eq(_) => BinOpTy::Eq,
				OpTy::AddEq(_) => BinOpTy::AddEq,
				OpTy::SubEq(_) => BinOpTy::SubEq,
				OpTy::MulEq(_) => BinOpTy::MulEq,
				OpTy::DivEq(_) => BinOpTy::DivEq,
				OpTy::RemEq(_) => BinOpTy::RemEq,
				OpTy::AndEq(_) => BinOpTy::AndEq,
				OpTy::OrEq(_) => BinOpTy::OrEq,
				OpTy::XorEq(_) => BinOpTy::XorEq,
				OpTy::LShiftEq(_) => BinOpTy::LShiftEq,
				OpTy::RShiftEq(_) => BinOpTy::RShiftEq,
				OpTy::EqEq(_) => BinOpTy::EqEq,
				OpTy::NotEq(_) => BinOpTy::NotEq,
				OpTy::AndAnd(_) => BinOpTy::AndAnd,
				OpTy::OrOr(_) => BinOpTy::OrOr,
				OpTy::XorXor(_) => BinOpTy::XorXor,
				OpTy::Gt(_) => BinOpTy::Gt,
				OpTy::Lt(_) => BinOpTy::Lt,
				OpTy::Ge(_) => BinOpTy::Ge,
				OpTy::Le(_) => BinOpTy::Le,
				_ => unreachable!("[Op::to_bin_op] Given a `ty` which should not be handled here.")
			};

		BinOp {
			span: self.span,
			ty,
		}
	}
}

/// An open grouping of items.
#[derive(Debug, PartialEq)]
enum Group {
	/// A parenthesis group.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis.
	/// - `1` - The span of the opening parenthesis.
	Paren(bool, Span),
	/// A function call.
	///
	/// - `0` - The number of expressions to consume for the arguments.
	/// - `1` - The span of the opening parenthesis.
	FnCall(usize, Span),
	/// An index operator.
	///
	/// - `0` - Whether this group has an inner expression within the brackets.
	/// - `1` - The span of the opening bracket.
	Index(bool, Span),
	/// An initializer list.
	///
	/// - `0` - The number of expressions to consume for the arguments.
	/// - `1` - The span of the opening brace.
	Init(usize, Span),
	/// An array constructor.
	///
	/// - `0` - The number of expressions to consume for the arguments.
	/// - `1` - The span of the opening parenthesis.
	ArrInit(usize, Span),
	/// A general list **outside** of function calls, initializer lists and array constructors.
	///
	/// - `0` - The number of expressions to consume for the arguments.
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

/// The implementation of a shunting yard-based parser.
struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Node, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The top-most entry is the group being currently parsed.
	groups: Vec<Group>,
	/// The start position of the first item in this expression.
	start_position: usize,
	/// The behavioural mode of the parser.
	mode: Mode,

	/// Syntax diagnostics encountered during the parser execution.
	syntax_diags: Vec<Syntax>,
	/// Semantic diagnostics encountered during the parser execution; (these will only be related to macros).
	semantic_diags: Vec<Semantic>,

	/// Syntax highlighting tokens created during the parser execution.
	syntax_tokens: Vec<SyntaxToken>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Op) {
		if let OpTy::TernaryC(_) = op.ty {
			// This completes the ternary.
			match self.groups.pop() {
				Some(group) => match group {
					Group::Ternary => {}
					_ => unreachable!("Should be in ternary group"),
				},
				None => unreachable!("Should be in ternary group"),
			};
		}

		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			match back.ty {
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				OpTy::ParenStart
				| OpTy::IndexStart
				| OpTy::FnCallStart
				| OpTy::InitStart
				| OpTy::ArrInitStart => break,
				_ => {}
			}

			match (&op.ty, &back.ty) {
				// This is done to make `ObjAccess` right-associative.
				(OpTy::ObjAccess(_), OpTy::ObjAccess(_)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					break;
				}
				// These are done to make the ternary operator right-associate correctly. This is slightly more
				// complex since the ternary is made of two distinct "operators", the `?` and `:`.
				(OpTy::TernaryC(_), OpTy::TernaryQ(_)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					break;
				}
				(OpTy::TernaryC(_), OpTy::TernaryC(_)) => {
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
					continue;
				}
				(_, _) => {}
			}

			// TODO: Implement same precedence check for binary operators as in the conditional expression parser.
			// This is strictly not necessary since we won't ever be mathematically evaluating expressions, but it
			// would be a good idea nonetheless.
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
	fn collapse_paren(&mut self, group: Group, end_span: Span) {
		if let Group::Paren(has_inner, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnCallStart => unreachable!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Paren)!"),
						OpTy::IndexStart => unreachable!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Paren)!"),
						OpTy::InitStart => unreachable!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Paren)!"),
						OpTy::ArrInitStart => unreachable!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Paren)!"),
						_ => {}
					}
				}

				if let OpTy::ParenStart = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::Paren(has_inner, l_paren, end_span),
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
	/// `end_span` is the span which marks the end of this function call group. It may be the span of the `)`
	/// token, or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_fn(&mut self, group: Group, end_span: Span) {
		if let Group::FnCall(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => unreachable!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Fn)!"),
						OpTy::IndexStart => unreachable!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Fn)!"),
						OpTy::InitStart => unreachable!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Fn)!"),
						OpTy::ArrInitStart => unreachable!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Fn)!"),
						_ => {}
					}
				}

				if let OpTy::FnCallStart = op.ty {
					// The first expression will always be the `Expr::Ident` containing the function identifier,
					// hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::FnCall(count + 1, l_paren, end_span),
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
	fn collapse_index(&mut self, group: Group, end_span: Span) {
		if let Group::Index(contains_i, l_bracket) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op .ty{
						OpTy::ParenStart => unreachable!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Index)!"),
						OpTy::FnCallStart => unreachable!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Index)!"),
						OpTy::InitStart=> unreachable!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Index)!"),
						OpTy::ArrInitStart => unreachable!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Index)!"),
						_ => {}
					}
				}

				if let OpTy::IndexStart = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_bracket.start, end_span.end),
						ty: OpTy::Index(contains_i, l_bracket, end_span),
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
	fn collapse_init(&mut self, group: Group, end_span: Span) {
		if let Group::Init(count, l_brace) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => unreachable!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Init)!"),
						OpTy::IndexStart => unreachable!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Init)!"),
						OpTy::FnCallStart => unreachable!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Init)!"),
						OpTy::ArrInitStart => unreachable!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Init)!"),
						_ => {}
					}
				}

				if let OpTy::InitStart = op.ty {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_brace.start, end_span.end),
						ty: OpTy::Init(count, l_brace, end_span),
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
	fn collapse_arr_init(&mut self, group: Group, end_span: Span) {
		if let Group::ArrInit(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => unreachable!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::ArrInit)!"),
						OpTy::IndexStart => unreachable!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::ArrInit)!"),
						OpTy::FnCallStart => unreachable!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::ArrInit)!"),
						OpTy::InitStart => unreachable!("Mismatch between operator stack (Op::InitStart) and group stack (Group::ArrInit)!"),
						_ => {}
					}
				}

				if let OpTy::ArrInitStart = op.ty {
					// The first expression will always be the `Expr::Index` containing the identifier/item and the
					// array index, hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						span: Span::new(l_paren.start, end_span.end),
						ty: OpTy::ArrInit(count + 1, l_paren, end_span),
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
						OpTy::FnCallStart => unreachable!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::List)!"),
						OpTy::InitStart => unreachable!("Mismatch between operator stack (Op::InitStart) and group stack (Group::List)!"),
						OpTy::ArrInitStart => unreachable!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::List)!"),
						_ => {}
					}
				}

				// Lists don't have a starting delimiter, so we consume until we encounter another group-start
				// delimiter (and if there are none, we just end up consuming the rest of the operator stack).
				// Since lists cannnot exist within a `Group::FnCall|Init|ArrInit`, we don't check for those start
				// delimiters.
				match op.ty {
					OpTy::ParenStart | OpTy::IndexStart => break,
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

	/// Registers the end of a parenthesis, function call or array constructor group, popping any operators until
	/// the start of the group is reached.
	fn end_paren_fn(&mut self, end_span: Span) -> Result<(), ()> {
		let current_group = match self.groups.last() {
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
					'inner: while let Some(current_group) = self.groups.last() {
						match current_group {
							Group::Init(_, _) => {
								let current_group = self.groups.pop().unwrap();
								self.collapse_init(
									current_group,
									Span::new(
										end_span.end_at_previous().end,
										end_span.end_at_previous().end,
									),
								);
							}
							Group::Index(_, _) => {
								let current_group = self.groups.pop().unwrap();
								self.collapse_index(
									current_group,
									end_span.start_zero_width(),
								)
							}
							Group::List(_, _) => {
								let current_group = self.groups.pop().unwrap();

								self.collapse_list(
									current_group,
									end_span.end_at_previous().end,
								);
							}
							Group::Ternary => {
								'tern: while let Some(op) =
									self.operators.back()
								{
									if let OpTy::TernaryQ(_) = op.ty {
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

								self.groups.pop();
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

		let group = self.groups.pop().unwrap();
		match group {
			Group::Paren(_, _) => self.collapse_paren(group, end_span),
			Group::FnCall(_, _) => self.collapse_fn(group, end_span),
			Group::ArrInit(_, _) => self.collapse_arr_init(group, end_span),
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
	fn end_index(&mut self, end_span: Span) -> Result<(), ()> {
		let current_group = match self.groups.last() {
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
				'inner: while let Some(current_group) = self.groups.last() {
					match current_group {
						Group::Paren(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_paren(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::FnCall(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_fn(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::Init(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_init(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::ArrInit(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_arr_init(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::Ternary => {
							'tern: while let Some(op) = self.operators.back() {
								if let OpTy::TernaryQ(_) = op.ty {
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

							self.groups.pop();
						}
						Group::List(_, _) => {
							let current_group = self.groups.pop().unwrap();
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

		let group = self.groups.pop().unwrap();
		self.collapse_index(group, end_span);
		Ok(())
	}

	/// Registers the end of an initializer list group, popping any operators until the start of the group is
	/// reached.
	fn end_init(&mut self, end_span: Span) -> Result<(), ()> {
		let current_group = match self.groups.last() {
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
				'inner: while let Some(current_group) = self.groups.last() {
					match current_group {
						Group::Paren(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_paren(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::Index(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_index(
								current_group,
								end_span.start_zero_width(),
							);
						}
						Group::FnCall(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_fn(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::ArrInit(_, _) => {
							let current_group = self.groups.pop().unwrap();
							self.collapse_arr_init(
								current_group,
								Span::new(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								),
							);
						}
						Group::Ternary => {
							'tern: while let Some(op) = self.operators.back() {
								if let OpTy::TernaryQ(_) = op.ty {
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

							self.groups.pop();
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

		let group = self.groups.pop().unwrap();
		self.collapse_init(group, end_span);
		Ok(())
	}

	/// Registers the end of a sub-expression, popping any operators until the start of the group (or expression)
	/// is reached.
	fn register_arity_argument(&mut self, end_span: Span) {
		while let Some(group) = self.groups.last_mut() {
			match group {
				Group::FnCall(count, _)
				| Group::Init(count, _)
				| Group::ArrInit(count, _) => {
					// We want to move all existing operators up to the function call, initializer list, or array
					// constructor start delimiter to the stack, to clear it for the next expression.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						match back.ty {
							OpTy::FnCallStart
							| OpTy::InitStart
							| OpTy::ArrInitStart => break,
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
					let group = self.groups.pop().unwrap();
					self.collapse_paren(group, end_span);
				}
				Group::Index(_, _) => {
					let group = self.groups.pop().unwrap();
					self.collapse_index(group, end_span);
				}
				Group::Ternary => {
					'tern: while let Some(op) = self.operators.back() {
						if let OpTy::TernaryQ(_) = op.ty {
							let moved = self.operators.pop_back().unwrap();
							self.stack.push_back(Either::Right(moved));
							break 'tern;
						} else {
							let moved = self.operators.pop_back().unwrap();
							self.stack.push_back(Either::Right(moved));
						}
					}

					self.groups.pop();
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
		self.groups.push(Group::List(
			if self.stack.is_empty() && self.operators.is_empty() {
				0
			} else {
				1
			},
			self.start_position,
		))
	}

	/// Sets the toggle on the last operator that it has a right-hand side operand, (if applicable).
	fn set_op_rhs_toggle(&mut self) {
		if let Some(op) = self.operators.back_mut() {
			match &mut op.ty {
				OpTy::Add(b)
				| OpTy::Sub(b)
				| OpTy::Mul(b)
				| OpTy::Div(b)
				| OpTy::Rem(b)
				| OpTy::And(b)
				| OpTy::Or(b)
				| OpTy::Xor(b)
				| OpTy::LShift(b)
				| OpTy::RShift(b)
				| OpTy::Eq(b)
				| OpTy::AddEq(b)
				| OpTy::SubEq(b)
				| OpTy::MulEq(b)
				| OpTy::DivEq(b)
				| OpTy::RemEq(b)
				| OpTy::AndEq(b)
				| OpTy::OrEq(b)
				| OpTy::XorEq(b)
				| OpTy::LShiftEq(b)
				| OpTy::RShiftEq(b)
				| OpTy::EqEq(b)
				| OpTy::NotEq(b)
				| OpTy::AndAnd(b)
				| OpTy::OrOr(b)
				| OpTy::XorXor(b)
				| OpTy::Gt(b)
				| OpTy::Lt(b)
				| OpTy::Ge(b)
				| OpTy::Le(b)
				| OpTy::AddPre(b)
				| OpTy::SubPre(b)
				| OpTy::Neg(b)
				| OpTy::Flip(b)
				| OpTy::Not(b)
				| OpTy::TernaryQ(b)
				| OpTy::TernaryC(b)
				| OpTy::ObjAccess(b) => *b = true,
				_ => {}
			}
		}
		if let Some(group) = self.groups.last_mut() {
			match group {
				Group::Paren(b, _) | Group::Index(b, _) => *b = true,
				_ => {}
			}
		}
	}

	/// Returns whether we have just started to parse a parenthesis group, i.e. `..(<HERE>`.
	fn just_started_paren(&self) -> bool {
		if let Some(current_group) = self.groups.last() {
			match current_group {
				Group::Paren(has_inner, _) => *has_inner == false,
				_ => false,
			}
		} else {
			false
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
				OpTy::FnCallStart | OpTy::ArrInitStart => op.span,
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
		if let Some(current_group) = self.groups.last() {
			match current_group {
				Group::Init(count, _) => *count == 0,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we are currently within a ternary expression group.
	fn is_in_ternary(&self) -> bool {
		if let Some(current_group) = self.groups.last() {
			match current_group {
				Group::Ternary => true,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we are currently in a function call, initializer list, array constructor, or general list
	/// group.
	fn is_in_variable_arg_group(&self) -> bool {
		if let Some(current_group) = self.groups.last() {
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

	/// Pushes a syntax highlighting token over the given span.
	fn colour<'a, P: super::TokenStreamProvider<'a>>(
		&mut self,
		walker: &Walker<'a, P>,
		span: Span,
		token: SyntaxType,
	) {
		// When we are within a macro, we don't want to produce syntax tokens.
		if walker.streams.len() == 1 {
			self.syntax_tokens.push(SyntaxToken {
				ty: token,
				modifiers: SyntaxModifiers::empty(),
				span,
			});
		}
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse<'a, P: super::TokenStreamProvider<'a>>(
		&mut self,
		walker: &mut Walker<'a, P>,
		end_tokens: &[Token],
	) {
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
					// TODO: Register syntax error if previous was operator.
					break 'main;
				}
			}

			match token {
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

					match Lit::parse(token, span) {
						Ok(l) => self.stack.push_back(Either::Left(Node {
							ty: NodeTy::Lit(l),
							span,
						})),
						Err((l, d)) => {
							self.stack.push_back(Either::Left(Node {
								ty: NodeTy::Lit(l),
								span,
							}));
							self.syntax_diags.push(d);
						}
					}

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					state = State::AfterOperand;

					can_start = Start::None;

					self.set_op_rhs_toggle();

					self.colour(
						walker,
						span,
						match token {
							Token::Num { .. } => SyntaxType::Number,
							Token::Bool(_) => SyntaxType::Boolean,
							_ => unreachable!(),
						},
					);
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
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundOperandAfterOperand(
								self.get_previous_span().unwrap(),
								span,
							),
						));
						break 'main;
					}
					arity_state = Arity::PotentialEnd;

					match Lit::parse(token, span) {
						Ok(l) => self.stack.push_back(Either::Left(Node {
							ty: NodeTy::Lit(l),
							span,
						})),
						Err((l, d)) => {
							self.stack.push_back(Either::Left(Node {
								ty: NodeTy::Lit(l),
								span,
							}));
							self.syntax_diags.push(d);
						}
					}

					can_start = Start::None;

					self.colour(
						walker,
						span,
						match token {
							Token::Num { .. } => SyntaxType::Number,
							Token::Bool(_) => SyntaxType::Boolean,
							_ => unreachable!(),
						},
					);

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
						ty: NodeTy::Ident(Ident {
							name: s.clone(),
							span,
						}),
						span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + i` instead of `..10 i`.
					state = State::AfterOperand;

					// After an identifier, we may start a function call, or eventually an array constructor.
					can_start = Start::FnOrArr;

					self.set_op_rhs_toggle();

					self.colour(walker, span, SyntaxType::UncheckedIdent);
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
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundOperandAfterOperand(
								self.get_previous_span().unwrap(),
								span,
							),
						));
						break 'main;
					}
					arity_state = Arity::PotentialEnd;

					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Ident(Ident {
							name: s.clone(),
							span,
						}),
						span,
					}));

					// After an identifier, we may start a function call.
					can_start = Start::FnOrArr;

					self.colour(walker, span, SyntaxType::UncheckedIdent);

					// We don't change state since even though we found an operand instead of an operator, after
					// this operand we will still be expecting an operator.
				}
				Token::Op(op) if state == State::Operand => {
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == lexer::OpTy::Eq
					{
						break 'main;
					}

					match op {
						lexer::OpTy::Sub
						| lexer::OpTy::Not
						| lexer::OpTy::Flip
						| lexer::OpTy::AddAdd
						| lexer::OpTy::SubSub => {
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
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::InvalidPrefixOperator(span),
							));
							break 'main;
						}
					}

					match op {
						// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
						// state since after a prefix operator, we are still looking for an operand atom.
						lexer::OpTy::Sub => self.push_operator(Op {
							span,
							ty: OpTy::Neg(false),
						}),
						lexer::OpTy::Not => self.push_operator(Op {
							span,
							ty: OpTy::Not(false),
						}),
						lexer::OpTy::Flip => self.push_operator(Op {
							span,
							ty: OpTy::Flip(false),
						}),
						lexer::OpTy::AddAdd => self.push_operator(Op {
							span,
							ty: OpTy::AddPre(false),
						}),
						lexer::OpTy::SubSub => self.push_operator(Op {
							span,
							ty: OpTy::SubPre(false),
						}),
						_ => {
							unreachable!()
						}
					}

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Operator);
				}
				Token::Op(op) if state == State::AfterOperand => {
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == lexer::OpTy::Eq
					{
						break 'main;
					}

					match op {
						lexer::OpTy::Flip | lexer::OpTy::Not => {
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::InvalidBinOrPostOperator(span),
							));
							break 'main;
						}
						// These operators are postfix operators. We don't switch state since after a postfix
						// operator, we are still looking for a binary operator or the end of expression, i.e.
						// `..i++ - i` rather than `..i++ i`.
						lexer::OpTy::AddAdd => {
							self.push_operator(Op {
								span,
								ty: OpTy::AddPost,
							});
						}
						lexer::OpTy::SubSub => {
							self.push_operator(Op {
								span,
								ty: OpTy::SubPost,
							});
						}
						// Any other operators can be part of a binary expression. We switch state since after a
						// binary operator we are expecting an operand.
						_ => {
							self.push_operator(Op::from_token(*op, span));
							state = State::Operand;
						}
					}

					arity_state = Arity::Operator;

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Operator);
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

					self.operators.push_back(Op {
						span,
						ty: OpTy::ParenStart,
					});
					self.groups.push(Group::Paren(false, span));

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);

					// We don't switch state since after a `(`, we are expecting an operand, i.e.
					// `..+ ( 1 *` rather than `..+ ( *`.
				}
				Token::LParen if state == State::AfterOperand => {
					if can_start == Start::FnOrArr {
						// We have `ident(` which makes this a function call.
						self.operators.push_back(Op {
							span,
							ty: OpTy::FnCallStart,
						});
						self.groups.push(Group::FnCall(0, span));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `fn( 1..` rather than`fn( +..`.1
						state = State::Operand;

						// We unset this flag, since this flag is only used to detect the `ident` -> `(` token
						// chain.
						can_start = Start::None;

						just_started_arity_group = true;
					} else if can_start == Start::ArrInit {
						// We have `ident[...](` which makes this an array constructor.
						self.operators.push_back(Op {
							span,
							ty: OpTy::ArrInitStart,
						});
						self.groups.push(Group::ArrInit(0, span));

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
								self.syntax_diags.push(Syntax::Expr(
									ExprDiag::FoundOperandAfterOperand(
										self.get_previous_span().unwrap(),
										span,
									),
								));
							}
							break 'main;
						}

						self.set_op_rhs_toggle();

						self.operators.push_back(Op {
							span,
							ty: OpTy::ParenStart,
						});
						self.groups.push(Group::Paren(false, span));

						state = State::Operand;

						can_start = Start::None;
					}
					arity_state = Arity::Operator;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::RParen if state == State::AfterOperand => {
					if !self.just_started_fn_arr_init()
						&& self.is_in_variable_arg_group()
					{
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					match self.end_paren_fn(span) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);

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
					let just_started_paren = self.just_started_paren();
					let just_started_fn_arr_init =
						self.just_started_fn_arr_init();

					match self.end_paren_fn(span) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					if just_started_paren {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundEmptyParens(Span::new(
								prev_op_span.unwrap().start,
								span.end,
							)),
						));
					} else if just_started_fn_arr_init {
					} else {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundRParenInsteadOfOperand(
								prev_op_span.unwrap(),
								span,
							),
						))
					}

					state = State::AfterOperand;

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::LBracket if state == State::AfterOperand => {
					// We switch state since after a `[`, we are expecting an operand, i.e.
					// `i[5 +..` rather than `i[+..`.
					self.operators.push_back(Op {
						span,
						ty: OpTy::IndexStart,
					});
					self.groups.push(Group::Index(false, span));

					state = State::Operand;

					arity_state = Arity::Operator;

					can_start = Start::EmptyIndex;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::LBracket if state == State::Operand => {
					if self.mode != Mode::TakeOneUnit {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundLBracketInsteadOfOperand(
								self.get_previous_span(),
								span,
							),
						));
					}
					break 'main;
				}
				Token::RBracket if state == State::AfterOperand => {
					// We don't switch state since after a `]`, we are expecting an operator, i.e.
					// `..] + 5` instead of `..] 5`.
					match self.end_index(span) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					// After an index `ident[..]` we may have an array constructor.
					can_start = Start::ArrInit;

					arity_state = Arity::PotentialEnd;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::RBracket if state == State::Operand => {
					if can_start == Start::EmptyIndex {
						match self.end_index(span) {
							Ok(_) => {}
							Err(_) => {
								break 'main;
							}
						}
					} else {
						let prev_op_span = self.get_previous_span();

						match self.end_index(span) {
							Ok(_) => {}
							Err(_) => {
								break 'main;
							}
						}

						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundRBracketInsteadOfOperand(
								prev_op_span.unwrap(),
								span,
							),
						));
					}
					// We switch state since after a `]`, we are expecting an operator, i.e.
					// `..[] + 5` rather than `..[] 5`.
					state = State::AfterOperand;

					arity_state = Arity::PotentialEnd;

					self.colour(walker, span, SyntaxType::Punctuation);
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

					self.operators.push_back(Op {
						span,
						ty: OpTy::InitStart,
					});
					self.groups.push(Group::Init(0, span));

					can_start = Start::None;

					just_started_arity_group = true;

					self.colour(walker, span, SyntaxType::Punctuation);

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
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::FoundOperandAfterOperand(
									self.get_previous_span().unwrap(),
									span,
								),
							));
						}
						break 'main;
					}
					arity_state = Arity::Operator;

					self.set_op_rhs_toggle();

					self.operators.push_back(Op {
						span,
						ty: OpTy::InitStart,
					});
					self.groups.push(Group::Init(0, span));

					state = State::Operand;

					can_start = Start::None;

					just_started_arity_group = true;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::RBrace if state == State::AfterOperand => {
					if self.is_in_variable_arg_group() {
						self.register_arity_argument(span.start_zero_width());
					}
					arity_state = Arity::PotentialEnd;

					match self.end_init(span) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);

					// We don't switch state since after a `}`, we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
				}
				Token::RBrace if state == State::Operand => {
					if self.is_in_variable_arg_group()
						&& !just_started_arity_group
					{
						self.register_arity_argument(span.start_zero_width());
					}
					let prev_arity = arity_state;
					arity_state = Arity::PotentialEnd;

					let prev_op_span = self.get_previous_span();
					let empty_group = self.just_started_init();

					// This is valid, i.e. `{}`, or `{1, }`.
					match self.end_init(span) {
						Ok(_) => {}
						Err(_) => {
							break 'main;
						}
					}

					if !empty_group && prev_arity != Arity::PotentialEnd {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundRBraceInsteadOfOperand(
								prev_op_span.unwrap(),
								span,
							),
						));
					}

					// We switch state since after an init list we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
					state = State::AfterOperand;

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);
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
						span,
						ty: NodeTy::Separator,
					}));

					// We switch state since after a comma (which delineates an expression), we're effectively
					// starting a new expression which must start with an operand, i.e.
					// `.., 5 + 6` instead of `.., + 6`.
					state = State::Operand;

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);
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
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundCommaInsteadOfOperand(
								self.get_previous_span().unwrap(),
								span,
							),
						));
					} else if !self.stack.is_empty() {
						if let Some(Either::Left(Node {
							span: _,
							ty: NodeTy::Separator,
						})) = self.stack.back()
						{
						} else {
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::FoundCommaInsteadOfOperand(
									self.get_previous_span().unwrap(),
									span,
								),
							));
						}
					}

					if can_start == Start::EmptyIndex {
						match self.groups.last_mut() {
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
						span,
						ty: NodeTy::Separator,
					}));

					can_start = Start::None;

					self.colour(walker, span, SyntaxType::Punctuation);
				}
				Token::Dot if state == State::AfterOperand => {
					// We don't need to consider arity because a dot after an operand will always be a valid object
					// access notation, and in the alternate branch we don't recover from the error.

					self.push_operator(Op {
						span,
						ty: OpTy::ObjAccess(false),
					});

					// We switch state since after an object access we are execting an operand, such as:
					// `foo. bar()`.
					state = State::Operand;
					
					can_start = Start::None;

					arity_state = Arity::Operator;

					self.colour(walker, span, SyntaxType::Operator);
				}
				Token::Dot if state == State::Operand => {
					// We have encountered something like: `foo + . ` or `foo.bar(). . `.
					//
					// We do not recover from this error because we currently mandate that the `ExprTy::ObjAccess`
					// node has a left-hand side.
					//
					// MAYBE: Should we make this a recoverable situation? (If so we need to consider arity)

					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundDotInsteadOfOperand(
							self.get_previous_span(),
							span,
						),
					));
					break 'main;
				}
				Token::Question => {
					if state == State::Operand {
						// We have encountered something like: `foo + ?`.
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundQuestionInsteadOfOperand(
								self.get_previous_span(),
								span,
							),
						));
					}

					self.push_operator(Op {
						span,
						ty: OpTy::TernaryQ(false),
					});
					self.groups.push(Group::Ternary);

					// We switch state since after the `?` we are expecting an operand, such as:
					// `foo ? bar`.
					state = State::Operand;

					can_start = Start::None;

					arity_state = Arity::Operator;

					self.colour(walker, span, SyntaxType::Operator);
				}
				Token::Colon => {
					if !self.is_in_ternary() {
						break 'main;
					}

					if state == State::Operand {
						// We have encountered something like: `foo ? a + :`.
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundColonInsteadOfOperand(
								self.get_previous_span(),
								span,
							),
						));
					}

					self.push_operator(Op {
						span,
						ty: OpTy::TernaryC(false),
					});

					// We switch state since after the `:` we are expecting an operand, such as:
					// `foo ? bar : baz2`.
					state = State::Operand;

					can_start = Start::None;

					arity_state = Arity::Operator;

					self.colour(walker, span, SyntaxType::Operator);
				}
				_ => {
					// We have encountered an unexpected token that's not allowed to be part of an expression.
					self.syntax_diags
						.push(Syntax::Expr(ExprDiag::FoundInvalidToken(span)));
					break 'main;
				}
			}

			// Reset the flag. This is a separate statement because otherwise this assignment would have to be in
			// _every_ single branch other than the l_paren branch and this is just cleaner/more maintainable.
			match token {
				Token::LParen | Token::LBrace => {}
				_ => just_started_arity_group = false,
			}

			walker.advance_expr_parser(
				&mut self.syntax_diags,
				&mut self.semantic_diags,
				&mut self.syntax_tokens,
			);
		}

		// Close any open groups. Any groups still open must be missing a closing delimiter.
		if !self.groups.is_empty() {
			// The end position of this expression will be the end position of the last parsed item.
			let group_end = self.get_previous_span().unwrap().end_zero_width();

			// We don't take ownership of the groups because the individual `collapse_*()` methods do that.
			while let Some(group) = self.groups.last_mut() {
				match group {
					Group::FnCall(_, _)
					| Group::Init(_, _)
					| Group::ArrInit(_, _) => {
						if !just_started_arity_group {
							self.register_arity_argument(group_end);
						}
					}
					// A list always goes to the end of the expression, so we never increment the counter in the
					// main loop for the final expression, hence we must always do it here.
					Group::List(count, _) => *count += 1,
					_ => {}
				}

				// After the first iteration, we reset to false because if there are more groups, then they
				// definitely have at least one argument.
				just_started_arity_group = false;

				let group = self.groups.pop().unwrap();
				match group {
					Group::Paren(_, l_paren) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedParens(l_paren, group_end),
						));
						self.collapse_paren(group, group_end);
					}
					Group::Index(_, l_bracket) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedIndexOperator(
								l_bracket, group_end,
							),
						));
						self.collapse_index(group, group_end)
					}
					Group::FnCall(_, l_paren) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedFunctionCall(l_paren, group_end),
						));
						self.collapse_fn(group, group_end)
					}
					Group::Init(_, l_brace) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedInitializerList(
								l_brace, group_end,
							),
						));
						self.collapse_init(group, group_end)
					}
					Group::ArrInit(_, l_paren) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedArrayConstructor(
								l_paren, group_end,
							),
						));
						self.collapse_arr_init(group, group_end)
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
		if self.stack.is_empty() {
			return None;
		}

		let mut stack: VecDeque<Expr> = VecDeque::new();
		let pop_back = |stack: &mut VecDeque<Expr>| stack.pop_back().unwrap();

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the n-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(item) = self.stack.pop_front() {
			match item {
				Either::Left(node) => match node.ty {
					NodeTy::Lit(lit) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Lit(lit),
					}),
					NodeTy::Ident(ident) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Ident(ident),
					}),
					NodeTy::Separator => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Separator,
					}),
				},
				Either::Right(op) => match op.ty {
					OpTy::AddPre(has_operand) => {
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
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Add,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::SubPre(has_operand) => {
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
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Sub,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::AddPost => {
						let expr = pop_back(&mut stack);
						let span = Span::new(expr.span.start, op.span.end);

						stack.push_back(Expr {
							span,
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								op: PostOp {
									ty: PostOpTy::Add,
									span: op.span,
								},
							},
						});
					}
					OpTy::SubPost => {
						let expr = pop_back(&mut stack);
						let span = Span::new(expr.span.start, op.span.end);

						stack.push_back(Expr {
							span,
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								op: PostOp {
									ty: PostOpTy::Sub,
									span: op.span,
								},
							},
						});
					}
					OpTy::Neg(has_operand) => {
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
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Neg,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Flip(has_operand) => {
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
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Flip,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Not(has_operand) => {
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
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Not,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::TernaryQ(has_rhs) => {
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
								true_: true_.map(|e| Box::from(e)),
								false_: None,
							},
							span,
						});
					}
					OpTy::TernaryC(has_rhs) => {
						let last = pop_back(&mut stack);
						let (prev, false_) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let (cond, true_) = match prev.ty {
							ExprTy::Ternary {
								cond,
								true_,
								false_: _,
							} => (cond, true_),
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
								true_,
								false_: false_.map(|e| Box::from(e)),
							},
							span,
						});
					}
					OpTy::Paren(has_inner, _l_paren, _end) => {
						let expr = if has_inner {
							Some(pop_back(&mut stack))
						} else {
							None
						};

						stack.push_back(Expr {
							span: op.span,
							ty: ExprTy::Parens {
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::FnCall(count, l_paren, end) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						// Get the identifier (which is the first expression).
						let ident = match temp.pop_front().unwrap().ty {
							ExprTy::Ident(ident) => ident,
							_ => unreachable!("The first expression of a function call operator is not an identifier!")
						};
						let args = process_fn_arr_constructor_args(
							temp,
							&mut self.syntax_diags,
							l_paren,
						);

						stack.push_back(Expr {
							span: Span::new(ident.span.start, end.end),
							ty: ExprTy::FnCall { ident, args },
						});
					}
					OpTy::Index(contains_i, _l_bracket, end) => {
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
								i,
							},
						});
					}
					OpTy::Init(count, l_brace, _end) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						let args = process_initializer_list_args(
							temp,
							&mut self.syntax_diags,
							l_brace,
						);

						stack.push_back(Expr {
							ty: ExprTy::InitList { args },
							span: op.span,
						});
					}
					OpTy::ArrInit(count, l_paren, end) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						// Get the index operator (which is the first expression).
						let arr = temp.pop_front().unwrap();
						match arr.ty {
							ExprTy::Index { .. } => {}
							_ => {
								unreachable!("The first expression of an array constructor operator is not an `Expr::Index`!");
							}
						}

						let args = process_fn_arr_constructor_args(
							temp,
							&mut self.syntax_diags,
							l_paren,
						);

						stack.push_back(Expr {
							span: Span::new(arr.span.start, end.end),
							ty: ExprTy::ArrConstructor {
								arr: Box::from(arr),
								args,
							},
						});
					}
					OpTy::List(count) => {
						let mut temp = VecDeque::new();
						for _ in 0..count {
							temp.push_front(pop_back(&mut stack));
						}

						let args =
							process_list_args(temp, &mut self.syntax_diags);

						stack.push_back(Expr {
							ty: ExprTy::List { items: args },
							span: op.span,
						});
					}
					OpTy::ObjAccess(has_rhs) => {
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
								leaf: right.map(|e| Box::from(e)),
							},
							span,
						});
					}
					OpTy::Add(has_rhs)
					| OpTy::Sub(has_rhs)
					| OpTy::Mul(has_rhs)
					| OpTy::Div(has_rhs)
					| OpTy::Rem(has_rhs)
					| OpTy::And(has_rhs)
					| OpTy::Or(has_rhs)
					| OpTy::Xor(has_rhs)
					| OpTy::LShift(has_rhs)
					| OpTy::RShift(has_rhs)
					| OpTy::EqEq(has_rhs)
					| OpTy::NotEq(has_rhs)
					| OpTy::Gt(has_rhs)
					| OpTy::Lt(has_rhs)
					| OpTy::Ge(has_rhs)
					| OpTy::Le(has_rhs)
					| OpTy::AndAnd(has_rhs)
					| OpTy::OrOr(has_rhs)
					| OpTy::XorXor(has_rhs)
					| OpTy::Eq(has_rhs)
					| OpTy::AddEq(has_rhs)
					| OpTy::SubEq(has_rhs)
					| OpTy::MulEq(has_rhs)
					| OpTy::DivEq(has_rhs)
					| OpTy::RemEq(has_rhs)
					| OpTy::AndEq(has_rhs)
					| OpTy::OrEq(has_rhs)
					| OpTy::XorEq(has_rhs)
					| OpTy::LShiftEq(has_rhs)
					| OpTy::RShiftEq(has_rhs) => {
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
						let bin_op = op.to_bin_op();

						stack.push_back(Expr {
							ty: ExprTy::Binary {
								left: Box::from(left),
								op: bin_op,
								right: right.map(|e| Box::from(e)),
							},
							span,
						});
					}
					_ => {
						unreachable!("Invalid operator {op:?} in shunting yard stack. This operator should never be present in the final RPN stack.");
					}
				},
			}
		}

		if stack.len() > 1 {
			let expr = pop_back(&mut stack);
			stack.push_back(expr);
		}

		if stack.len() != 1 {
			unreachable!("After processing the shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap())
	}
}

fn process_fn_arr_constructor_args(
	mut list: VecDeque<Expr>,
	diags: &mut Vec<Syntax>,
	opening_delim: Span,
) -> Vec<Expr> {
	let mut args = Vec::new();

	enum Prev {
		None,
		Item(Span),
		Comma(Span),
	}
	let mut previous = Prev::None;
	while let Some(arg) = list.pop_front() {
		match arg.ty {
			ExprTy::Separator => {
				match previous {
					Prev::Comma(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedArgAfterComma(Span::new_between(
								span, arg.span,
							)),
						));
					}
					Prev::None => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedArgBetweenParenComma(
								Span::new_between(opening_delim, arg.span),
							),
						));
					}
					_ => {}
				}
				previous = Prev::Comma(arg.span);
			}
			_ => {
				match previous {
					Prev::Item(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedCommaAfterArg(Span::new_between(
								span, arg.span,
							)),
						));
					}
					_ => {}
				}
				previous = Prev::Item(arg.span);
				args.push(arg);
			}
		}
	}

	if let Prev::Comma(span) = previous {
		diags.push(Syntax::Expr(ExprDiag::ExpectedArgAfterComma(
			span.next_single_width(),
		)));
	}

	args
}

fn process_initializer_list_args(
	mut list: VecDeque<Expr>,
	diags: &mut Vec<Syntax>,
	opening_delim: Span,
) -> Vec<Expr> {
	let mut args = Vec::new();

	enum Prev {
		None,
		Item(Span),
		Comma(Span),
	}
	let mut previous = Prev::None;
	while let Some(arg) = list.pop_front() {
		match arg.ty {
			ExprTy::Separator => {
				match previous {
					Prev::Comma(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedArgAfterComma(Span::new_between(
								span, arg.span,
							)),
						));
					}
					Prev::None => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedArgBetweenParenComma(
								Span::new_between(opening_delim, arg.span),
							),
						));
					}
					_ => {}
				}
				previous = Prev::Comma(arg.span);
			}
			_ => {
				match previous {
					Prev::Item(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedCommaAfterArg(Span::new_between(
								span, arg.span,
							)),
						));
					}
					_ => {}
				}
				previous = Prev::Item(arg.span);
				args.push(arg);
			}
		}
	}

	args
}

fn process_list_args(
	mut list: VecDeque<Expr>,
	diags: &mut Vec<Syntax>,
) -> Vec<Expr> {
	let mut args = Vec::new();

	enum Prev {
		None,
		Item(Span),
		Comma(Span),
	}
	let mut previous = Prev::None;
	while let Some(arg) = list.pop_front() {
		match arg.ty {
			ExprTy::Separator => {
				match previous {
					Prev::Comma(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedExprAfterComma(
								Span::new_between(span, arg.span),
							),
						));
					}
					Prev::None => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedExprBeforeComma(
								arg.span.previous_single_width(),
							),
						));
					}
					_ => {}
				}
				previous = Prev::Comma(arg.span);
			}
			_ => {
				match previous {
					Prev::Item(span) => {
						diags.push(Syntax::Expr(
							ExprDiag::ExpectedCommaAfterExpr(
								Span::new_between(span, arg.span),
							),
						));
					}
					_ => {}
				}
				previous = Prev::Item(arg.span);
				args.push(arg);
			}
		}
	}

	if let Prev::Comma(span) = previous {
		diags.push(Syntax::Expr(ExprDiag::ExpectedExprAfterComma(
			span.next_single_width(),
		)));
	}

	args
}
