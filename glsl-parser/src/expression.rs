use crate::{
	cst::{
		BinOp, Expr, ExprTy, Ident, List, Lit, PostOp, PostOpTy, PreOp, PreOpTy,
	},
	error::SyntaxErr,
	lexer::{self, Token},
	log,
	parser::Walker,
	span::{span, Span},
	Either,
};
use std::collections::VecDeque;

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

/// Tries to parse an expression beginning at the current position.
pub fn expr_parser(
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
		start_position,
		mode,
		errors: Vec::new(),
	};

	parser.parse(walker, end_tokens);
	(parser.create_ast(), parser.errors)
}

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

/// A node operator.
#[derive(Debug, Clone, PartialEq)]
struct Op {
	ty: OpTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum OpTy {
	/* BINARY OPERATORS */
	/* The `bool` represents whether to consume a node for the right-hand side expression. */
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
	/* PREFIX OPERATORS */
	/* The `bool` represents whether to consume a node for the expression. */
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
	/* TODO */
	/// The `,` token within a variable argument group.
	Comma,
	ObjAccess,
	/* GROUPS */
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis,
	/// - `1` - The span of the opening parenthesis,
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	Paren(bool, Span, Span),
	/// A function call. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the function identifier node, so it
	///   will always be `1` or greater,
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	FnCall(usize, Span, Span),
	/// An index operator. This operator spans from the opening bracket to the closing bracket.
	///
	/// - `0` - Whether to consume a node for the expression within the `[...]` brackets,
	/// - `1` - The span of the opening bracket,
	/// - `2` - The span of the closing bracket. If this is zero-width, that means there is no `]` token present.
	Index(bool, Span, Span),
	/// An initializer list. This operator spans from the opening brace to the closing brace.
	///
	/// - `0` - The number of nodes to consume for the arguments,
	/// - `1` - The span of the opening brace,
	/// - `2` - The span of the closing brace. If this is zero-width, that means there is no `}` token present.
	Init(usize, Span, Span),
	/// An array initializer. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - The number of nodes to consume for the arguments; this includes the index expression node, so it
	///   will always be `1` or greater.
	/// - `1` - The span of the opening parenthesis,
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	ArrInit(usize, Span, Span),
	/// A general list **outside** of function calls, initializer lists and array constructors.
	///
	/// - `0` - The number of nodes to consume for the arguments.
	List(usize),
}

impl Op {
	/// Converts from a lexer `OpTy` token to the `Op2` type used in this expression parser.
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
				lexer::OpTy::Neg
				| lexer::OpTy::Not
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
			OpTy::ObjAccess => 33,
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
			// TODO: Ternary
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
			| OpTy::RShiftEq(_) => 3,
			// These are never directly checked for precedence, but rather have special branches.
			_ => panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
		}
	}
}

impl From<Op> for BinOp {
	fn from(op: Op) -> Self {
		use crate::cst::BinOpTy;
		Self {
			span: op.span,
			ty: match op.ty {
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
				_ => unreachable!("[BinOp::from::<Op>] Given an `op.ty` which should not be handled here.")
			},
		}
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
}

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Expr, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The top-most entry is the group being currently parsed.
	groups: VecDeque<Group>,
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
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if back.ty == OpTy::ParenStart
				|| back.ty == OpTy::IndexStart
				|| back.ty == OpTy::FnCallStart
				|| back.ty == OpTy::InitStart
			{
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				break;
			}

			// This is done to make `ObjAccess` right-associative.
			if op.ty == OpTy::ObjAccess && back.ty == OpTy::ObjAccess {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
				break;
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
	/// Assumes that `self.group.back()` is of type [`Group::Paren`].
	///
	/// `end_span` is the span which marks the end of this parenthesis group. It may be the span of the `)` token,
	/// or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_bracket(&mut self, end_span: Span) {
		let group = self.groups.pop_back().unwrap();

		if let Group::Paren(has_inner, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnCallStart => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Paren)!"),
						OpTy::IndexStart => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Paren)!"),
						OpTy::InitStart => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Paren)!"),
						OpTy::ArrInitStart => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Paren)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::ParenStart {
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
	/// Assumes that `self.group.back()` is of type [`Group::Fn`].
	///
	/// `end_span` is the span which marks the end of this function call group. It may be the span of the `)` token,
	/// or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_fn(&mut self, end_span: Span) {
		let group = self.groups.pop_back().unwrap();

		if let Group::FnCall(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Fn)!"),
						OpTy::IndexStart => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Fn)!"),
						OpTy::InitStart => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Fn)!"),
						OpTy::ArrInitStart => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Fn)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::FnCallStart {
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
	/// Assumes that `self.group.back()` is of type [`Group::Index`].
	///
	/// `end_span` is the span which marks the end of this index group. It may be a span of the `]` token, or it
	/// may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_index(&mut self, end_span: Span) {
		let group = self.groups.pop_back().unwrap();

		if let Group::Index(contains_i, l_bracket) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op .ty{
						OpTy::ParenStart => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Index)!"),
						OpTy::FnCallStart => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Index)!"),
						OpTy::InitStart => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Index)!"),
						OpTy::ArrInitStart => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Index)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::IndexStart {
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
	/// Assumes that `self.group.back()` is of type [`Group::Init`].
	///
	/// `end_span` is the span which marks the end of this initializer list group. It may be a span of the `}`
	/// token, or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_init(&mut self, end_span: Span) {
		let group = self.groups.pop_back().unwrap();

		if let Group::Init(count, l_brace) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::Init)!"),
						OpTy::IndexStart => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Init)!"),
						OpTy::FnCallStart => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::Init)!"),
						OpTy::ArrInitStart => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Init)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::InitStart {
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
	/// Assumes that `self.group.back()` is of type [`Group::ArrInit`].
	///
	/// `end_span` is the span which marks the end of this array constructor group. It may be a span of the `)`
	/// token, or it may be a zero-width span if this group was collapsed without a matching closing delimiter.
	fn collapse_arr_init(&mut self, end_span: Span) {
		let group = self.groups.pop_back().unwrap();

		if let Group::ArrInit(count, l_paren) = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::ParenStart => log!("Mismatch between operator stack (Op::ParenStart) and group stack (Group::ArrInit)!"),
						OpTy::IndexStart => log!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::ArrInit)!"),
						OpTy::FnCallStart => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::ArrInit)!"),
						OpTy::InitStart => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::ArrInit)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::ArrInitStart {
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
	/// Assumes that `self.group.back()` is of type [`Group::List`].
	fn collapse_list(&mut self, span_end: usize) {
		let group = self.groups.pop_back().unwrap();

		if let Group::List(count, start_pos) = group {
			while self.operators.back().is_some() {
				let op = self.operators.back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnCallStart => log!("Mismatch between operator stack (Op::FnCallStart) and group stack (Group::List)!"),
						OpTy::InitStart => log!("Mismatch between operator stack (Op::InitStart) and group stack (Group::List)!"),
						OpTy::ArrInitStart => log!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::List)!"),
						_ => {}
					}
				}

				// Lists don't have a starting delimiter, so we consume until we encounter another group-start
				// delimiter (and if there are none, we just end up consuming the rest of the operator stack).
				// Since lists cannnot exist within a `Group::FnCall|Init|ArrInit`, we don't check for those start
				// delimiters.
				if op.ty == OpTy::ParenStart || op.ty == OpTy::IndexStart {
					self.stack.push_back(Either::Right(Op {
						span: Span::new(start_pos, span_end),
						ty: OpTy::List(count),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
				}
			}
		} else {
			unreachable!()
		}
	}

	/// Registers the end of a bracket, function call or array constructor group, popping any operators until the
	/// start of the group is reached.
	fn end_bracket_fn(&mut self, end_span: Span) -> Result<(), SyntaxErr> {
		let current_group = match self.groups.back() {
			Some(t) => t,
			None => {
				// Since we have no groups, that means we have a lonely `)`. This means we want to stop parsing
				// further tokens.
				log!("Found a `)` delimiter without a starting `(` delimiter!");
				return Err(SyntaxErr::FoundUnmatchedClosingDelim(
					end_span, false,
				));
			}
		};

		match current_group {
			Group::Paren(_, _) | Group::FnCall(_, _) | Group::ArrInit(_, _) => {
			}
			_ => {
				// The current group is not a bracket/function/array constructor group, so we need to check whether
				// there is one at all.

				if self.exists_paren_fn_group() {
					// We have at least one other group to close before we can close the bracket/function/array
					// constructor group.
					'inner: loop {
						let current_group = match self.groups.back() {
							Some(g) => g,
							// PERF: Since we've already checked that there is a `Group::Index`, we know this will
							// never return `None` before we break out of the loop.
							None => break 'inner,
						};

						match current_group {
							Group::Init(_, _) => {
								log!("Unclosed `}}` initializer list found!");
								self.collapse_init(span(
									end_span.end_at_previous().end,
									end_span.end_at_previous().end,
								));
							}
							Group::Index(_, _) => {
								log!("Unclosed `]` index operator found!");
								self.collapse_index(end_span.start_zero_width())
							}
							Group::List(_, _) => self
								.collapse_list(end_span.end_at_previous().end),
							Group::Paren(_, _)
							| Group::FnCall(_, _)
							| Group::ArrInit(_, _) => break 'inner,
						}
					}
				} else {
					// Since we don't have a parenthesis/function/array constructor group at all, that means we
					// have a lonely `)`. This means we want to stop parsing further tokens.
					log!("Found a `)` delimiter without a starting `(` delimiter!");
					return Err(SyntaxErr::FoundUnmatchedClosingDelim(
						end_span, false,
					));
				}
			}
		}

		match self.groups.back().unwrap() {
			Group::Paren(_, _) => self.collapse_bracket(end_span),
			Group::FnCall(_, _) => self.collapse_fn(end_span),
			Group::ArrInit(_, _) => self.collapse_arr_init(end_span),
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
	) -> Result<Option<usize>, SyntaxErr> {
		let current_group = match self.groups.back() {
			Some(t) => t,
			None => {
				// Since we have no groups, that means we have a lonely `]`. This means we want to stop parsing
				// further tokens.
				log!("Found a `]` delimiter without a starting `[` delimiter!");
				return Err(SyntaxErr::FoundUnmatchedClosingDelim(
					end_span, false,
				));
			}
		};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Index(false, Span::empty()))
		{
			// The current group is not an index group, so we need to check whether there is one at all.

			if self.exists_index_group() {
				// We have at least one other group to close before we can close the index group.
				'inner: loop {
					let current_group = match self.groups.back() {
						Some(g) => g,
						// PERF: Since we've already checked that there is a `Group::Index`, we know this will
						// never return `None` before we break out of the loop.
						None => break 'inner,
					};

					match current_group {
						Group::Paren(_, _) => {
							log!("Unclosed `)` parenthesis found!");
							self.collapse_bracket(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::FnCall(_, _) => {
							log!("Unclosed `)` function call found!");
							self.collapse_fn(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::Init(_, _) => {
							log!("Unclosed `}}` initializer list found!");
							self.collapse_init(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::ArrInit(_, _) => {
							log!("Unclosed `)` array constructor found!");
							self.collapse_arr_init(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::List(_, _) => {
							self.collapse_list(end_span.end_at_previous().end)
						}
						Group::Index(_, _) => break 'inner,
					}
				}
			} else {
				// Since we don't have an index group at all, that means we have a lonely `]`. This means we want
				// to stop parsing further tokens.
				log!("Found a `]` delimiter without a starting `[` delimiter!");
				return Err(SyntaxErr::FoundUnmatchedClosingDelim(
					end_span, false,
				));
			}
		}

		// If this `Index` can start an array constructor, return the start of the identifier token, i.e.
		//
		//   ident[...]
		//  ^
		let can_start_arr_init = match self.groups.back().unwrap() {
			Group::Index(_, possible_start) => possible_start,
			_ => unreachable!(),
		};

		self.collapse_index(end_span);
		Ok(Some(0))
	}

	/// Registers the end of an initializer list group, popping any operators until the start of the group is
	/// reached.
	fn end_init(&mut self, end_span: Span) -> Result<(), SyntaxErr> {
		let current_group =
			match self.groups.back() {
				Some(t) => t,
				None => {
					// Since we have no groups, that means we have a lonely `}`. This means we want to stop parsing
					// further tokens.
					log!("Found a `}}` delimiter without a starting `{{` delimiter!");
					return Err(SyntaxErr::FoundUnmatchedClosingDelim(
						end_span, true,
					));
				}
			};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Init(0, Span::empty()))
		{
			// The current group is not an initializer group, so we need to check whether there is one at all.

			if self.exists_init_group() {
				// We have at least one other group to close before we can close the initializer group.
				'inner: loop {
					let current_group = match self.groups.back() {
						Some(g) => g,
						// PERF: Since we've already checked that there is a `Group::Index`, we know this will
						// never return `None` before we break out of the loop.
						None => break 'inner,
					};

					match current_group {
						Group::Paren(_, _) => {
							log!("Unclosed `)` parenthesis found!");
							self.collapse_bracket(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::Index(_, _) => {
							log!("Unclosed `]` index operator found!");
							self.collapse_index(end_span.start_zero_width());
						}
						Group::FnCall(_, _) => {
							log!("Unclosed `)` function call found!");
							self.collapse_fn(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						Group::ArrInit(_, _) => {
							log!("Unclosed `)` array constructor found!");
							self.collapse_arr_init(span(
								end_span.end_at_previous().end,
								end_span.end_at_previous().end,
							));
						}
						// See `List` documentation.
						Group::List(_, _) => unreachable!(),
						Group::Init(_, _) => break 'inner,
					}
				}
			} else {
				// Since we don't have an initializer group at all, that means we have a lonely `}`. This means we
				// want to stop parsing further tokens.
				log!(
					"Found a `}}` delimiter without a starting `{{` delimiter!"
				);
				return Err(SyntaxErr::FoundUnmatchedClosingDelim(
					end_span, true,
				));
			}
		}

		self.collapse_init(end_span);
		Ok(())
	}

	/// Registers the end of a sub-expression, popping any operators until the start of the group (or expression)
	/// is reached.
	fn end_comma(&mut self) {
		if let Some(group) = self.groups.back_mut() {
			match group {
				Group::FnCall(_, _)
				| Group::Init(_, _)
				| Group::ArrInit(_, _) => {
					// We want to move all existing operators up to the function call, initializer list, or array
					// constructor start delimiter to the stack, to clear it for the next expression.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::FnCallStart
							|| back.ty == OpTy::InitStart
							|| back.ty == OpTy::ArrInitStart
						{
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
				}
				Group::List(_, _) => {
					// We want to move all existing operators up to the bracket or index start delimiter, or to the
					// beginning of the expression. We don't push a new list group since we are already within a
					// list group, and it accepts a variable amount of arguments.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::ParenStart
							|| back.ty == OpTy::IndexStart
						{
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
				}
				Group::Paren(_, _) | Group::Index(_, _) => {
					// Same as the branch above, but we do push a new list group. Since list groups don't have a
					// start delimiter, we can only do it now that we've encountered a comma within these two
					// groups.
					let mut list_start_pos = self.start_position;
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::ParenStart
							|| back.ty == OpTy::IndexStart
						{
							list_start_pos = back.span.end;
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
					self.groups.push_back(Group::List(1, list_start_pos));
				}
			}
		} else {
			// Since we are outside of any group, we can just push all the operators to the stack to clear it for
			// the next expression. We also push a new list group. Since list groups don't have a start delimiter,
			// we can only do it now that we've encountered a comma in an otherwise ungrouped expression.
			while self.operators.back().is_some() {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
			}
			self.groups.push_back(Group::List(1, self.start_position))
		}
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
				| OpTy::Not(b) => *b = true,
				_ => {}
			}
		}
	}

	/// Returns whether we have just started to parse a function, i.e. `..fn(<HERE>`
	fn just_started_fn(&self) -> bool {
		if let Some(current_group) = self.groups.back() {
			match current_group {
				Group::FnCall(count, _) => *count == 0,
				_ => false,
			}
		} else {
			false
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

		// The start position of a potential delimiter, i.e. an `Ident` which may become a function call or an
		// array constructor.
		let mut possible_delim_start = 0;

		// Whether to increase the arity on the next iteration. If set to `true`, on the next iteration, if we have
		// a valid State::Operand, we increase the arity and reset the flag back to `false`.
		let mut increase_arity = false;

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
				Token::Num { .. } | Token::Bool(_)
					if state == State::Operand =>
				{
					// We switch state since after an atom, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					self.stack.push_back(match Lit::parse(token) {
						Ok(l) => Either::Left(Expr {
							span: *span,
							ty: ExprTy::Lit(l),
						}),
						Err(_) => Either::Left(Expr {
							span: *span,
							ty: ExprTy::Invalid,
						}),
					});
					state = State::AfterOperand;

					can_start = Start::None;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
					self.set_op_rhs_toggle();
				}
				Token::Ident(s) if state == State::Operand => {
					// We switch state since after an atom, we are expecting an operator, i.e.
					// `..ident + i` instead of `..ident i`.
					self.stack.push_back(Either::Left(Expr {
						span: *span,
						ty: ExprTy::Ident(Ident {
							name: s.clone(),
							span: *span,
						}),
					}));
					state = State::AfterOperand;

					// After an identifier, we may start a function call.
					can_start = Start::FnOrArr;
					possible_delim_start = span.start;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
					self.set_op_rhs_toggle();
				}
				Token::Num { .. } | Token::Bool(_) | Token::Ident(_)
					if state == State::AfterOperand =>
				{
					if self.mode != Mode::TakeOneUnit {
						// This is an error, e.g. `..1 1` instead of `..1 + 1`.
						log!("Expected a postfix, index or binary operator, or the end of expression, found an atom instead!");

						// Panic: Since the state starts with `State::Operand` and we are in now
						// `State::AfterOperand`, we can be certain at least one item is on the stack.
						let prev_operand_span =
							self.get_previous_span().unwrap();
						self.errors.push(SyntaxErr::FoundOperandAfterOperand(
							prev_operand_span,
							*span,
						));
					}
					break 'main;
				}
				Token::Op(op) if state == State::Operand => {
					// If the parser is set to break at an `=`, do so.
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == lexer::OpTy::Eq
					{
						// self.errors.push(SyntaxErr::FoundEq(*span));
						break 'main;
					}

					match op {
						lexer::OpTy::Sub
						| lexer::OpTy::Not
						| lexer::OpTy::Flip
						| lexer::OpTy::AddAdd
						| lexer::OpTy::SubSub => self.set_op_rhs_toggle(),
						_ => {}
					}

					match op {
						// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
						// state since after a prefix operator, we are still looking for an operand atom.
						lexer::OpTy::Sub => self.push_operator(Op {
							span: *span,
							ty: OpTy::Neg(false),
						}),
						lexer::OpTy::Not => self.push_operator(Op {
							span: *span,
							ty: OpTy::Not(false),
						}),
						lexer::OpTy::Flip => self.push_operator(Op {
							span: *span,
							ty: OpTy::Flip(false),
						}),
						lexer::OpTy::AddAdd => self.push_operator(Op {
							span: *span,
							ty: OpTy::AddPre(false),
						}),
						lexer::OpTy::SubSub => self.push_operator(Op {
							span: *span,
							ty: OpTy::SubPre(false),
						}),
						_ => {
							// This is an error, e.g. `..*1` instead of `..-1`.
							log!("Expected an atom or a prefix operator, found a non-prefix operator instead!");
							self.errors
								.push(SyntaxErr::InvalidPrefixOperator(*span));
							break 'main;
						}
					}

					can_start = Start::None;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
				}
				Token::Op(op) if state == State::AfterOperand => {
					// If the parser is set to break at an `=`, do so.
					if (self.mode == Mode::BreakAtEq
						|| self.mode == Mode::TakeOneUnit)
						&& *op == lexer::OpTy::Eq
					{
						//self.errors.push(SyntaxErr::FoundEq(*span));
						break 'main;
					}

					match op {
						lexer::OpTy::Flip | lexer::OpTy::Not => {
							// These operators cannot be directly after an atom, because they are prefix operators.
							log!("Expected a postfix, index or binary operator, found a prefix operator instead!");
							self.errors.push(
								SyntaxErr::FoundPrefixInsteadOfPostfix(*span),
							);
							break 'main;
						}
						// These operators are postfix operators. We don't switch state since after a postfix
						// operator, we are still looking for a binary operator or the end of expression, i.e.
						// `..i++ - i` rather than `..i++ i`.
						lexer::OpTy::AddAdd => {
							self.push_operator(Op {
								span: *span,
								ty: OpTy::AddPost,
							});
						}
						lexer::OpTy::SubSub => {
							self.push_operator(Op {
								span: *span,
								ty: OpTy::SubPost,
							});
						}
						// Any other operators can be part of a binary expression. We switch state since after a
						// binary operator we are expecting an operand.
						_ => {
							self.push_operator(Op::from_token(*op, *span));
							state = State::Operand;
						}
					}

					can_start = Start::None;
				}
				Token::LParen if state == State::Operand => {
					// We don't switch state since after a `(`, we are expecting an operand, i.e.
					// `..+ (1 *` rather than `..+ (*`.

					// First increment the arity, since we are creating a new group.
					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
					self.set_op_rhs_toggle();

					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::ParenStart,
					});
					self.groups.push_back(Group::Paren(false, *span));

					can_start = Start::None;

					increase_arity = true;
				}
				Token::LParen if state == State::AfterOperand => {
					if can_start == Start::FnOrArr {
						// We have `ident(` which makes this a function call.
						self.operators.push_back(Op {
							span: *span,
							ty: OpTy::FnCallStart,
						});
						self.groups.push_back(Group::FnCall(0, *span));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `fn( 1..` rather than`fn( +..`.1
						state = State::Operand;

						// We unset the flag, since this flag is only used to detect the `ident` -> `(` token
						// chain.
						can_start = Start::None;

						increase_arity = true;
					} else if can_start == Start::ArrInit {
						// We have `ident[...](` which makes this an array constructor.
						self.operators.push_back(Op {
							span: *span,
							ty: OpTy::ArrInitStart,
						});
						self.groups.push_back(Group::ArrInit(0, *span));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `int[]( 1,..` rather than`int[]( +1,..`.
						state = State::Operand;

						// We unset the flag, since this flag is only used to detect the `..]` -> `(` token chain.
						can_start = Start::None;

						increase_arity = true;
					} else {
						if self.mode != Mode::TakeOneUnit {
							// This is an error. e.g. `..1 (` instead of `..1 + (`.
							log!("Expected an operator or the end of expression, found `(` instead!");

							// Panic: Since the state starts with `State::Operand` and we are in now `State::AfterOperand`,
							// we can be certain at least one item is on the stack.
							let prev_operand_span =
								self.get_previous_span().unwrap();
							self.errors.push(
								SyntaxErr::FoundOperandAfterOperand(
									prev_operand_span,
									*span,
								),
							);
						}
						break 'main;
					}
				}
				Token::RParen if state == State::AfterOperand => {
					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`.
					match self.end_bracket_fn(*span) {
						Ok(_) => {}
						Err(e) => {
							if self.mode != Mode::TakeOneUnit {
								self.errors.push(e);
							}
							break 'main;
						}
					}

					can_start = Start::None;
				}
				Token::RParen if state == State::Operand => {
					if self.just_started_fn() {
						// This is valid, i.e. `fn()`.
						match self.end_bracket_fn(*span) {
							Ok(_) => {}
							Err(e) => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(e);
								}
								break 'main;
							}
						}

						// We switch state since after a function call we are expecting an operator, i.e.
						// `..fn() + 5` rather than `..fn() 5`.
						state = State::AfterOperand;

						increase_arity = false;

						can_start = Start::None;
					} else {
						// This is an error, e.g. `..+ )` instead of `..+ 1)`,
						// or `fn(..,)` instead of `fn(.., 1)`.
						log!("Expected an atom or a prefix operator, found `)` instead!");
						match self.get_previous_span() {
							Some(prev_op_span) => {
								if self.exists_paren_fn_group() {
									self.errors.push(
										SyntaxErr::FoundClosingDelimInsteadOfOperand(
											prev_op_span,
											*span,
										),
									);
								} else {
									if self.mode != Mode::TakeOneUnit {
										self.errors.push(
											SyntaxErr::FoundUnmatchedClosingDelim(
												*span, false,
											),
										);
									}
								}
							}
							None => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(
										SyntaxErr::FoundUnmatchedClosingDelim(
											*span, false,
										),
									);
								}
							}
						}
						break 'main;
					}
				}
				Token::LBracket if state == State::AfterOperand => {
					// We switch state since after a `[`, we are expecting an operand, i.e.
					// `i[5 +..` rather than `i[+..`.
					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::IndexStart,
					});
					if can_start == Start::FnOrArr {
						// Since we just had an `Expr::Ident` before, this `Index` may be part of a greater array
						// constructor, so we want to store the starting position in case it is needed later.
						self.groups.push_back(Group::Index(true, *span));
					} else {
						// We had something other than an `Expr::Ident` beforehand, so don't bother storing the
						// position.
						self.groups.push_back(Group::Index(true, *span));
					}
					state = State::Operand;

					can_start = Start::EmptyIndex;
				}
				Token::LBracket if state == State::Operand => {
					if self.mode != Mode::TakeOneUnit {
						// This is an error, e.g. `..+ [` instead of `..+ i[`.
						log!("Expected an atom or a prefix operator, found `[` instead!");
						match self.get_previous_span() {
							Some(prev_op_span) => self.errors.push(
								SyntaxErr::FoundOperatorInsteadOfOperand(
									prev_op_span,
									*span,
								),
							),
							None => self.errors.push(
								SyntaxErr::FoundOperatorFirstThing(*span),
							),
						}
					}
					break 'main;
				}
				Token::RBracket if state == State::AfterOperand => {
					// We don't switch state since after a `]`, we are expecting an operator, i.e.
					// `..] + 5` instead of `..] 5`.
					match self.end_index(*span) {
						Ok(can_start_arr_init) => {
							if let Some(delim_start) = can_start_arr_init {
								// After an index `ident[..]` we may have an array constructor.
								can_start = Start::ArrInit;
								// We want to set the possible start value to the one provided by the index, so
								// that if we encounter a `(`, we create an `ArrInit` with the correct span.
								possible_delim_start = delim_start;
							}
						}
						Err(e) => {
							if self.mode != Mode::TakeOneUnit {
								self.errors.push(e);
							}
							break 'main;
						}
					}
				}
				Token::RBracket if state == State::Operand => {
					if can_start == Start::EmptyIndex {
						// We switch state since after a `]`, we are expecting an operator, i.e.
						// `..[] + 5` rather than `..[] 5`.

						match self.groups.back_mut() {
							Some(g) => match g {
								Group::Index(contains_i, _) => {
									*contains_i = false
								}
								_ => unreachable!(),
							},
							None => unreachable!(),
						}

						match self.end_index(*span) {
							Ok(can_start_arr_init) => {
								if let Some(delim_start) = can_start_arr_init {
									// After an index `ident[]` we may have an array constructor.
									can_start = Start::ArrInit;
									// We want to set the possible start value to the one provided by the index, so
									// that if we encounter a `(`, we create an `ArrInit` with the correct span.
									possible_delim_start = delim_start;
								}
							}
							Err(e) => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(e);
								}
								break 'main;
							}
						}
						state = State::AfterOperand;
					} else {
						// This is an error, e.g. `..+ ]` instead of `..+ 1]`.
						log!("Expected an atom or a prefix operator, found `]` instead!");
						match self.get_previous_span() {
							Some(prev_op_span) => {
								if self.exists_index_group() {
									self.errors.push(
										SyntaxErr::FoundClosingDelimInsteadOfOperand(
											prev_op_span,
											*span,
										),
									);
								} else {
									if self.mode != Mode::TakeOneUnit {
										self.errors.push(
											SyntaxErr::FoundUnmatchedClosingDelim(
												*span, false,
											),
										);
									}
								}
							}
							None => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(
										SyntaxErr::FoundUnmatchedClosingDelim(
											*span, false,
										),
									);
								}
							}
						}
						break 'main;
					}
				}
				Token::LBrace if state == State::Operand => {
					// We don't switch state since after a `{`, we are expecting an operand, i.e.
					// `..+ {1,` rather than `..+ {,`.

					// First increase the arity, since we are creating a new group with its own arity.
					if increase_arity {
						self.increase_arity();
					}
					self.set_op_rhs_toggle();

					self.operators.push_back(Op {
						span: *span,
						ty: OpTy::InitStart,
					});
					self.groups.push_back(Group::Init(0, *span));

					increase_arity = true;

					can_start = Start::None;
				}
				Token::LBrace if state == State::AfterOperand => {
					if self.mode != Mode::TakeOneUnit {
						// This is an error, e.g. `.. {` instead of `.. + {`.
						log!("Expected an operator or the end of expression, found `{{` instead!");

						// Panic: Since the state starts with `State::Operand` and we are in now `State::AfterOperand`,
						// we can be certain at least one item is on the stack.
						let prev_operand_span =
							self.get_previous_span().unwrap();
						self.errors.push(SyntaxErr::FoundOperandAfterOperand(
							prev_operand_span,
							*span,
						));
					}
					break 'main;
				}
				Token::RBrace if state == State::AfterOperand => {
					// We don't switch state since after a `}`, we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
					match self.end_init(*span) {
						Ok(_) => {}
						Err(e) => {
							if self.mode != Mode::TakeOneUnit {
								self.errors.push(e);
							}
							break 'main;
						}
					}

					can_start = Start::None;
				}
				Token::RBrace if state == State::Operand => {
					if self.just_started_init() || self.is_in_init() {
						// This is valid, i.e. `{}`, or `{1, }`.
						match self.end_init(*span) {
							Ok(_) => {}
							Err(e) => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(e);
								}
								break 'main;
							}
						}

						// We switch state since after an init list we are expecting an operator, i.e.
						// `..}, {..` rather than `..} {..`.
						state = State::AfterOperand;

						increase_arity = false;

						can_start = Start::None;
					} else {
						// This is an error, e.g. `..+ }` instead of `..+ 1}`.
						log!("Expected an atom or a prefix operator, found `}}` instead!");
						match self.get_previous_span() {
							Some(prev_op_span) => {
								if self.exists_init_group() {
									self.errors.push(
										SyntaxErr::FoundClosingDelimInsteadOfOperand(
											prev_op_span,
											*span,
										),
									);
								} else {
									if self.mode != Mode::TakeOneUnit {
										self.errors.push(
											SyntaxErr::FoundUnmatchedClosingDelim(
												*span, true,
											),
										);
									}
								}
							}
							None => {
								if self.mode != Mode::TakeOneUnit {
									self.errors.push(
										SyntaxErr::FoundUnmatchedClosingDelim(
											*span, true,
										),
									);
								}
							}
						}
						break 'main;
					}
				}
				Token::Comma if state == State::AfterOperand => {
					if (self.mode == Mode::DisallowTopLevelList
						|| self.mode == Mode::TakeOneUnit)
						&& self.groups.is_empty()
					{
						log!("Found a `,` outside of a group, with `Mode::DisallowTopLevelList`!");
						//self.errors
						//	.push(SyntaxErr::FoundCommaAtTopLevel(*span));
						break 'main;
					}

					// We switch state since after a comma (which delineates an expression), we're effectively
					// starting a new expression which must start with an operand, i.e.
					// `.., 5 + 6` instead of `.., + 6`.
					self.end_comma();
					state = State::Operand;

					can_start = Start::None;

					increase_arity = true;
				}
				Token::Comma if state == State::Operand => {
					// This is an error, e.g. `..+ ,` instead of `..+ 1,`.
					log!("Expected an atom or a prefix operator, found `,` instead!");
					match self.get_previous_span() {
						Some(prev_op_span) => self.errors.push(
							SyntaxErr::FoundCommaInsteadOfOperand(
								prev_op_span,
								*span,
							),
						),
						None => self
							.errors
							.push(SyntaxErr::FoundCommaFirstThing(*span)),
					}
					break 'main;
				}
				Token::Dot if state == State::AfterOperand => {
					// We switch state since after an object access we are execting an operand, i.e.
					// `ident.something` rather than `ident. +`.
					self.push_operator(Op {
						span: *span,
						ty: OpTy::ObjAccess,
					});
					state = State::Operand;

					can_start = Start::None;
				}
				Token::Dot if state == State::Operand => {
					// This is an error, e.g. `ident.+` instead of `ident.something`.
					log!("Expected an atom or a prefix operator, found `.` instead!");
					match self.get_previous_span() {
						Some(prev_op_span) => self.errors.push(
							SyntaxErr::FoundDotInsteadOfOperand(
								prev_op_span,
								*span,
							),
						),
						None => self
							.errors
							.push(SyntaxErr::FoundDotFirstThing(*span)),
					}
					break 'main;
				}
				_ => {
					// We have a token that's not allowed to be part of an expression.
					log!("Unexpected token found: {token:?}");
					self.errors.push(SyntaxErr::FoundInvalidToken(*span));
					break 'main;
				}
			}

			walker.advance();
		}

		if !self.groups.is_empty() {
			// The end position of this expression will be the end position of the last parsed item.
			let group_end = self.get_previous_span().unwrap().end_zero_width();

			// Close any open groups.
			while let Some(group) = self.groups.pop_back() {
				log!("Found an unclosed: {group:?}");

				// TODO: No invalidation anymore, still syntax errors though.
				// Reasoning about what gets invalidated and what doesn't: will it potentially produce semantic errors
				//
				// Brackets - no matter where the closing parenthesis is located, it won't change whether the
				// 	 expression type checks or not.
				// Index - depending on where the closing bracket is placed, it can change whether the expression
				// 	 type checks or not.
				// Fn - depending on where the closing parenthesis is, it can change the number of arguments.
				// Init - same as above.
				// ArrInit - same as above.
				// List - a perfectly valid top-level grouping structure.
				match group {
					Group::Paren(_, l_paren) => {
						self.errors.push(SyntaxErr::UnclosedParenthesis(
							l_paren, group_end,
						));
						self.collapse_bracket(group_end);
					}
					Group::Index(_, l_bracket) => {
						self.errors.push(SyntaxErr::UnclosedIndexOperator(
							l_bracket, group_end,
						));
						self.collapse_index(group_end)
					}
					Group::FnCall(_, l_paren) => {
						self.errors.push(SyntaxErr::UnclosedFunctionCall(
							l_paren, group_end,
						));
						self.collapse_fn(group_end)
					}
					Group::Init(_, l_brace) => {
						self.errors.push(SyntaxErr::UnclosedInitializerList(
							l_brace, group_end,
						));
						self.collapse_init(group_end)
					}
					Group::ArrInit(_, l_paren) => {
						self.errors.push(SyntaxErr::UnclosedArrayConstructor(
							l_paren, group_end,
						));
						self.collapse_arr_init(group_end)
					}
					Group::List(_, _) => self.collapse_list(group_end.end),
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
		let mut stack = VecDeque::new();

		// We have "parsed" the token stream and we immediately hit a token which cannot be part of an expression.
		// Hence, there is no expression to return at all.
		if self.stack.len() == 0 {
			return None;
		}

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the n-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(item) = self.stack.pop_front() {
			match item {
				Either::Left(e) => stack.push_back(e),
				Either::Right(op) => match op.ty {
					OpTy::AddPre(has_operand) => {
						let expr =
							if has_operand { stack.pop_back() } else { None };
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
						let expr =
							if has_operand { stack.pop_back() } else { None };
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
						let expr = stack.pop_back().unwrap();
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
						let expr = stack.pop_back().unwrap();
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
						let expr =
							if has_operand { stack.pop_back() } else { None };
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
						let expr =
							if has_operand { stack.pop_back() } else { None };
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
						let expr =
							if has_operand { stack.pop_back() } else { None };
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
					OpTy::Paren(has_inner, l_span, end) => {
						let expr =
							if has_inner { stack.pop_back() } else { None };
						stack.push_back(Expr {
							span: op.span,
							ty: ExprTy::Paren {
								expr: expr.map(|e| Box::from(e)),
								l_paren: l_span,
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::FnCall(count, l_paren, end) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap());
						}
						// Get the identifier (which is the first expression).
						let ident = match args.pop_front().unwrap().ty {
							ExprTy::Ident(i) => i,
							_ => panic!("The first expression of a function call operator is not an identifier!")
						};
						stack.push_back(Expr {
							span: Span::new(ident.span.start, end.end),
							ty: ExprTy::Fn {
								ident,
								l_paren,
								args: args.into(),
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::Index(contains_i, l_bracket, end) => {
						let i = if contains_i {
							stack.pop_back().map(|e| Box::from(e))
						} else {
							None
						};
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr {
							span: Span::new(expr.span.start, end.end),
							ty: ExprTy::Index {
								item: Box::from(expr),
								l_bracket,
								i,
								r_bracket: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::Init(count, l_brace, r_brace) => {
						// Note: the span for `Op::Init` is from the start of the `{` to the end of the `}`.
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap());
						}
						args.reverse();
						stack.push_back(Expr {
							ty: ExprTy::Init {
								l_brace,
								args,
								r_brace: if r_brace.is_zero_width() {
									None
								} else {
									Some(r_brace)
								},
							},
							span: op.span,
						});
					}
					OpTy::ArrInit(count, l_paren, end) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap());
						}
						// Get the index operator (which is the first expression).
						let arr = args.pop_front().unwrap();
						match arr.ty {
							ExprTy::Index { .. } => {}
							_ => {
								panic!("The first expression of an array constructor operator is not an `Expr::Index`!");
							}
						}
						stack.push_back(Expr {
							span: Span::new(arr.span.start, end.end),
							ty: ExprTy::ArrInit {
								arr: Box::from(arr),
								l_paren,
								args: args.into(),
								r_paren: if end.is_zero_width() {
									None
								} else {
									Some(end)
								},
							},
						});
					}
					OpTy::List(count) => {
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap());
						}
						args.reverse();
						stack.push_back(Expr {
							ty: ExprTy::List(args),
							span: op.span,
						});
					}
					OpTy::ObjAccess => {
						let access = stack.pop_back().unwrap();
						let obj = stack.pop_back().unwrap();
						let span = span(obj.span.start, access.span.end);
						stack.push_back(Expr {
							ty: ExprTy::ObjAccess {
								obj: Box::from(obj),
								leaf: Box::from(access),
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
						let last = stack.pop_back().unwrap();
						let (left, right) = if has_rhs {
							(stack.pop_back().unwrap(), Some(last))
						} else {
							(last, None)
						};
						//dbg!(has_rhs);
						//dbg!(&left);
						//dbg!(&right);

						let span = if let Some(ref right) = right {
							Span::new(left.span.start, right.span.end)
						} else {
							Span::new(left.span.start, op.span.end)
						};
						stack.push_back(Expr {
							ty: ExprTy::Binary {
								left: Box::from(left),
								op: BinOp::from(op),
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

		#[cfg(debug_assertions)]
		if stack.len() != 1 {
			panic!("After processing the shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap())
	}
}

/*
#[cfg(test)]
use crate::lexer::lexer;

/// Asserts whether the expression output of the `expr_parser()` matches the right hand side.
#[cfg(test)]
macro_rules! assert_expr {
	($source:expr, $rest:expr) => {
		let mut walker = Walker {
			token_stream: lexer($source),
			cursor: 0,
		};
		assert_eq!(
			expr_parser(&mut walker, Mode::Default, &[]).0.unwrap(),
			$rest
		);
	};
}

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
fn brackets() {
	assert_expr!("(5 + 1) * 8", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{
				ty: ExprTy::Paren {
					expr: Box::from(Expr{
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
							op: Op{ty: OpTy::Add, span: span(3, 4)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(5, 6)}),
						},
						span: span(1, 6),
					}),
					left: span(0, 1),
					right: span(6, 7),
				},
				span: span(0, 7),
			}),
			op: Op{ty: OpTy::Mul, span: span(8, 9)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(8)), span: span(10, 11)})
		},
		span: span(0, 11),
	});
	assert_expr!("((5 + 1) < 100) * 8", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr {
				ty: ExprTy::Paren {
					expr: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr {
								ty: ExprTy::Paren {
									expr: Box::from(Expr {
										ty: ExprTy::Binary {
											left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
											op: Op{ty: OpTy::Add, span: span(4, 5)},
											right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)}),
										},
										span: span(2, 7),
									}),
									left: span(1, 2),
									right: span(7, 8),
								},
								span: span(1, 8),
							}),
							op: Op{ty: OpTy::Lt, span: span(9, 10)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(100)), span: span(11, 14)}),
						},
						span: span(1, 14),
					}),
					left: span(0, 1),
					right: span(14, 15),
				},
				span: span(0, 15),
			}),
			op: Op{ty: OpTy::Mul, span: span(16, 17)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(8)), span: span(18, 19)})
		},
		span: span(0, 19),
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
fn fn_calls() {
	assert_expr!("fn()", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![]},
		span: span(0, 4),
	});
	assert_expr!("fu_nc(1)", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fu_nc".into(), span: span(0, 5)}, args: vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)},
		]},
		span: span(0, 8),
	});
	assert_expr!("fn(5 + 1, i << 6)", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn".into(), span: span(0, 2)},
			args: vec![
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(3, 4)}),
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(7, 8)}),
						op: Op{ty: OpTy::Add, span: span(5, 6)},
					},
					span: span(3, 8),
				},
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(10, 11)}), span: span(10, 11)}),
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(6)), span: span(15, 16)}),
						op: Op{ty: OpTy::LShift, span: span(12, 14)},
					},
					span: span(10, 16),
				}
			]
		},
		span: span(0, 17),
	});
	assert_expr!("fn(fn())", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![Expr {
			ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(3, 5)}, args: vec![]},
			span: span(3, 7),
		}]},
		span: span(0, 8),
	});
	assert_expr!("fn1(5, fn2(0))", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn1".into(), span: span(0, 3)},
			args: vec![
				Expr {
					ty: ExprTy::Lit(Lit::Int(5)),
					span: span(4, 5),
				},
				Expr {
					ty: ExprTy::Fn{ident: Ident{name: "fn2".into(), span: span(7, 10)}, args: vec![Expr {
						ty: ExprTy::Lit(Lit::Int(0)),
						span: span(11, 12),
					}]},
					span: span(7, 13),
				}
			]
		},
		span: span(0, 14),
	});
	assert_expr!("fn1(5, fn2(fn3()))", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn1".into(), span: span(0, 3)},
			args: vec![
				Expr {
					ty: ExprTy::Lit(Lit::Int(5)),
					span: span(4, 5),
				},
				Expr {
					ty: ExprTy::Fn{ident: Ident{name: "fn2".into(), span: span(7, 10)}, args: vec![Expr {
						ty: ExprTy::Fn{ident: Ident{name: "fn3".into(), span: span(11, 14)}, args: vec![]},
						span: span(11, 16),
					}]},
					span: span(7, 17),
				}
			]
		},
		span: span(0, 18),
	});
}

#[test]
#[rustfmt::skip]
fn obj_access() {
	assert_expr!("ident.something", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "ident".into(), span: span(0, 5)}), span: span(0, 5)}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "something".into(), span: span(6, 15)}), span: span(6, 15)}),
		},
		span: span(0, 15),
	});
	/* assert_expr!("a.b.c", Expr::ObjAccess {
		obj: Box::from(Expr::Ident(Ident("a".into()))),
		access: Box::from(Expr::ObjAccess {
			obj: Box::from(Expr::Ident(Ident("b".into()))),
			access: Box::from(Expr::Ident(Ident("c".into())))
		})
	}); */
	assert_expr!("a.b.c", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr {
				ty: ExprTy::ObjAccess {
					obj: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)}),
					leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(2, 3)}), span: span(2, 3)}),
				},
				span: span(0, 3),
			}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "c".into(), span: span(4, 5)}), span: span(4, 5)}),
		},
		span: span(0, 5),
	});
	assert_expr!("fn().x", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr{ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![]}, span: span(0, 4)}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "x".into(), span: span(5, 6)}), span: span(5, 6)}),
		},
		span: span(0, 6),
	});
}

#[test]
#[rustfmt::skip]
fn indexes() {
	// Single-dimensional indexes
	assert_expr!("i[0]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(0)), span: span(2, 3)})),
			op: span(1, 4),
		},
		span: span(0, 4),
	});
	assert_expr!("s[z+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "s".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "z".into(), span: span(2, 3)}), span: span(2, 3)}),
					op: Op{ty: OpTy::Add, span: span(3, 4)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
				},
				span: span(2, 5),
			})),
			op: span(1, 6)
		},
		span: span(0, 6),
	});
	assert_expr!("i[y[5]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "y".into(), span:span(2, 3)}), span: span(2, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(2, 6),
			})),
			op: span(1, 7)
		},
		span: span(0, 7),
	});
	assert_expr!("i[y[z[1+2]]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "y".into(), span:span(2, 3)}), span: span(2, 3)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "z".into(), span:span(4, 5)}), span: span(4, 5)}),
							i: Some(Box::from(Expr {
								ty: ExprTy::Binary {
									left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)}),
									op: Op{ty: OpTy::Add, span: span(7, 8)},
									right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(8, 9)}),
								},
								span: span(6, 9),
							})),
							op: span(5, 10),
						},
						span: span(4, 10),
					})),
					op: span(3, 11),
				},
				span: span(2, 11),
			})),
			op: span(1, 12)
		},
		span: span(0, 12),
	});

	// Multi-dimensional indexes
	assert_expr!("i[5][2]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
					op: span(1, 4),
				},
				span: span(0, 4),
			}),
			i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
			op: span(4, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("i[5][2][size]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
							i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
							op: span(1, 4),
						},
						span: span(0, 4),
					}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
					op: span(4, 7),
				},
				span: span(0, 7),
			}),
			i: Some(Box::from(Expr{ty: ExprTy::Ident(Ident{name: "size".into(), span: span(8, 12)}), span: span(8, 12)})),
			op: span(7, 13),
		},
		span: span(0, 13),
	});

	// Empty indexes
	assert_expr!("i[]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: None,
			op: span(1, 3),
		},
		span: span(0, 3),
	});
	assert_expr!("int[i[]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span:span(0, 3)}), span: span(0, 3)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(4, 5)}), span: span(4, 5)}),
					i: None,
					op: span(5, 7),
				},
				span: span(4, 7),
			})),
			op: span(3, 8)
		},
		span: span(0, 8),
	});
	assert_expr!("i[][]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
					i: None,
					op: span(1, 3),
				},
				span: span(0, 3),
			}),
			i: None,
			op: span(3, 5),
		},
		span: span(0, 5),
	});
	assert_expr!("i[5][2][]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
							i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
							op: span(1, 4),
						},
						span: span(0, 4),
					}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
					op: span(4, 7),
				},
				span: span(0, 7),
			}),
			i: None,
			op: span(7, 9),
		},
		span: span(0, 9),
	});
}

#[test]
#[rustfmt::skip]
fn arr_constructors() {
	assert_expr!("int[1](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(7, 8)}],
		},
		span: span(0, 9),
	});
	assert_expr!("int[size](2, false, 5.0)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Ident(Ident{name: "size".into(), span: span(4, 8)}), span: span(4, 8)})),
					op: span(3, 9),
				},
				span: span(0, 9),
			}),
			args: vec![
				Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(10, 11)},
				Expr{ty: ExprTy::Lit(Lit::Bool(false)), span: span(13, 18)},
				Expr{ty: ExprTy::Lit(Lit::Float(5.0)), span: span(20, 23)}
			],
		},
		span: span(0, 24),
	});
	assert_expr!("int[1+5](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
							op: Op{ty: OpTy::Add, span: span(5, 6)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(6, 7)}),
						},
						span: span(4, 7),
					})),
					op: span(3, 8),
				},
				span: span(0, 8),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(9, 10)}],
		},
		span: span(0, 11),
	});
	assert_expr!("vec3[](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "vec3".into(), span: span(0, 4)}), span: span(0, 4)}),
					i: None,
					op: span(4, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(7, 8)}],
		},
		span: span(0, 9),
	});
}

#[test]
#[rustfmt::skip]
fn initializers() {
	assert_expr!("{1}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
		]),
		span: span(0, 3),
	});
	assert_expr!("{1,}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
		]),
		span: span(0, 4),
	});
	assert_expr!("{1, true, i}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
			Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(4, 8)},
			Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(10, 11)}), span: span(10, 11)},
		]),
		span: span(0, 12),
	});
	assert_expr!("{2.0, {1, s}}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Float(2.0)), span: span(1, 4)},
			Expr {
				ty: ExprTy::Init(vec![
					Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(7, 8)},
					Expr{ty: ExprTy::Ident(Ident{name: "s".into(), span: span(10, 11)}), span: span(10, 11)},
				]),
				span: span(6, 12),
			}
		]),
		span: span(0, 13),
	});
}

#[test]
#[rustfmt::skip]
fn lists() {
	// Note: Lists cannot exist within function calls, array constructors or initializer lists. Hence the absence
	// of those from this test.
	assert_expr!("a, b", Expr {
		ty: ExprTy::List(vec![
			Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)},
			Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(3, 4)}), span: span(3, 4)},
		]),
		span: span(0, 4),
	});
	assert_expr!("a, b, c", Expr {
		ty: ExprTy::List(vec![
			Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)},
			Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(3, 4)}), span: span(3, 4)},
			Expr{ty: ExprTy::Ident(Ident{name: "c".into(), span: span(6, 7)}), span: span(6, 7)},
		]),
		span: span(0, 7),
	});
	assert_expr!("i[a, b]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::List(vec![
					Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(2, 3)}), span: span(2, 3)},
					Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(5, 6)}), span: span(5, 6)},
				]),
				span: span(2, 6),
			})),
			op: span(1, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("(a, b)", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr {
				ty: ExprTy::List(vec![
					Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(1, 2)}), span: span(1, 2)},
					Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(4, 5)}), span: span(4, 5)},
				]),
				span: span(1, 5),
			}),
			left: span(0, 1),
			right: span(5, 6),
		},
		span: span(0, 6),
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

#[test]
#[rustfmt::skip]
fn incomplete() {
	/* assert_expr!("i+5]", Expr::Binary {
		left: Box::from(Expr::Ident(Ident("i".into()))),
		op: Op::Add,
		right: Box::from(Expr::Lit(Lit::Int(5)))
	}); */
	assert_expr!("i[(5+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(2, 6)})),
			op: span(1, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("i[fn((5+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(2, 9)})),
			op: span(1, 10),
		},
		span: span(0, 10),
	});
	/* assert_expr!("(i+5])", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr{ty: ExprTy::Incomplete, span: span(1, 5)}),
			left: span(0, 1),
			right: span(5, 6),
		},
		span: span(0, 6),
	}); */
	/* assert_expr!("fn(1])", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn".into(), span: span(0, 2)},
			args: vec![Expr{ty: ExprTy::Incomplete, span: span(3, 5)}]
		},
		span: span(0, 6),
	}); */
	/* assert_expr!("int[3](i])", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Incomplete, span: span(7, 9)}],
		},
		span: span(0, 10),
	}); */

	// Outer unclosed delimiters.
	assert_expr!("(i+x", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(1, 2)}), span: span(1, 2)}),
					op: Op{ty: OpTy::Add, span: span(2, 3)},
					right: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "x".into(), span: span(3, 4)}), span: span(3, 4)}),
				},
				span: span(1, 4),
			}),
			left: span(0, 1),
			right: span(4, 4),
		},
		span: span(0, 4),
	});
	assert_expr!("i[5+1", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(1, 5)})),
			op: span(1, 5),
		},
		span: span(0, 5),
	});
	assert_expr!("fn(5+1", Expr{ty: ExprTy::Incomplete, span: span(0, 6)});
	assert_expr!("{5, 1", Expr{ty: ExprTy::Incomplete, span: span(0, 5)});
	assert_expr!("int[5](1, 2", Expr{ty: ExprTy::Incomplete, span: span(0, 11)});
}
 */
