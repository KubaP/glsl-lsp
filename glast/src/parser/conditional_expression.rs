//! The parser for conditional directive expressions.

use super::{
	ast::conditional::{BinOp, BinOpTy, Expr, ExprTy, PreOp, PreOpTy},
	ast::Ident,
	SyntaxModifiers, SyntaxToken, SyntaxType,
};
use crate::{
	diag::{ExprDiag, Syntax},
	lexer::preprocessor::ConditionToken,
	Either, Span, Spanned,
};
use std::collections::VecDeque;

/*
The functionality of this parser is largely copied from the expression parser. The decision to copy the relevant
parts of the code over was done in order to prevent the complexity of the expression parser from growing even
larger. There are already a *lot* of conditions and checks and feature-gates; adding more would make it even
less maintainable. Furthermore, this parser uses an entirely different token type so the amount of direct code
reuse would be limited anyway.
*/

/// Tries to parse a conditional directive expression.
///
/// This function consumes all of the tokens; if a syntax error is encountered and the parser cannot continue, it
/// will invalidate the rest of the tokens.
pub(super) fn cond_parser(
	tokens: Vec<Spanned<ConditionToken>>,
) -> (Option<Expr>, Vec<Syntax>, Vec<SyntaxToken>) {
	let mut walker = Walker { tokens, cursor: 0 };

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: Vec::new(),
		syntax_diags: Vec::new(),
		syntax_tokens: Vec::new(),
	};
	parser.parse(&mut walker);

	(
		parser.create_ast(),
		parser.syntax_diags,
		parser.syntax_tokens,
	)
}

/// Allows for stepping through a conditional token stream.
struct Walker {
	/// The conditional expression token stream.
	tokens: Vec<Spanned<ConditionToken>>,
	/// The index of the current token.
	cursor: usize,
}

impl Walker {
	/// Returns a reference to the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<Spanned<&ConditionToken>> {
		self.tokens.get(self.cursor).map(|(t, s)| (t, *s))
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns whether the walker has reached the end of the token stream.
	fn is_done(&self) -> bool {
		self.cursor == self.tokens.len()
	}
}

/// A node; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Node {
	ty: NodeTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum NodeTy {
	Num(usize),
	Ident(Ident),
}

/// A node operator; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Op {
	ty: OpTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum OpTy {
	/* OPERATORS */
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
	EqEq(bool),
	NotEq(bool),
	AndAnd(bool),
	OrOr(bool),
	XorXor(bool),
	Gt(bool),
	Lt(bool),
	Ge(bool),
	Le(bool),
	Neg(bool),
	Flip(bool),
	Not(bool),
	/* GROUPS */
	/// The `(` token.
	ParenStart,
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis.
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	Paren(bool, Span, Span),
	/// The `defined` token.
	DefinedStart,
	/// A defined operator group. This operator spans from the keyword to either the closing parenthesis (if there
	/// is an opening one), or to the end of the first identifier after the keyword.
	///
	/// - `0` - Whether to consume a node for the inner expression.
	/// - `1` - The optional span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis if there is an opening parenthesis, or the span of the first
	///   identifier after the `defined` keyword. If this is zero-width, that means neither tokens are present.
	Defined(bool, Option<Span>, Span),
}

impl Op {
	/// Converts from a lexer `ConditionalToken` token to the `Op` type used in this expression parser.
	fn from_token(token: ConditionToken, span: Span) -> Self {
		Self {
			span,
			ty: match token {
				ConditionToken::Add => OpTy::Add(false),
				ConditionToken::Sub => OpTy::Sub(false),
				ConditionToken::Mul => OpTy::Mul(false),
				ConditionToken::Div => OpTy::Div(false),
				ConditionToken::Rem => OpTy::Rem(false),
				ConditionToken::And => OpTy::And(false),
				ConditionToken::Or => OpTy::Or(false),
				ConditionToken::Xor => OpTy::Xor(false),
				ConditionToken::LShift => OpTy::LShift(false),
				ConditionToken::RShift => OpTy::RShift(false),
				ConditionToken::EqEq => OpTy::EqEq(false),
				ConditionToken::NotEq => OpTy::NotEq(false),
				ConditionToken::AndAnd => OpTy::AndAnd(false),
				ConditionToken::OrOr => OpTy::OrOr(false),
				ConditionToken::XorXor => OpTy::XorXor(false),
				ConditionToken::Gt => OpTy::Gt(false),
				ConditionToken::Lt => OpTy::Lt(false),
				ConditionToken::Ge => OpTy::Ge(false),
				ConditionToken::Le => OpTy::Le(false),
				ConditionToken::Not | ConditionToken::Flip | _ => {
					// These tokens are handled by individual branches in the main parser loop.
					unreachable!("Given a conditional `token` which should never be handled by this function.")
				}
			},
		}
	}

	/// Returns the precedence of this operator.
	#[rustfmt::skip]
	fn precedence(&self) -> usize {
		match &self.ty {
			OpTy::Neg(_)
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
			// These are never directly checked for precedence, but rather have special branches.
			_ => unreachable!("The conditional expression operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
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
				OpTy::EqEq(_) => BinOpTy::EqEq,
				OpTy::NotEq(_) => BinOpTy::NotEq,
				OpTy::AndAnd(_) => BinOpTy::AndAnd,
				OpTy::OrOr(_) => BinOpTy::OrOr,
				OpTy::XorXor(_) => BinOpTy::XorXor,
				OpTy::Gt(_) => BinOpTy::Gt,
				OpTy::Lt(_) => BinOpTy::Lt,
				OpTy::Ge(_) => BinOpTy::Ge,
				OpTy::Le(_) => BinOpTy::Le,
				_ => unreachable!("Given a conditional expression `ty` which should not be handled here.")
			};

		BinOp {
			span: self.span,
			ty,
		}
	}
}

/// An open grouping of items.
enum Group {
	/// A parenthesis group.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis.
	/// - `1` - The span of the opening parenthesis.
	Paren(bool, Span),
	/// A defined operator group.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis.
	/// - `1` - The span of the `defined` keyword.
	/// - `2` - The optional span of the opening parenthesis.
	Defined(bool, Span, Option<Span>),
}

/// The implementation of a shunting yard-based parser.
struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Node, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The last entry is the group being currently parsed.
	groups: Vec<Group>,

	/// Syntax diagnostics encountered during the parser execution.
	syntax_diags: Vec<Syntax>,

	/// Syntax highlighting tokens created during the parser execution.
	syntax_tokens: Vec<SyntaxToken>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Op) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			match back.ty {
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				OpTy::ParenStart | OpTy::DefinedStart => break,
				_ => {}
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

	/// Registers the end of a parenthesis or defined operator group, popping any operators until the start of the
	/// group is reached.
	fn end_paren_defined(&mut self, end_span: Span) -> Result<(), ()> {
		let group = if !self.groups.is_empty() {
			self.groups.remove(self.groups.len() - 1)
		} else {
			return Err(());
		};

		match group {
			Group::Paren(has_inner, l_paren) => {
				while self.operators.back().is_some() {
					let op = self.operators.pop_back().unwrap();

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
			}
			Group::Defined(has_inner, defined, l_paren) => {
				while self.operators.back().is_some() {
					let op = self.operators.pop_back().unwrap();

					if let OpTy::DefinedStart = op.ty {
						self.stack.push_back(Either::Right(Op {
							span: Span::new(defined.start, end_span.end),
							ty: OpTy::Defined(has_inner, l_paren, end_span),
						}));
						break;
					} else {
						// Any other operators get moved, since we are moving everything until we hit the start
						// delimiter.
						self.stack.push_back(Either::Right(op));
					}
				}
			}
		}

		Ok(())
	}

	/// Registers the end of a defined operator group, popping any operators until the start of the group is
	/// reached.
	fn end_defined(&mut self, end_span: Span) {
		let group = if !self.groups.is_empty() {
			self.groups.remove(self.groups.len() - 1)
		} else {
			unreachable!()
		};

		match group {
			Group::Paren(_, _) => {
				unreachable!()
			}
			Group::Defined(has_inner, defined, l_paren) => {
				while self.operators.back().is_some() {
					let op = self.operators.pop_back().unwrap();

					if let OpTy::DefinedStart = op.ty {
						self.stack.push_back(Either::Right(Op {
							span: Span::new(defined.start, end_span.end),
							ty: OpTy::Defined(has_inner, l_paren, end_span),
						}));
						break;
					} else {
						// Any other operators get moved, since we are moving everything until we hit the start
						// delimiter.
						self.stack.push_back(Either::Right(op));
					}
				}
			}
		}
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
				| OpTy::EqEq(b)
				| OpTy::NotEq(b)
				| OpTy::AndAnd(b)
				| OpTy::OrOr(b)
				| OpTy::XorXor(b)
				| OpTy::Gt(b)
				| OpTy::Lt(b)
				| OpTy::Ge(b)
				| OpTy::Le(b)
				| OpTy::Neg(b)
				| OpTy::Flip(b)
				| OpTy::Not(b) => *b = true,
				_ => {}
			}
		}
		if let Some(Group::Paren(b, _) | Group::Defined(b, _, _)) =
			self.groups.last_mut()
		{
			*b = true;
		}
	}

	/// Returns whether we have just started to parse a parenthesis group, i.e. `..(<HERE>`.
	fn just_started_paren(&self) -> bool {
		if let Some(Group::Paren(has_inner, _)) = self.groups.last() {
			*has_inner == false
		} else {
			false
		}
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
	fn colour(&mut self, span: Span, token: SyntaxType) {
		self.syntax_tokens.push(SyntaxToken {
			ty: token,
			modifiers: SyntaxModifiers::CONDITIONAL,
			span,
		});
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse(&mut self, walker: &mut Walker) {
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

		// This is set to `true` when a `defined` token is encountered, and it is reset to `false` upon the next
		// iteration.
		let mut previously_started_defined = false;

		// If this is set to `true`, that means that the parser has exited early because of a syntax error and we
		// want to invalidate the rest of the tokens, (if there are any).
		let mut invalidate_rest = false;

		'main: while !walker.is_done() {
			let (token, span) = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break 'main,
			};

			match token {
				ConditionToken::Num(num) if state == State::Operand => {
					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Num(*num),
						span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					state = State::AfterOperand;
					self.set_op_rhs_toggle();

					self.colour(span, SyntaxType::Number);
				}
				ConditionToken::Num(num) if state == State::AfterOperand => {
					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Num(*num),
						span,
					}));

					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));

					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Ident(s) if state == State::Operand => {
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
					self.set_op_rhs_toggle();

					// If we are parsing a `defined` but we are not in a group (which means we have no
					// parenthesis), we want to reset the flag back to false. If we are in a defined parenthesis
					// group, the closing parenthesis will take care of resetting the flag.
					if previously_started_defined {
						previously_started_defined = false;
						self.end_defined(span);
					}

					self.colour(span, SyntaxType::UncheckedIdent);
				}
				ConditionToken::Ident(s) if state == State::AfterOperand => {
					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Ident(Ident {
							name: s.clone(),
							span,
						}),
						span,
					}));

					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));

					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Sub if state == State::Operand => {
					self.push_operator(Op {
						span,
						ty: OpTy::Neg(false),
					});

					self.colour(span, SyntaxType::Operator);
				}
				ConditionToken::Not if state == State::Operand => {
					self.push_operator(Op {
						span,
						ty: OpTy::Not(false),
					});

					self.colour(span, SyntaxType::Operator);
				}
				ConditionToken::Flip if state == State::Operand => {
					self.push_operator(Op {
						span,
						ty: OpTy::Flip(false),
					});

					self.colour(span, SyntaxType::Operator);
				}
				ConditionToken::Not | ConditionToken::Flip
					if state == State::AfterOperand =>
				{
					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::InvalidBinOrPostOperator(span),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::LParen if state == State::Operand => {
					if previously_started_defined {
						let Some(Group::Defined(_, _, l_paren_span)) = self.groups.last_mut()  else {unreachable!();};
						*l_paren_span = Some(span);
					} else {
						self.set_op_rhs_toggle();
						self.operators.push_back(Op {
							span,
							ty: OpTy::ParenStart,
						});
						self.groups.push(Group::Paren(false, span));
					}

					self.colour(span, SyntaxType::Punctuation);
				}
				ConditionToken::LParen if state == State::AfterOperand => {
					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::RParen if state == State::AfterOperand => {
					match self.end_paren_defined(span) {
						Ok(_) => {}
						Err(_) => {
							invalidate_rest = true;
							break 'main;
						}
					}

					self.colour(span, SyntaxType::Punctuation);

					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`
				}
				ConditionToken::RParen if state == State::Operand => {
					let prev_op_span = self.get_previous_span();
					let just_started_paren = self.just_started_paren();
					match self.end_paren_defined(span) {
						Ok(_) => {}
						Err(_) => {
							invalidate_rest = true;
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
					} else {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundRParenInsteadOfOperand(
								prev_op_span.unwrap(),
								span,
							),
						))
					}

					state = State::AfterOperand;

					self.colour(span, SyntaxType::Punctuation);
				}
				ConditionToken::Defined if state == State::Operand => {
					self.push_operator(Op {
						span,
						ty: OpTy::DefinedStart,
					});
					self.groups.push(Group::Defined(false, span, None));
					previously_started_defined = true;

					self.colour(span, SyntaxType::Keyword);
				}
				ConditionToken::Defined if state == State::AfterOperand => {
					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::InvalidNum(_) => {
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Invalid(_) => {
					// We have encountered an unexpected token that's not allowed to be part of an expression.
					self.syntax_diags
						.push(Syntax::Expr(ExprDiag::FoundInvalidToken(span)));
					invalidate_rest = true;
					break 'main;
				}
				_ if state == State::AfterOperand => {
					self.push_operator(Op::from_token(token.clone(), span));
					state = State::Operand;

					self.colour(span, SyntaxType::Operator);
				}
				_ => unreachable!(),
			}

			// Reset the flag. We do this here to avoid having to sprinkle every branch other than the `Defined`
			// branch with a reset, as that would be needlessly verbose.
			match token {
				ConditionToken::Defined => {}
				_ => previously_started_defined = false,
			}

			walker.advance();
		}

		// If we break early because of a syntax error, we want to colour the rest of the tokens as invalid.
		if invalidate_rest {
			walker.advance();
			while let Some((_, span)) = walker.peek() {
				self.colour(span, SyntaxType::Invalid);
				walker.advance();
			}
		}

		// Close any open groups. Any groups still open must be missing a closing delimiter.
		if !self.groups.is_empty() {
			// The end position of this expression will be the end position of the last parsed item. This is
			// important because in the case of encountering an error, the relevant branches above will consume the
			// rest of the tokens since no further processing is done outside of this function. That means that
			// naively getting the last token span could potentially result in an incorrect span.
			let group_end = self.get_previous_span().unwrap().end_zero_width();

			// We don't take ownership of the groups because the `end_paren_defined()` method does that.
			while let Some(group) = self.groups.last() {
				match group {
					Group::Paren(_, l_paren) => {
						self.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedParens(*l_paren, group_end),
						));
					}
					Group::Defined(_, kw, l_paren) => {
						if let Some(l_paren) = l_paren {
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::UnclosedDefinedOp(
									*l_paren, group_end,
								),
							));
						} else {
							self.syntax_diags.push(Syntax::Expr(
								ExprDiag::ExpectedIdentAfterDefinedOp(
									kw.next_single_width(),
								),
							));
						}
					}
				}
				let _ = self.end_paren_defined(group_end);
			}
		}

		// If there is an open group, then all of the operators will have been already moved as part of the
		// ending function. However, if we didn't need to close any groups, we may have leftover operators which
		// still need moving.
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
					NodeTy::Num(num) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Num(num),
					}),
					NodeTy::Ident(ident) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Ident(ident),
					}),
				},
				Either::Right(op) => match op.ty {
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
					OpTy::Defined(has_inner, _l_paren, end) => {
						let expr = if has_inner {
							Some(pop_back(&mut stack))
						} else {
							None
						};

						stack.push_back(Expr {
							span: Span::new(op.span.start, end.end),
							ty: ExprTy::Defined {
								expr: expr.map(|e| Box::from(e)),
							},
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
					| OpTy::XorXor(has_rhs) => {
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
						unreachable!("Invalid operator {op:?} in conditional expression shunting yard stack. This operator should never be present in the final RPN stack.");
					}
				},
			}
		}

		if stack.len() > 1 {
			let expr = pop_back(&mut stack);
			stack.push_back(expr);
		}

		if stack.len() != 1 {
			unreachable!("After processing the conditional expression shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap())
	}
}
