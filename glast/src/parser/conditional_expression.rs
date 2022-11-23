use super::{
	ast::conditional::{BinOp, BinOpTy, Expr, ExprTy, PreOp, PreOpTy},
	ast::Ident,
	SyntaxToken,
};
use crate::{
	diag::{ExprDiag, Semantic, Syntax},
	lexer::preprocessor::ConditionToken,
	Either, Span, Spanned,
};
use std::collections::VecDeque;

/// Tries to parse a conditional directive expression.
pub(super) fn cond_parser(
	tokens: Vec<Spanned<ConditionToken>>,
) -> (
	Option<Expr>,
	Vec<Syntax>,
	Vec<Semantic>,
	Vec<Spanned<SyntaxToken>>,
) {
	let mut walker = Walker { tokens, cursor: 0 };

	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		// If we are at the end of the token stream, we can return early with nothing.
		None => return (None, vec![], vec![], vec![]),
	};

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		start_position,
		paren_groups: Vec::new(),
		syntax_diags: Vec::new(),
		semantic_diags: Vec::new(),
		syntax_tokens: Vec::new(),
	};
	parser.parse(&mut walker);

	if let Some(expr) = parser.create_ast() {
		(
			Some(expr),
			parser.syntax_diags,
			parser.semantic_diags,
			parser.syntax_tokens,
		)
	} else {
		(None, parser.syntax_diags, parser.semantic_diags, vec![])
	}
}

struct Walker {
	tokens: Vec<Spanned<ConditionToken>>,
	cursor: usize,
}

impl Walker {
	fn peek(&self) -> Option<Spanned<&ConditionToken>> {
		self.tokens.get(self.cursor).map(|(t, s)| (t, *s))
	}

	fn get(&self) -> Option<Spanned<ConditionToken>> {
		self.tokens.get(self.cursor).cloned()
	}

	fn advance(&mut self) {
		self.cursor += 1;
	}

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
	Defined(bool),
	/// The `(` token.
	ParenStart,
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis,
	/// - `1` - The span of the opening parenthesis,
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	Paren(bool, Span, Span),
}

impl Op {
	/// Converts from a lexer `OpTy` token to the `Op2` type used in this expression parser.
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
					unreachable!("[Op::from_token] Given a `token` which should never be handled by this function.")
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
			_ => panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
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
				_ => unreachable!("[Op::to_bin_op] Given a `ty` which should not be handled here.")
			};

		BinOp {
			span: self.span,
			ty,
		}
	}
}

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Node, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// The start position of the first item in this expression.
	start_position: usize,
	/// Parenthesis groups.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis.
	/// - `1` - The span of the opening parenthesis.
	paren_groups: Vec<(bool, Span)>,

	/// Syntax diagnostics encountered during the parser execution.
	syntax_diags: Vec<Syntax>,
	/// Semantic diagnostics encountered during the parser execution, (these will only be related to macros).
	semantic_diags: Vec<Semantic>,

	/// Syntax highlighting tokens created during the parser execution.
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
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
				OpTy::ParenStart => break,
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

	/// Registers the end of a bracket group, popping any operators until the start of the group is reached.
	fn end_bracket(
		&mut self,
		end_span: Span,
		/* r_comments: Comments, */
	) -> Result<(), ()> {
		let (has_inner, l_paren) = if !self.paren_groups.is_empty() {
			self.paren_groups.remove(self.paren_groups.len() - 1)
		} else {
			return Err(());
		};

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

		Ok(())
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
		if let Some((b, _)) = self.paren_groups.last_mut() {
			*b = true;
		}
	}

	/// Returns whether we have just started a parenthesis group.
	fn just_started_paren(&self) -> bool {
		if let Some((has_inner, _)) = self.paren_groups.last() {
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

	fn colour(&mut self, _walker: &Walker, span: Span, token: SyntaxToken) {
		self.syntax_tokens.push((token, span));
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

		'main: while !walker.is_done() {
			let (token, span) = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break 'main,
			};

			match token {
				ConditionToken::Num(num) if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Number);

					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Num(*num),
						span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					state = State::AfterOperand;
					self.set_op_rhs_toggle();
				}
				ConditionToken::Num(num) if state == State::AfterOperand => {
					self.colour(walker, span, SyntaxToken::Number);

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

					// We don't change state since even though we found an operand instead of an operator, after
					// this operand we will still be expecting an operator.
				}
				ConditionToken::Ident(s) if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::UncheckedIdent);

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
				}
				ConditionToken::Ident(s) if state == State::AfterOperand => {
					self.colour(walker, span, SyntaxToken::UncheckedIdent);

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

					// We don't change state since even though we found an operand instead of an operator, after
					// this operand we will still be expecting an operator.
				}
				ConditionToken::Sub if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Operator);
					self.push_operator(Op {
						span,
						ty: OpTy::Neg(false),
					});
				}
				ConditionToken::Not if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Operator);
					self.push_operator(Op {
						span,
						ty: OpTy::Not(false),
					});
				}
				ConditionToken::Flip if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Operator);
					self.push_operator(Op {
						span,
						ty: OpTy::Flip(false),
					});
				}
				ConditionToken::Not | ConditionToken::Flip
					if state == State::AfterOperand =>
				{
					self.colour(walker, span, SyntaxToken::Operator);
					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::InvalidBinOrPostOperator(span),
					));
					break 'main;
				}
				ConditionToken::LParen if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Punctuation);
					self.set_op_rhs_toggle();
					self.operators.push_back(Op {
						span,
						ty: OpTy::ParenStart,
					});
					self.paren_groups.push((false, span));
				}
				ConditionToken::LParen if state == State::AfterOperand => {
					self.colour(walker, span, SyntaxToken::Punctuation);
					self.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));
					break 'main;
				}
				ConditionToken::RParen if state == State::AfterOperand => {
					self.colour(walker, span, SyntaxToken::Punctuation);
					match self.end_bracket(span) {
						Ok(_) => {}
						Err(_) => break 'main,
					}

					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`
				}
				ConditionToken::RParen if state == State::Operand => {
					self.colour(walker, span, SyntaxToken::Punctuation);
					let prev_op_span = self.get_previous_span();
					let just_started_paren = self.just_started_paren();
					match self.end_bracket(span) {
						Ok(_) => {}
						Err(_) => break 'main,
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
				}
				ConditionToken::InvalidNum(_) => {
					self.colour(walker, span, SyntaxToken::Invalid);
					// FIXME: Since the calling code doesn't do any further iteration, we need to syntax highlight
					// the invalid tokens here, until we run out.
					break 'main;
				}
				ConditionToken::Invalid(_) | ConditionToken::Defined => {
					// We have encountered an unexpected token that's not allowed to be part of an expression.
					self.syntax_diags
						.push(Syntax::Expr(ExprDiag::FoundInvalidToken(span)));
					// FIXME: Since the calling code doesn't do any further iteration, we need to syntax highlight
					// the invalid tokens here, until we run out.
					break 'main;
				}
				_ if state == State::AfterOperand => {
					self.colour(walker, span, SyntaxToken::Operator);
					self.push_operator(Op::from_token(token.clone(), span));
					state = State::Operand;
				}
				_ => unreachable!(),
			}

			walker.advance();
		}

		// qe may have leftover operators which need moving.
		while let Some(op) = self.operators.pop_back() {
			self.stack.push_back(Either::Right(op));
		}
	}

	/// Converts the internal RPN stack into a singular `Expr` node, which contains the entire expression.
	fn create_ast(&mut self) -> Option<Expr> {
		if self.stack.len() == 0 {
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
					OpTy::Paren(has_inner, l_paren, end) => {
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
