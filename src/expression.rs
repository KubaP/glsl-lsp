#![allow(unused)]
use crate::{
	ast::{Either, Expr, Ident, Lit},
	lexer::{lexer, OpType, Spanned, Token},
};
use std::{collections::VecDeque, iter::Peekable, slice::Iter};

pub fn expr_parser(cst: Vec<Spanned<Token>>) -> Expr {
	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: VecDeque::new(),
	};
	parser.parse(cst);
	parser.create_ast()
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

struct Walker {
	cst: Vec<Spanned<Token>>,
	cursor: usize,
}

impl Walker {
	/// Returns the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<&Token> {
		self.cst.get(self.cursor).map(|(t, _)| t)
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	fn lookahead_1(&self) -> Option<&Token> {
		self.cst.get(self.cursor + 1).map(|(t, _)| t)
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	fn next(&mut self) -> Option<&Token> {
		// If we are successful in getting the token, advance the cursor.
		match self.cst.get(self.cursor) {
			Some((t, _)) => {
				self.cursor += 1;
				Some(t)
			}
			None => None,
		}
	}

	/// Returns whether the `Lexer` has reached the end of the token list.
	fn is_done(&self) -> bool {
		// We check that the cursor is equal to the length, because that means we have gone past the last token
		// of the string, and hence, we are done.
		self.cursor == self.cst.len()
	}
}

#[derive(Debug, PartialEq)]
enum Group {
	/// A bracket group, `(...)`.
	Bracket,
	/// An index operator `[...]`.
	Index,
	/// A function call `fn(...)`.
	Fn(usize),
}

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Expr, OpType>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<OpType>,
	/// Temporary stack to hold expression groups. The top-most entry is the group being currently parsed.
	groups: VecDeque<Group>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: OpType) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if *back == OpType::BracketStart
				|| *back == OpType::IndexStart
				|| *back == OpType::FnStart
			{
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				break;
			}

			if op.precedence() < back.precedence() {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
			} else {
				// If the precedence is greater, we aren't going to be moving any operators to the stack anymore,
				// so we can exit the loop.
				break;
			}
		}
		self.operators.push_back(op);
	}

	/// Registers the end of a bracket or function call group, popping any operators until the start of the group
	/// is reached.
	fn end_bracket_fn(&mut self) {
		// We've encountered a `)` delimiter, but we first want to check that we are actually within a group, i.e.
		// there was a start delimiter of some kind, and that the delimiter is a `(` as opposed to the other `[` or
		// `{` delimiters.
		//
		// Ok:  { ( )
		// Err: ( { )
		let current_group =
			match self.groups.back() {
				Some(g) => g,
				None => {
					println!("Found a `)` delimiter without a starting `(` delimiter!");
					return;
				}
			};
		if *current_group == Group::Index {
			println!("Found a `)` delimiter, but we still have an open `[` index operator!");
			return;
		}

		while self.operators.back().is_some() {
			let top_op = self.operators.back().unwrap();

			if *top_op == OpType::BracketStart {
				// We have reached the start of the current bracket group.

				// Sanity check; this should never happen.
				if let Group::Fn(_) = current_group {
					println!(
						"Mismatch between operator stack (OpType::BracketStart) and group stack (Group::Fn)!"
					);
					return;
				}

				// We remove the operator without pushing it to the stack. Bracket groups don't actually create an
				// AST node, they are just used to prioritise the order of binary expressions, hence no need for an
				// operator.
				self.operators.pop_back();
				self.groups.pop_back();
				break;
			} else if *top_op == OpType::FnStart {
				// We have reached the start of the current function call group.

				match current_group {
					Group::Fn(count) => {
						// We remove the operator and instead push a new operator which contains information about
						// how many of the previous expressions are part of the current function call group.
						//
						// Note: The first expression will always be the expression containing the function
						// identifier (hence the `+ 1`).
						self.operators.pop_back();
						self.stack.push_back(Either::Right(OpType::FnCall(
							count + 1,
						)));
						self.groups.pop_back();
						break;
					}
					// Sanity check; this should never happen.
					Group::Bracket => {
						println!(
							"Mismatch between operator stack (OpType::FnStart) and group stack (Group::Bracket)!"
						);
						return;
					}
					_ => unreachable!(),
				}
			} else if *top_op == OpType::IndexStart {
				// Sanity check; this should never happen.
				println!("Mismatch between operator stack (OpType::IndexStart) and group stack (Group::Bracket|Group::Fn)!");
				return;
			} else {
				// Any other operators get moved, since we are moving everything until we hit the start delimiter.
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
			}
		}
	}

	/// Registers the end of an index operator group, popping any operators until the start of the index group is
	/// reached.
	fn end_index(&mut self) {
		// We've encountered a `]` delimiter, but we first want to check that we are actually within a group, i.e.
		// there was a start delimiter of some kind, and that the delimiter is a `[` as opposed to the other `(` or
		// `{` delimiters.
		//
		// Ok:  ( [ ]
		// Err: [ ( ]
		let current_group =
			match self.groups.back() {
				Some(g) => g,
				None => {
					println!("Found a `]` delimiter without a starting `[` delimiter!");
					return;
				}
			};
		if *current_group == Group::Bracket {
			println!("Found a `]` delimiter, but we still have an open `(` bracket group!");
			return;
		} else if let Group::Fn(_) = current_group {
			println!("Found a `]` delimiter, but we still have an open `(` function call!");
			return;
		}

		while self.operators.back().is_some() {
			let top_op = self.operators.back().unwrap();

			if *top_op == OpType::IndexStart {
				// We have reached the start of the current index group.

				// We remove the operator and push it to the stack.
				self.operators.pop_back();
				self.groups.pop_back();
				self.stack.push_back(Either::Right(OpType::Index));
				break;
			} else if *top_op == OpType::BracketStart {
				// Sanity check; this should never happen.
				println!("Mismatch between operator stack (OpType::BracketStart) and group stack (Group::Index)!");
				return;
			} else if *top_op == OpType::FnStart {
				// Sanity check; this should never happen.
				println!("Mismatch between operator stack (OpType::FnStart) and group stack (Group::Index)!");
				return;
			} else {
				// Any other operators get moved, since we are moving everything until we hit the start delimiter.
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
			}
		}
	}

	/// Increases the arity of the top-most current function call.
	fn increase_arity(&mut self) {
		// We've come across a `,` which is only valid inside of a function call group. Check that we are in a
		// function call group, otherwise this is an error.
		if let Some(current_group) = self.groups.back_mut() {
			match current_group {
				Group::Fn(count) => {
					*count += 1;

					// Now that the arity has increased, and we are parsing the next expression, we want to move all
					// existing operators up to the function call start delimiter to the stack, to clear it for the next
					// expression.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if *back == OpType::FnStart {
							break;
						}

						let moved_op = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved_op));
					}
				}
				_ => {
					println!("Found a `,` expression delimiter outside of a function call!");
					return;
				}
			}
		} else {
			println!(
				"Found a `,` expresion delimiter outside of a function call!"
			);
			return;
		}
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse(&mut self, cst: Vec<Spanned<Token>>) {
		#[derive(PartialEq)]
		enum State {
			/// We are looking for either a) a prefix operator, b) an atom, c) bracket group start.
			Operand,
			/// We are looking for either a) a postfix operator, b) an index operator start or end, c) a binary
			/// operator, d) bracket group end, e) a comma, f) end of expression.
			AfterOperand,
		}
		let mut state = State::Operand;
		let mut walker = Walker { cst, cursor: 0 };

		'main: while !walker.is_done() {
			let token = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break,
			};

			match token {
				Token::Num { .. } | Token::Bool(_)
					if state == State::Operand =>
				{
					// We switch state since after an atom, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					self.stack.push_back(match Lit::parse(token) {
						Ok(l) => Either::Left(Expr::Lit(l)),
						Err(_) => Either::Left(Expr::Invalid),
					});
					state = State::AfterOperand;
				}
				Token::Ident(s) if state == State::Operand => {
					// Depending on what is after the identifier we may want to handle member access or function
					// calls.
					if let Some(lookahead) = walker.lookahead_1() {
						if *lookahead == Token::Dot {
							let mut members = Vec::new();

							// Push the current initial identifier.
							members.push(match Ident::parse_name(s) {
								Ok(i) => i,
								Err(_) => {
									println!(
										"Expected an identifier, found a type!"
									);
									return;
								}
							});
							walker.advance();

							// Loop, looking for a `.ident`, until either:
							// a) there is no input left,
							// b) there is no following dot
							// In both these cases, we produce a complete member access expression.
							//
							// In the case that there is a dot but it's not followed by an identifier (or anything
							// period), then we error.
							'member: loop {
								// First, check if there is a dot next.
								let dot = match walker.peek() {
									Some(t) => t,
									None => break 'member,
								};
								if *dot != Token::Dot {
									// We've reached the end of the member access, so we can create an expression
									// for it. We rerun the main loop on the current token since it will match
									// against a different main branch, such as the operator branch. We don't
									// advance the cursor.
									self.stack.push_back(Either::Left(
										Expr::Member(members),
									));
									state = State::AfterOperand;
									continue 'main;
								}

								// There is a dot, so we are now expecting an identifier.
								walker.advance();
								let ident = match walker.peek() {
									Some(t) => t,
									None => {
										println!("Expected an identifier after the `.`, found the end of input instead!");
										break 'member;
									}
								};
								if let Token::Ident(s) = ident {
									// There is an identifier after the dot, so we can add it to the list of
									// members. We continue looping in case there is another `.ident` afterwards.
									members.push(match Ident::parse_name(s) {
										Ok(i) => i,
										Err(_) => {
											println!("Expected an identifier, found a type!");
											return;
										}
									});
									walker.advance();
									continue 'member;
								} else {
									// There is a dot, but afterwards there is no identifier. This is an error.
									println!("Expected an identifier after the `.`, found something else instead!");
									return;
								}
							}

							// We've reached the end of the token list, so we can create an expression.
							self.stack
								.push_back(Either::Left(Expr::Member(members)));
						} else if *lookahead == Token::LParen {
							// We push the function identifier to the stack.
							self.stack.push_back(match Ident::parse_name(s) {
								Ok(i) => Either::Left(Expr::Ident(i)),
								Err(_) => Either::Left(Expr::Invalid),
							});
							// Consume the identifier and `(`.
							walker.advance();
							walker.advance();

							if let Some(lookahead_2) = walker.peek() {
								if *lookahead_2 == Token::RParen {
									// We have a function call with zero arguments.

									// We can push the appropriate function call operator straight away since we
									// know there's nothing else to parse. We switch state since we now expect
									// either an operator or an end of expression.
									self.operators.push_back(OpType::FnCall(1));
									walker.advance();
									state = State::AfterOperand;
									continue 'main;
								} else {
									// We have a function call with at least one argument.

									// We push a function call group start to the operator stack, and continue
									// looking for an operand, so we don't switch state.
									self.operators.push_back(OpType::FnStart);
									self.groups.push_back(Group::Fn(1));
									continue 'main;
								}
							} else {
								println!("Expected function call arguments or `)`, found end of input instead!");
								return;
							}
						} else if *lookahead == Token::Comma {
							// We push the identifier to the stack.
							self.stack.push_back(match Ident::parse_name(s) {
								Ok(i) => Either::Left(Expr::Ident(i)),
								Err(_) => Either::Left(Expr::Invalid),
							});
							// We have an operand, followed by a comma. If we are parsing a function call at all
							// currently, then we can increase the arity of the top-most one. If not, then this is
							// an error.
							self.increase_arity();

							// Consume the identifier and `,`.
							walker.advance();
							walker.advance();

							// Don't switch state, since after a comma, we will be expecting another operand.
							continue 'main;
						} else {
							// There is no following dot, so this is just a simple identifier.
							self.stack.push_back(match Ident::parse_name(s) {
								Ok(i) => Either::Left(Expr::Ident(i)),
								Err(_) => Either::Left(Expr::Invalid),
							});
						}
					} else {
						// There is no following dot, so this is just a simple identifier.
						self.stack.push_back(match Ident::parse_name(s) {
							Ok(i) => Either::Left(Expr::Ident(i)),
							Err(_) => Either::Left(Expr::Invalid),
						});
					}
					state = State::AfterOperand;
				}
				Token::Num { .. } | Token::Bool(_) | Token::Ident(_)
					if state == State::AfterOperand =>
				{
					// This is an error, e.g. `..1 1` instead of `..1 + 1`.
					println!("Expected a postfix, index or binary operator, or the end of expression, found an atom instead!");
					return;
				}
				Token::Op(op) if state == State::Operand => match op {
					// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
					// state since after a prefix operator, we are still looking for an operand atom.
					OpType::Sub => self.push_operator(OpType::Neg),
					OpType::Not => self.push_operator(OpType::Not),
					OpType::Flip => self.push_operator(OpType::Flip),
					OpType::AddAdd => self.push_operator(OpType::AddAddPre),
					OpType::SubSub => self.push_operator(OpType::SubSubPre),
					_ => {
						// This is an error, e.g. `..*1` instead of `..-1`.
						println!("Expected an atom or a prefix operator, found a non-prefix operator instead!");
						return;
					}
				},
				Token::Op(op) if state == State::AfterOperand => match op {
					OpType::Flip | OpType::Not => {
						// These operators cannot be directly after an atom.
						println!("Expected a postfix, index or binary operator, found a prefix operator instead!");
						return;
					}
					// These operators are postfix operators. We don't switch state since after a postfix operator,
					// we are still looking for a binary operator or the end of expression, i.e.
					// `..i++ - i` rather than `..i++ i`.
					OpType::AddAdd => {
						self.push_operator(OpType::AddAddPost);
					}
					OpType::SubSub => {
						self.push_operator(OpType::SubSubPost);
					}
					// Any other operators can be part of a binary expression. We switch state since after a binary
					// operator we are expecting an operand.
					_ => {
						self.push_operator(*op);
						state = State::Operand;
					}
				},
				Token::LParen if state == State::Operand => {
					// We don't switch state since after a `(`, we are expecting an operand, i.e.
					// `..+ (1 *` rather than `..+ (*`.
					self.operators.push_back(OpType::BracketStart);
					self.groups.push_back(Group::Bracket);
				}
				Token::LParen if state == State::AfterOperand => {
					// This is an error. e.g. `..1 (` instead of `..1 + (`.
					println!("Expected an operator or the end of expression, found `(` instead!");
					return;
				}
				Token::RParen if state == State::AfterOperand => {
					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`.
					self.end_bracket_fn();
				}
				Token::RParen if state == State::Operand => {
					// This is an error, e.g. `..+ )` instead of `..+ 1)`.
					println!("Expected an atom or a prefix operator, found `)` instead!");
					return;
				}
				Token::LBracket if state == State::AfterOperand => {
					// We switch state since after a `[`, we are expecting an operand, i.e.
					// `i[5 +..` rather than `i[+..`.
					self.operators.push_back(OpType::IndexStart);
					self.groups.push_back(Group::Index);
					state = State::Operand;
				}
				Token::LBracket if state == State::Operand => {
					// This is an error, e.g. `..+ [` instead of `..+ i[`.
					println!("Expected an atom or a prefix operator, found `[` instead!");
					return;
				}
				Token::RBracket if state == State::AfterOperand => {
					// We don't switch state since after a `]`, we are expecting an operator, i.e.
					// `..] + 5` instead of `..] 5`.
					self.end_index();
				}
				Token::RBracket if state == State::Operand => {
					// This is an error, e.g. `..+ ]` instead of `..+ 1]`.
					println!("Expected an atom or a prefix operator, found `]` instead!");
					return;
				}
				Token::Comma if state == State::AfterOperand => {
					// We switch state since after a comma (which delineates an expression), we're effectively
					// starting a new expression which must start with an operand, i.e.
					// `.., 5 + 6` instead of `.., + 6`.
					// TODO: Check if the next token is a `)` or a `}` and in such case don't increase the arity
					self.increase_arity();
					state = State::Operand;
				}
				Token::Comma if state == State::Operand => {
					// This is an error, e.g. `..+ ,` instead of `..+ 1,`.
					println!("Expected an atom or a prefix operator, found `,` instead!");
					return;
				}
				_ => {
					// We have a token that's not allowed to be part of an expression.
					// FIXME: Deal with this properly.
					println!("Unexpected token found: {token:?}");
					return;
				}
			}

			walker.advance();
		}

		// Move any remaining operators onto the stack.
		while let Some(op) = self.operators.pop_back() {
			// FIXME: Deal with unclosed delimiters
			self.stack.push_back(Either::Right(op))
		}
	}

	/// Converts the internal RPN stack into a singular `Expr` node, which contains the entire expression.
	fn create_ast(&mut self) -> Expr {
		let mut stack = VecDeque::new();

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the x-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(e) = self.stack.pop_front() {
			match e {
				Either::Left(e) => stack.push_back(e),
				Either::Right(op) => match op {
					OpType::Neg => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Neg(Box::from(expr)));
					}
					OpType::Flip => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Flip(Box::from(expr)));
					}
					OpType::Not => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Not(Box::from(expr)));
					}
					OpType::AddAddPre => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Prefix(
							Box::from(expr),
							OpType::Add,
						));
					}
					OpType::SubSubPre => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Prefix(
							Box::from(expr),
							OpType::Sub,
						));
					}
					OpType::AddAddPost => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Postfix(
							Box::from(expr),
							OpType::Add,
						));
					}
					OpType::SubSubPost => {
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Postfix(
							Box::from(expr),
							OpType::Sub,
						));
					}
					OpType::FnCall(count) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap());
						}

						// Get the identifier (which is the first expression).
						let ident = if let Expr::Ident(i) =
							args.pop_front().unwrap()
						{
							i
						} else {
							panic!("The first expression of a function call operator is not an identifier!");
						};

						stack.push_back(Expr::Fn {
							ident,
							args: args.into(),
						});
					}
					OpType::Index => {
						let i = stack.pop_back().unwrap();
						let expr = stack.pop_back().unwrap();
						stack.push_back(Expr::Index {
							item: Box::from(expr),
							i: Box::from(i),
						});
					}
					OpType::Add
					| OpType::Sub
					| OpType::Mul
					| OpType::Div
					| OpType::Rem
					| OpType::And
					| OpType::Or
					| OpType::Xor
					| OpType::LShift
					| OpType::RShift
					| OpType::EqEq
					| OpType::NotEq
					| OpType::Gt
					| OpType::Lt
					| OpType::Ge
					| OpType::Le
					| OpType::AndAnd
					| OpType::OrOr
					| OpType::XorXor
					| OpType::AddEq
					| OpType::SubEq
					| OpType::MulEq
					| OpType::DivEq
					| OpType::RemEq
					| OpType::AndEq
					| OpType::OrEq
					| OpType::XorEq
					| OpType::LShiftEq
					| OpType::RShiftEq => {
						let right = stack.pop_back().unwrap();
						let left = stack.pop_back().unwrap();
						stack.push_back(Expr::Binary {
							left: Box::from(left),
							op,
							right: Box::from(right),
						});
					}
					_ => {
						panic!("Invalid operator {op} in shunting yard stack. This operator should never be present in the final RPN output stack.");
					}
				},
			}
		}

		#[cfg(debug_assertions)]
		if stack.len() != 1 {
			panic!("After processing the shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		stack.pop_back().unwrap()
	}
}

impl OpType {
	/// Returns the precedence of the operator.
	fn precedence(&self) -> u8 {
		match self {
			Self::AddAddPost | Self::SubSubPost => 31,
			Self::AddAddPre
			| Self::SubSubPre
			| Self::Neg
			| Self::Flip
			| Self::Not => 29,
			Self::Mul | Self::Div | Self::Rem => 27,
			Self::Add | Self::Sub => 25,
			Self::LShift | Self::RShift => 23,
			Self::Lt | Self::Gt | Self::Le | Self::Ge => 21,
			Self::EqEq | Self::NotEq => 19,
			Self::And => 17,
			Self::Xor => 15,
			Self::Or => 13,
			Self::AndAnd => 11,
			Self::XorXor => 9,
			Self::OrOr => 7,
			// TODO: Ternary
			Self::AddEq
			| Self::SubEq
			| Self::MulEq
			| Self::DivEq
			| Self::RemEq
			| Self::AndEq
			| Self::XorEq
			| Self::OrEq
			| Self::LShiftEq
			| Self::RShiftEq => 3,
			// These two should always be converted to the *Pre or *Post versions in the shunting yard.
			Self::AddAdd | Self::SubSub => panic!("OpType::AddAdd | OpType::SubSub do not have precedence values because they should never be passed into this function. Something has gone wrong!"),
			// These are never directly checked for precedence, but rather have special branches.
			Self::BracketStart | Self::FnStart | Self::FnCall(_) | Self::IndexStart | Self::Index => {
				panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!")
			},
		}
	}
}

// Purely used for debugging the parsed expressions.
impl std::fmt::Display for ShuntingYard {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for node in self.stack.iter() {
			match node {
				Either::Left(e) => write!(f, "{e} ")?,
				Either::Right(op) => write!(f, "{op} ")?,
			}
		}
		Ok(())
	}
}

impl std::fmt::Display for OpType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			// Maths
			Self::Add => write!(f, "+"),
			Self::Sub => write!(f, "-"),
			Self::Mul => write!(f, "*"),
			Self::Div => write!(f, "/"),
			Self::Rem => write!(f, "%"),
			Self::And => write!(f, "&"),
			Self::Or => write!(f, "|"),
			Self::Xor => write!(f, "^"),
			Self::LShift => write!(f, "<<"),
			Self::RShift => write!(f, ">>"),
			Self::AddEq => write!(f, "+="),
			Self::SubEq => write!(f, "-="),
			Self::MulEq => write!(f, "*="),
			Self::DivEq => write!(f, "/="),
			Self::RemEq => write!(f, "%="),
			Self::AndEq => write!(f, "&="),
			Self::OrEq => write!(f, "|="),
			Self::XorEq => write!(f, "^="),
			Self::LShiftEq => write!(f, "<<="),
			Self::RShiftEq => write!(f, ">>="),
			Self::Flip => write!(f, "~"),
			Self::AddAdd => write!(f, "NOP"),
			Self::SubSub => write!(f, "NOP"),
			//
			// Comparison
			Self::EqEq => write!(f, "=="),
			Self::NotEq => write!(f, "!="),
			Self::Gt => write!(f, ">"),
			Self::Lt => write!(f, "<"),
			Self::Ge => write!(f, ">="),
			Self::Le => write!(f, "<="),
			Self::AndAnd => write!(f, "&&"),
			Self::OrOr => write!(f, "||"),
			Self::XorXor => write!(f, "^^"),
			Self::Not => write!(f, "!"),
			//
			// Shunting Yard
			Self::Neg => write!(f, "neg"),
			Self::AddAddPre => write!(f, "++pre"),
			Self::AddAddPost => write!(f, "++post"),
			Self::SubSubPre => write!(f, "--pre"),
			Self::SubSubPost => write!(f, "--post"),
			Self::BracketStart | Self::FnStart | Self::IndexStart => {
				write!(f, "")
			}
			Self::Index => write!(f, "index"),
			Self::FnCall(count) => write!(f, "FN:{count}"),
		}
	}
}

/// Asserts the expression output of the `expr_parser()` matches the right hand side.
macro_rules! assert_expr {
	($source:expr, $rest: expr) => {
		assert_eq!(expr_parser(lexer($source)), $rest);
	};
}

#[test]
#[rustfmt::skip]
fn binaries() {
	// Single operator
	assert_expr!("5 + 1",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: OpType::Add,
			right: Box::from(Expr::Lit(Lit::Int(1)))
		}
	);
	assert_expr!("ident * 100.4",
		Expr::Binary {
			left: Box::from(Expr::Ident(Ident("ident".into()))),
			op: OpType::Mul,
			right: Box::from(Expr::Lit(Lit::Float(100.4)))
		}
	);
	assert_expr!("30 << 8u",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(30))),
			op: OpType::LShift,
			right: Box::from(Expr::Lit(Lit::UInt(8)))
		}
	);

	// Multiple operators
	assert_expr!("5 + 1 / 3",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: OpType::Add,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(1))),
				op: OpType::Div,
				right: Box::from(Expr::Lit(Lit::Int(3)))
			})
		}
	);
	assert_expr!("5 + 1 / 3 * i",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: OpType::Add,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(1))),
				op: OpType::Div,
				right: Box::from(Expr::Binary {
					left: Box::from(Expr::Lit(Lit::Int(3))),
					op: OpType::Mul,
					right: Box::from(Expr::Ident(Ident("i".into())))
				})
			})
		}
	);
	assert_expr!("5 + 1 == true * i",
		Expr::Binary {
			left: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: OpType::Add,
				right: Box::from(Expr::Lit(Lit::Int(1)))
			}),
			op: OpType::EqEq,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Bool(true))),
				op: OpType::Mul,
				right: Box::from(Expr::Ident(Ident("i".into())))
			})
		}
	);
}

#[test]
#[rustfmt::skip]
fn brackets() {
	assert_expr!("(5 + 1) * 8",
		Expr::Binary {
			left: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: OpType::Add,
				right: Box::from(Expr::Lit(Lit::Int(1))),
			}),
			op: OpType::Mul,
			right: Box::from(Expr::Lit(Lit::Int(8)))
		}
	);
	assert_expr!("((5 + 1) < 100) * 8",
		Expr::Binary {
			left: Box::from(Expr::Binary {
				left: Box::from(Expr::Binary {
					left: Box::from(Expr::Lit(Lit::Int(5))),
					op: OpType::Add,
					right: Box::from(Expr::Lit(Lit::Int(1))),
				}),
				op: OpType::Lt,
				right: Box::from(Expr::Lit(Lit::Int(100))),
			}),
			op: OpType::Mul,
			right: Box::from(Expr::Lit(Lit::Int(8)))
		}
	);
}

#[test]
#[rustfmt::skip]
fn unaries() {
	// Single operator
	assert_expr!("-5", Expr::Neg(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("~5", Expr::Flip(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("!5", Expr::Not(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("++5", Expr::Prefix(Box::from(Expr::Lit(Lit::Int(5))), OpType::Add));
	assert_expr!("--5", Expr::Prefix(Box::from(Expr::Lit(Lit::Int(5))), OpType::Sub));
	assert_expr!("5++", Expr::Postfix(Box::from(Expr::Lit(Lit::Int(5))), OpType::Add));
	assert_expr!("5--", Expr::Postfix(Box::from(Expr::Lit(Lit::Int(5))), OpType::Sub));
	
	// Multiple operators
	assert_expr!("- -5",
		Expr::Neg(Box::from(
			Expr::Neg(Box::from(Expr::Lit(Lit::Int(5))))
		))
	);
	assert_expr!("- - -5",
		Expr::Neg(Box::from(
			Expr::Neg(Box::from(
				Expr::Neg(Box::from(Expr::Lit(Lit::Int(5))))
			))
		))
	);
	assert_expr!("!!5",
		Expr::Not(Box::from(
			Expr::Not(Box::from(Expr::Lit(Lit::Int(5))))
		))
	);
	assert_expr!("++++5",
		Expr::Prefix(
			Box::from(
				Expr::Prefix(
					Box::from(Expr::Lit(Lit::Int(5))),
					OpType::Add
				)
			),
			OpType::Add
		)
	);
	assert_expr!("--5++",
		Expr::Prefix(
			Box::from(Expr::Postfix(
				Box::from(Expr::Lit(Lit::Int(5))),
				OpType::Add
			)),
			OpType::Sub
		)
	);
}

#[test]
#[rustfmt::skip]
fn fn_calls() {
	assert_expr!("fn()",
		Expr::Fn { ident: Ident("fn".into()), args: vec![] }
	);
	assert_expr!("fu_nc(1)",
		Expr::Fn { ident: Ident("fu_nc".into()), args: vec![Expr::Lit(Lit::Int(1))] }
	);
	assert_expr!("fn(5 + 1, i << 6)",
		Expr::Fn { ident: Ident("fn".into()), args: vec![
			Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: OpType::Add,
				right: Box::from(Expr::Lit(Lit::Int(1))),
			},
			Expr::Binary {
				left: Box::from(Expr::Ident(Ident("i".into()))),
				op: OpType::LShift,
				right: Box::from(Expr::Lit(Lit::Int(6))),
			},
		]}
	);
}

#[test]
#[rustfmt::skip]
fn indexes() {
	assert_expr!("i[0]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Box::from(Expr::Lit(Lit::Int(0)))
	});
	assert_expr!("s[z+1]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("s".into()))),
		i: Box::from(Expr::Binary {
			left: Box::from(Expr::Ident(Ident("z".into()))),
			op: OpType::Add,
			right: Box::from(Expr::Lit(Lit::Int(1)))
		})
	});
	assert_expr!("i[y[5]]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("y".into()))),
			i: Box::from(Expr::Lit(Lit::Int(5)))
		})
	});
}

#[test]
#[rustfmt::skip]
fn complex() {
	assert_expr!("func(i[9], foo-- -6)", Expr::Fn {
		ident: Ident("func".into()),
		args: vec![
			Expr::Index {
				item: Box::from(Expr::Ident(Ident("i".into()))),
				i: Box::from(Expr::Lit(Lit::Int(9))),
			},
			Expr::Binary {
				left: Box::from(
					Expr::Postfix(Box::from(Expr::Ident(Ident("foo".into()))), OpType::Sub)
				),
				op: OpType::Sub,
				right: Box::from(Expr::Lit(Lit::Int(6)))
			}
		]
	});
	assert_expr!("true << i[func((1 + 1) * 5.0)]", Expr::Binary {
		left: Box::from(Expr::Lit(Lit::Bool(true))),
		op: OpType::LShift,
		right: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("i".into()))),
			i: Box::from(Expr::Fn {
				ident: Ident("func".into()),
				args: vec![
					Expr::Binary {
						left: Box::from(Expr::Binary {
							left: Box::from(Expr::Lit(Lit::Int(1))),
							op: OpType::Add,
							right: Box::from(Expr::Lit(Lit::Int(1))),
						}),
						op: OpType::Mul,
						right: Box::from(Expr::Lit(Lit::Float(5.0)))
					}
				]
			})
		})
	});
}
