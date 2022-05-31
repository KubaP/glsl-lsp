#![allow(unused)]
use crate::{
	ast::{Either, Expr, Ident, Lit},
	lexer::{OpType, Spanned, Token},
};
use std::{collections::VecDeque, iter::Peekable, slice::Iter};

pub fn expr_parser(cst: Vec<Spanned<Token>>) {
	let mut parser = ShuntingYard {
		stack: Vec::new(),
		operators: VecDeque::new(),
		arity: VecDeque::new(),
	};
	parser.parse(cst);

	println!("{parser}");
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

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: Vec<Either<Expr, OpType>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<OpType>,
	/// Temporary stack to hold the number of arguments any function calls are holding.
	arity: VecDeque<usize>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: OpType) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if *back == OpType::GroupStart || *back == OpType::FnStart {
				// Group start operators always have the highest precedence, so we don't need to check further.
				break;
			}

			if op.precedence() < back.precedence() {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push(Either::Right(moved_op));
			} else {
				// If the precedence is greater, we aren't going to be moving any operators to the stack anymore,
				// so we can exit the loop.
				break;
			}
		}
		self.operators.push_back(op);
	}

	/// Registers the start of a bracket group.
	fn start_group(&mut self) {
		self.operators.push_back(OpType::GroupStart);
	}

	/// Registers the start of a function call group.
	fn start_fn(&mut self) {
		self.operators.push_back(OpType::FnStart);
		self.arity.push_back(1);
	}

	/// Registers the end of a bracket group, popping any operators until the start of the last bracket group is
	/// reached.
	fn end_group(&mut self) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if *back == OpType::GroupStart {
				// We have reached the end of the current group. We remove the operator without pushing it to the
				// stack since it only functions as a flag, rather than as an actual operator.
				self.operators.pop_back();
				break;
			} else if *back == OpType::FnStart {
				// We have reached the end of the current function call group. We remove the operator and instead
				// push a new operator which contains information about how many of the previous expressions are
				// part of the current function call group.
				//
				// Note: The first expression will always be the expression containing the function identifier
				// (hence the `+ 1`).
				self.operators.pop_back();
				let count = self.arity.pop_back().unwrap();
				self.stack.push(Either::Right(OpType::FnCall(count + 1)));
				break;
			} else {
				// Any other operators get moved.
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push(Either::Right(moved_op));
			}
		}
	}

	/// Increases the arity of the top-most current function call.
	fn increase_arity(&mut self) {
		if let Some(count) = self.arity.back_mut() {
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
				self.stack.push(Either::Right(moved_op));
			}
		} else {
			println!(
				"Found a `,` outside of a function call. This is invalid!"
			);
			return;
		}
	}

	fn parse(&mut self, cst: Vec<Spanned<Token>>) {
		// `true` if we are looking for an operand (which includes parsing prefix operators). `false` if we are
		// looking for an operator for a binary expression (or alternatively the end of the expression).
		let mut operand_state = true;
		let mut walker = Walker { cst, cursor: 0 };

		'main: while !walker.is_done() {
			let token = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break,
			};

			match token {
				Token::Num { .. } | Token::Bool(_) if operand_state => {
					if let Some(lookahead) = walker.lookahead_1() {
						if *lookahead == Token::Comma {
							self.stack.push(match Lit::parse(token) {
								Ok(l) => Either::Left(Expr::Lit(l)),
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
							// There is no following comma, so this is just a simple literal.
							self.stack.push(match Lit::parse(token) {
								Ok(l) => Either::Left(Expr::Lit(l)),
								Err(_) => Either::Left(Expr::Invalid),
							});
						}
					} else {
						// There is no following comma, so this is just a simple literal.
						self.stack.push(match Lit::parse(token) {
							Ok(l) => Either::Left(Expr::Lit(l)),
							Err(_) => Either::Left(Expr::Invalid),
						});
					}
					// We are expecting an operand, so we can move the literal to the stack immediately.
					// We toggle the state so that we're now looking for an operator.

					operand_state = false;
				}
				Token::Ident(s) if operand_state => {
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
									self.stack.push(Either::Left(
										Expr::Member(members),
									));
									operand_state = false;
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
								.push(Either::Left(Expr::Member(members)));
						} else if *lookahead == Token::LParen {
							// We push the function identifier to the stack.
							self.stack.push(match Ident::parse_name(s) {
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
									operand_state = false;
									continue 'main;
								} else {
									// We have a function call with at least one argument.

									// We push a function call group start to the operator stack, and continue
									// looking for an operand, so we don't switch state.
									self.start_fn();
									continue 'main;
								}
							} else {
								println!("Expected function call arguments or `)`, found end of input instead!");
								return;
							}
						} else if *lookahead == Token::Comma {
							// We push the identifier to the stack.
							self.stack.push(match Ident::parse_name(s) {
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
							self.stack.push(match Ident::parse_name(s) {
								Ok(i) => Either::Left(Expr::Ident(i)),
								Err(_) => Either::Left(Expr::Invalid),
							});
						}
					} else {
						// There is no following dot, so this is just a simple identifier.
						self.stack.push(match Ident::parse_name(s) {
							Ok(i) => Either::Left(Expr::Ident(i)),
							Err(_) => Either::Left(Expr::Invalid),
						});
					}
					operand_state = false;
				}
				Token::Num { .. } | Token::Bool(_) | Token::Ident(_)
					if !operand_state =>
				{
					// We are expecting an operator, but we've found an operand. This is an error.
					// E.g. `..1 1` instead of `..1 + 1`
					println!("Expected an operator or the end of expression, found literal/identifier instead!");
					return;
				}
				Token::Op(op) if operand_state => match op {
					// We are expecting an operand, but if we find one of the allowed prefix operators, we can move
					// that to the operator stack since it's effectively part of the operand.
					OpType::Sub => self.push_operator(OpType::Neg),
					OpType::Not => self.push_operator(OpType::Not),
					OpType::Flip => self.push_operator(OpType::Flip),
					OpType::AddAdd => self.push_operator(OpType::AddAddPre),
					OpType::SubSub => self.push_operator(OpType::SubSubPre),
					_ => {
						// Any other operator that is not a valid prefix is an error.
						println!("Expected either a literal or a prefix operator, found a non-prefix operator instead!");
						return;
					}
				},
				Token::Op(op) if !operand_state => match op {
					// We are expecting an operator.
					OpType::Flip | OpType::Not => {
						// These operators cannot be part of a binary expression.
						println!("Expected a binary operator, found a prefix operator instead!");
						return;
					}
					// These operators are treated as postfix operators. Since postfix operators are effectively
					// part of the operand, we don't change state because we still want to find the binary
					// expression operator (if there is one).
					OpType::AddAdd => {
						self.push_operator(OpType::AddAddPost);
					}
					OpType::SubSub => {
						self.push_operator(OpType::SubSubPost);
					}
					// Any other operators can be part of a binary expression. We switch state because now we want
					// to look for the rhs operand.
					_ => {
						self.push_operator(*op);
						operand_state = true;
					}
				},
				Token::LParen if operand_state => {
					// We are expecting an operand, and we found a bracket group start. We move it to the operator
					// stack and continue looking for an operand, so we don't switch state.
					self.start_group();
				}
				Token::LParen if !operand_state => {
					// We are expecting an operator, but we've found an operand. This is an error.
					// E.g. `..1 (` instead of `..1 + (`
					println!("Expected an operator or the end of expression, found `(` instead!");
					return;
				}
				Token::RParen if !operand_state => {
					// We are expecting an operator, but we found a bracket group end. We move it to the operator
					// stack and continue looking for an operator, so we don't switch state.
					self.end_group();
				}
				Token::RParen if operand_state => {
					// We are expecting an operand, but we've found an bracket group end. This is an error.
					// E.g. `..+ )` instead of `..+ 1)`
					println!("Expected an operand or the end of expression, found `)` instead!");
					return;
				}
				_ => {
					// We have a token that's not allowed to be part of an expression.
					// TODO: Deal with this properly.
					println!("Unexpected token found: {token:?}");
					return;
				}
			}

			walker.advance();
		}

		// Move any remaining operators onto the stack.
		while let Some(op) = self.operators.pop_back() {
			self.stack.push(Either::Right(op))
		}
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
			Self::GroupStart | Self::FnStart | Self::FnCall(_) => {
				panic!("OpType::GroupStart | OpType::FnStart | OpType::FnCall do not have precedence values because they should never be passed into this function. Something has gone wrong!")
			},
			_ => 1,
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
			Self::GroupStart => write!(f, ""),
			Self::FnStart => write!(f, ""),
			Self::FnCall(count) => write!(f, "FN:{count}"),
		}
	}
}
