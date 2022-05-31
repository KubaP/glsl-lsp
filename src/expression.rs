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

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: Vec<Either<Expr, OpType>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<OpType>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: OpType) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if *back == OpType::GroupStart {
				// Group start operators always have the highest precedence, so we don't need to check further.
				break;
			}

			if op.precedence() < back.precedence() {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push(Either::Right(moved_op));
			}
		}
		self.operators.push_back(op);
	}

	/// Registers the start of a bracket group.
	fn start_group(&mut self) {
		self.operators.push_back(OpType::GroupStart);
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
			} else {
				// Any other operators get
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push(Either::Right(moved_op));
			}
		}
	}

	fn parse(&mut self, cst: Vec<Spanned<Token>>) {
		// `true` if we are looking for an operand (which includes parsing prefix operators). `false` if we are
		// looking for an operator for a binary expression (or alternatively the end of the expression).
		let mut operand_state = true;

		for (token, _range) in cst.iter() {
			match token {
				Token::Num { .. } | Token::Bool(_) if operand_state => {
					// We are expecting an operand, so we can move the literal to the stack immediately.
					// We toggle the state so that we're now looking for an operator.
					self.stack.push(match Lit::parse(token) {
						Ok(l) => Either::Left(Expr::Lit(l)),
						Err(_) => Either::Left(Expr::Invalid),
					});
					operand_state = false;
				}
				Token::Ident(s) if operand_state => {
					// TODO: Member access
					self.stack.push(match Ident::parse_name(s) {
						Ok(i) => Either::Left(Expr::Ident(i)),
						Err(_) => Either::Left(Expr::Invalid),
					});
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
			Self::AddAdd | Self::SubSub => panic!("OpType::AddAdd | OpType::SubSub do not have a precedence value because they should never be passed into this function. Something has gone wrong!"),
			// This is never directly checked for precedence, but rather has a special branch.
			Self::GroupStart => panic!("OpType::GroupStart does not have a precedence value because they should never be passed into this function. Something has gone wrong!"),
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
		}
	}
}
