#![allow(unused)]
use crate::{
	ast::{Either, Expr, Ident, Lit},
	lexer::{OpType, Spanned, Token},
};
use std::{collections::VecDeque, iter::Peekable, slice::Iter};

/* enum SyntaxError {
	Invalid(Spanned<char>),
	UnclosedParen {
		/// The `Token::LParen` which is unclosed.
		opened: Spanned<Token>,
		/// The `Token` which is at the position that a `Token::RParen` should be.
		expected: Spanned<Token>,
	},
} */

pub fn expr_parser(cst: Vec<Spanned<Token>>) {
	let mut parser = ShuntingYard {
		stack: Vec::new(),
		operators: VecDeque::new(),
	};
	parser.parse(cst);

	println!("{parser}");
}

struct ShuntingYard {
	stack: Vec<Either<Expr, OpType>>,
	operators: VecDeque<OpType>,
}

impl ShuntingYard {
	fn push_operator(&mut self, op: OpType) {
		while if let Some(back) = self.operators.back() {
			op.precedence() < back.precedence()
		} else {
			false
		} {
			let moved_op = self.operators.pop_back().unwrap();
			self.stack.push(Either::Right(moved_op))
		}
		self.operators.push_back(op);
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
				// TODO: Implement this:
				Token::LParen if operand_state => {
					// We are expecting an operand, and we found a bracket group start. We move it to the operator
					// stack and continue looking for an operand, so we don't switch state.
					self.push_operator(OpType::GroupStart);
				}
				_ => {
					// We have a token that's not allowed to be part of an expression.
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

impl OpType {
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
			// TODO: Comma for functions/lists
			// These two should always be converted to the *Pre or *Post versions in the shunting yard.
			Self::AddAdd | Self::SubSub => panic!("OpType::AddAdd | OpType::SubSub do not have a precedence value because they should never be passed into this function. Something has gone wrong!"),
			_ => 1,
		}
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
