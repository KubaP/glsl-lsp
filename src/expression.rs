#![allow(unused)]
use crate::{
	ast::{Expr, Ident, Lit},
	lexer::{OpType, Spanned, Token},
};
use std::{iter::Peekable, slice::Iter};

struct Parser<'a> {
	iter: Peekable<Iter<'a, Spanned<Token>>>,
}

impl<'a> Parser<'a> {
	fn new(iter: Peekable<Iter<'a, Spanned<Token>>>) -> Self {
		Self { iter }
	}

	fn peek(&mut self) -> Option<&Token> {
		self.iter.peek().map(|t| &t.0)
	}

	fn advance(&mut self) {
		self.iter.next();
	}

	fn current(&mut self) -> Option<&Token> {
		self.iter.next().map(|t| &t.0)
	}

	fn parse(&mut self) -> Result<Expr, ()> {
		let expr = self.sum()?;
		Ok(expr)
	}

	// region: PRECEDENCE
	fn atom(&mut self) -> Result<Expr, ()> {
		if let Some(current) = self.current() {
			return match current {
				Token::Num { .. } | Token::Bool(_) => Lit::parse(current).map(|l| Expr::Lit(l)),
				Token::Ident(s) => Ident::parse_name(s).map(|i| Expr::Ident(i)),
				Token::LParen => {
					let expr = self.sum()?;

					if let Some(paren) = self.current() {
						if *paren == Token::RParen {
							Ok(expr)
						} else {
							println!("UNCLOSED parens");
							Err(())
						}
					} else {
						println!("UNCLOSED parens");
						Err(())
					}
				}
				_ => Err(()),
			};
		}

		Err(())
	}

	fn prefix(&mut self) -> Result<Expr, ()> {
		let current = match self.peek() {
			Some(t) => t.clone(),
			None => return Err(()),
		};

		if let Token::Op(op) = current {
			if op == OpType::Sub {
				self.iter.next();
				let expr = self.atom()?;
				Ok(Expr::Neg(Box::from(expr)))
			} else {
				Err(())
			}
		// TODO: other operators
		} else {
			self.atom()
		}
	}

	fn product(&mut self) -> Result<Expr, ()> {
		let mut expr = self.prefix()?;

		loop {
			let next = match self.peek() {
				Some(t) => t.clone(),
				None => return Ok(expr),
			};

			if let Token::Op(ref op) = next {
				if *op == OpType::Mul || *op == OpType::Div {
					self.iter.next();
					let rhs = self.prefix()?;
					expr = Expr::Binary {
						left: Box::from(expr),
						op: *op,
						right: Box::from(rhs),
					};
				} else {
					break;
				}
			} else {
				break;
			}
		}

		Ok(expr)
	}

	fn sum(&mut self) -> Result<Expr, ()> {
		let mut expr = self.product()?;

		loop {
			let next = match self.peek() {
				Some(t) => t.clone(),
				None => return Ok(expr),
			};

			if let Token::Op(ref op) = next {
				if *op == OpType::Add || *op == OpType::Sub {
					self.iter.next();
					let rhs = self.product()?;
					expr = Expr::Binary {
						left: Box::from(expr),
						op: *op,
						right: Box::from(rhs),
					};
				} else {
					break;
				}
			} else {
				break;
			}
		}

		Ok(expr)
	}
	// endregion: PRECEDENCE
}

pub fn expr_parser(cst: &Vec<Spanned<Token>>) {
	let mut parser = Parser::new(cst.iter().peekable());
	let result = parser.parse();
	println!("{result:#?}");
}
