use crate::{
	ast::{Either, Expr, Stmt},
	expression::expr_parser,
	lexer::{lexer, Spanned, Token},
};

pub struct Walker {
	pub cst: Vec<Spanned<Token>>,
	pub cursor: usize,
}

impl Walker {
	/// Returns the current token under the cursor, without advancing the cursor.
	pub fn peek(&self) -> Option<&Token> {
		self.cst.get(self.cursor).map(|(t, _)| t)
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	pub fn lookahead_1(&self) -> Option<&Token> {
		self.cst.get(self.cursor + 1).map(|(t, _)| t)
	}

	/// Advances the cursor by one.
	pub fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	pub fn next(&mut self) -> Option<&Token> {
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
	pub fn is_done(&self) -> bool {
		// We check that the cursor is equal to the length, because that means we have gone past the last token
		// of the string, and hence, we are done.
		self.cursor == self.cst.len()
	}
}

pub fn parse(source: &str) {
	let cst = lexer(source);
	println!("{cst:?}");

	parser(cst);
}

fn print_stmt(stmt: &Stmt, indent: usize) {
	match stmt {
		Stmt::Empty => print!(
			"\r\n{:indent$}\x1b[9m(Empty)\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::VarDecl {
			type_,
			ident,
			value,
			is_const,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(type: {type_}, ident: {ident}",
				"",
				indent = indent * 4
			);
			if *is_const {
				print!(", \x1b[4mconst\x1b[0m");
			}
			print!(")");
			if let Some(value) = value {
				print!(" = {value}");
			}
		}
		Stmt::FnDecl {
			type_,
			ident,
			params,
			body,
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return: {type_} ident: {ident}, params: [",
				"",
				indent = indent * 4
			);
			for (type_, ident) in params {
				print!("{type_}: {ident}, ");
			}
			print!("]) {{");
			for inner in body {
				print_stmt(inner, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::StructDecl { ident, members } => {
			print!(
				"\r\n{:indent$}\x1b[32mStruct\x1b[0m(ident: {ident}, members: [",
				"",
				indent = indent * 4
			);
			for (t, i) in members {
				print!("{i}: {t}, ");
			}
			print!("])");
		}
		Stmt::FnCall { ident, args } => {
			print!(
				"\r\n{:indent$}\x1b[34mCall\x1b[0m(ident: {ident}, args: [",
				"",
				indent = indent * 4
			);
			for arg in args {
				print!("{arg}, ");
			}
			print!("])");
		}
		Stmt::VarAssign { ident, value } => {
			print!(
				"\r\n{:indent$}\x1b[32mAssign\x1b[0m(ident: {ident}) = {value}",
				"",
				indent = indent * 4
			);
		}
		Stmt::VarEq { ident, value, op } => {
			print!(
				"\r\n{:indent$}\x1b[32mAssign\x1b[0m(ident: {ident}, op: \x1b[36m{op:?}\x1b[0m) = {value}",
				"",
				indent = indent * 4
			);
		}
		Stmt::Preproc(p) => print!(
			"\r\n{:indent$}\x1b[4mPreproc({p})\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::If {
			cond,
			body,
			else_ifs,
			else_,
		} => {
			print!("\r\n{:indent$}If({cond}) {{", "", indent = indent * 4);
			for stmt in body {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);

			for (cond, body) in else_ifs {
				print!("\r\n{:indent$}ElseIf({cond})", "", indent = indent * 4);
				for stmt in body {
					print_stmt(stmt, indent + 1);
				}
				print!("\r\n{:indent$}}}", "", indent = indent * 4);
			}

			if let Some(body) = else_ {
				print!("\r\n{:indent$}Else {{", "", indent = indent * 4);
				for stmt in body {
					print_stmt(stmt, indent + 1);
				}
				print!("\r\n{:indent$}}}", "", indent = indent * 4);
			}
		}
		Stmt::Switch { expr, cases } => {
			print!("\r\n{:indent$}Switch({expr}) {{", "", indent = indent * 4);
			for (expr, stmts) in cases {
				if let Some(expr) = expr {
					print!(
						"\r\n{:indent$}Case({expr}) {{",
						"",
						indent = (indent + 1) * 4
					);
				} else {
					print!(
						"\r\n{:indent$}Default {{",
						"",
						indent = (indent + 1) * 4
					);
				}
				for stmt in stmts {
					print_stmt(stmt, indent + 2);
				}
				print!("\r\n{:indent$}}}", "", indent = (indent + 1) * 4);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::For {
			var,
			cond,
			inc,
			body,
		} => {
			print!("\r\n{:indent$}For(", "", indent = indent * 4);
			if let Some(var) = var {
				print!("var:");
				print_stmt(var, indent + 2);
				print!(", ");
			}
			if let Some(cond) = cond {
				print!(
					"\r\n{:indent$}cond:\r\n{:indent_2$}{cond}, ",
					"",
					"",
					indent = (indent + 1) * 4,
					indent_2 = (indent + 2) * 4
				);
			}
			if let Some(inc) = inc {
				print!(
					"\r\n{:indent$}inc:\r\n{:indent_2$}{inc}, ",
					"",
					"",
					indent = (indent + 1) * 4,
					indent_2 = (indent + 2) * 4
				);
			}
			print!(") {{");
			for stmt in body {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::Return(expr) => {
			print!("\r\n{:indent$}RETURN", "", indent = indent * 4);
			if let Some(expr) = expr {
				print!("(value: {expr})");
			}
		}
		Stmt::Break => {
			print!("\r\n{:indent$}BREAK", "", indent = indent * 4)
		}
		Stmt::Discard => {
			print!("\r\n{:indent$}DISCARD", "", indent = indent * 4)
		}
	}
}
/* 
/// Filters only the specified operands.
///
/// # Example
/// ```rust
/// match_op!(OpType::Mul, OpType::Div).then(/*...*/)
/// ```
macro_rules! match_op {
	($($op:pat),*) => {
		filter(|t: &Token| match t {
			Token::Op(op) => match op {
				$(
					$op => true,
				)*
				_ => false,
			},
			_ => false,
		})
	};
}

/// Creates a pattern for a binary expression with the specified operands.
///
/// # Example
/// ```rust
/// let product = {/*...*/};
/// let sum = binary_expr!(product, OpType::Add, OpType::Sub);
/// ```
macro_rules! binary_expr {
	($prev:expr, $($op:pat),*) => {
		$prev
			.clone()
			.then(
				filter(|t: &Token| match t {
					Token::Op(op) => match op {
						$(
							$op => true,
						)*
						_ => false,
					},
					_ => false,
				})
				.map(|t| match t {
					Token::Op(op) => op,
					_ => unreachable!(),
				})
				.then($prev)
				.repeated(),
			)
			.foldl(|lhs, (op, rhs)| Expr::Binary {
				left: Box::from(lhs),
				op,
				right: Box::from(rhs),
			})
	};
}

fn old_parser() -> impl Parser<Token, Vec<Stmt>, Error = Simple<Token>> {
	// Identifier for a name.
	let ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		match Ident::parse_name(&str) {
			Ok(i) => Ok(i),
			Err(_) => Err(Simple::custom(
				span,
				"Identifier cannot be the same as a type",
			)),
		}
	});

	// Type identifiers of any type, (incl. void).
	let type_ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		// Deconstruct the string.
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		// First, try to parse a primitive type identifier. If not, try to parse a valid custom type identifier.
		match Primitive::parse(&str) {
			Ok(p) => Ok(Either::Left(p)),
			Err(_) => match Ident::parse_struct(&str) {
				Ok(i) => Ok(Either::Right(i)),
				Err(_) => Err(Simple::custom(span, "Invalid type")),
			},
		}
	});

	// Type identifiers that are allowed in variable declarations.
	let var_type_ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		// Deconstruct the string.
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		// First, try to parse a primitive type identifier. If not, try to parse a valid custom type identifier.
		match Primitive::parse_var(&str) {
			Ok(p) => Ok(Either::Left(p)),
			Err(_) => match Ident::parse_struct(&str) {
				Ok(i) => Ok(Either::Right(i)),
				Err(_) => Err(Simple::custom(span, "Invalid type")),
			},
		}
	});

	// Array size, i.e. `[...]`.
	let arr = {
		let size = filter(|t: &Token| match t {
			Token::Num { .. } => true,
			Token::Ident(_) => true,
			_ => false,
		})
		.try_map(|t, span| match t {
			Token::Num {
				num: s,
				suffix,
				type_,
			} => match type_ {
				NumType::Dec | NumType::Oct | NumType::Hex => {
					match Lit::parse_num(&s, suffix.as_deref(), type_) {
						Ok(l) => match l {
							Lit::UInt(u) => Ok(Either::Left(u as usize)),
							Lit::Int(i) => Ok(Either::Left(i as usize)),
							_ => unimplemented!(),
						},
						Err(_) => {
							Err(Simple::custom(span, "Could not parse number!"))
						}
					}
				}
				_ => Err(Simple::custom(span, "Float values are not allowed")),
			},
			Token::Ident(s) => Ok(Either::Right(Ident(s))),
			_ => unreachable!(),
		});

		just(Token::LBracket)
			.then(size.or_not())
			.then(just(Token::RBracket))
			.map(|((_, s), _)| s)
	};

	// Expressions of all kinds.
	let expr = recursive(|expr| {
		let arr_init = type_ident
			.clone()
			.then(arr.clone())
			.then(
				expr.clone()
					.separated_by(just(Token::Comma))
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.map(|((type_, size), args)| Expr::Array {
				type_: Type::Array(type_, size),
				args,
			});

		let init_list = arr_init.or(expr
			.clone()
			.separated_by(just(Token::Comma))
			.delimited_by(just(Token::LBrace), just(Token::RBrace))
			.map(|v| Expr::InitList(v)));

		let fn_call = init_list.or(filter(|t: &Token| match t {
			Token::Ident(_) => true,
			_ => false,
		})
		.then(
			expr.clone()
				.separated_by(just(Token::Comma))
				.delimited_by(just(Token::LParen), just(Token::RParen)),
		)
		.try_map(|(t, args), span| {
			let str = if let Token::Ident(s) = t {
				s
			} else {
				unreachable!()
			};

			match Ident::parse_name(&str) {
				Ok(i) => Ok(Expr::Fn { ident: i, args }),
				Err(_) => Err(Simple::custom(span, "Invalid identifier")),
			}
		}));

		let member = fn_call.or(filter(|t: &Token| match t {
			Token::Ident(_) => true,
			_ => false,
		})
		.then(
			just(Token::Dot)
				.ignored()
				.then(filter(|t: &Token| match t {
					Token::Ident(_) => true,
					_ => false,
				}))
				.repeated()
				.at_least(1),
		)
		.try_map(|(first, v), span| {
			let mut vec = Vec::with_capacity(v.len() + 1);

			match first {
				Token::Ident(s) => match Ident::parse_name(&s) {
					Ok(i) => vec.push(i),
					Err(_) => {
						return Err(Simple::custom(span, "Invalid identifier"));
					}
				},
				_ => unreachable!(),
			}
			for (_, t) in v.into_iter() {
				match t {
					Token::Ident(s) => match Ident::parse_name(&s) {
						Ok(i) => vec.push(i),
						Err(_) => {
							return Err(Simple::custom(
								span,
								"Invalid identifier",
							));
						}
					},
					_ => unreachable!(),
				}
			}

			Ok(Expr::Member(vec))
		}));

		let val = member.or(filter(|t: &Token| match t {
			Token::Bool(_) => true,
			Token::Num { .. } => true,
			Token::Ident(_) => true,
			_ => false,
		})
		.try_map(|t, span| match t {
			Token::Bool(b) => Ok(Expr::Lit(Lit::Bool(b))),
			Token::Num {
				num: s,
				suffix,
				type_,
			} => match Lit::parse_num(&s, suffix.as_deref(), type_) {
				Ok(l) => Ok(Expr::Lit(l)),
				Err(_) => Err(Simple::custom(span, "Could not parse number")),
			},
			Token::Ident(s) => match Ident::parse_name(&s) {
				Ok(i) => Ok(Expr::Ident(i)),
				Err(_) => Err(Simple::custom(span, "Invalid identifier")),
			},
			_ => unreachable!(),
		}));

		let atom = val
			.or(expr
				.clone()
				.delimited_by(just(Token::LParen), just(Token::RParen)))
			.boxed();

		// Operators in order of precedence.
		// Note: The reason for the sprinkling of '.boxed()' everywhere is because otherwise there would be so much
		// nesting of generic types that rustc will have a breakdown.
		let postfix = atom
			.then(match_op!(OpType::AddAdd, OpType::SubSub).or_not())
			.map(|(expr, op)| {
				if let Some(op) = op {
					let op = match op {
						Token::Op(o) => o,
						_ => unreachable!(),
					};
					Expr::Postfix(Box::from(expr), op)
				} else {
					expr
				}
			});
		let prefix = match_op!(OpType::AddAdd, OpType::SubSub)
			.or_not()
			.then(postfix)
			.map(|(op, expr)| {
				if let Some(op) = op {
					let op = match op {
						Token::Op(o) => o,
						_ => unreachable!(),
					};
					Expr::Prefix(Box::from(expr), op)
				} else {
					expr
				}
			});
		let flip =
			match_op!(OpType::Flip)
				.or_not()
				.then(prefix)
				.map(|(op, expr)| {
					if let Some(_) = op {
						Expr::Flip(Box::from(expr))
					} else {
						expr
					}
				});
		let not = match_op!(OpType::Not)
			.repeated()
			.then(flip)
			.foldr(|_op, rhs| Expr::Not(Box::new(rhs)));
		let neg = match_op!(OpType::Sub)
			.repeated()
			.then(not)
			.foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));
		let product = binary_expr!(neg, OpType::Mul, OpType::Div, OpType::Rem);
		let sum = binary_expr!(product, OpType::Add, OpType::Sub);
		let shift = binary_expr!(sum, OpType::LShift, OpType::RShift);
		let cpm =
			binary_expr!(shift, OpType::Lt, OpType::Gt, OpType::Le, OpType::Ge);
		let eq = binary_expr!(cpm, OpType::EqEq, OpType::NotEq).boxed();
		let b_and = binary_expr!(eq, OpType::And);
		let b_xor = binary_expr!(b_and, OpType::Xor);
		let b_or = binary_expr!(b_xor, OpType::Or);
		let b_and_and = binary_expr!(b_or, OpType::AndAnd);
		let b_xor_xor = binary_expr!(b_and_and, OpType::XorXor);
		let b_or_or = binary_expr!(b_xor_xor, OpType::OrOr);
		let ternary = b_or_or
			.then(
				just(Token::Question)
					.ignored()
					.then(expr.clone())
					.then_ignore(just(Token::Colon))
					.then(expr)
					.or_not(),
			)
			.map(|(expr, if_else)| {
				if let Some(((_, true_), false_)) = if_else {
					Expr::Ternary {
						cond: Box::from(expr),
						true_: Box::from(true_),
						false_: Box::from(false_),
					}
				} else {
					expr
				}
			});
		let assign = binary_expr!(
			ternary,
			OpType::AddEq,
			OpType::SubEq,
			OpType::MulEq,
			OpType::DivEq,
			OpType::RemEq,
			OpType::AndEq,
			OpType::XorEq,
			OpType::OrEq,
			OpType::LShiftEq,
			OpType::RShiftEq
		);
		assign
	})
	.boxed();

	// Preprocessor directives.
	let preproc = filter(|t: &Token| match t {
		Token::Directive(_) => true,
		_ => false,
	})
	.try_map(|t, span: std::ops::Range<usize>| match t {
		Token::Directive(s) => {
			let (stmt, errors) = preproc_parser().parse_recovery(s);

			if let Some(_) = errors.first() {
				return Err(Simple::custom(
					span,
					"Error parsing preproc directive",
				));
			}

			if let Some(stmt) = stmt {
				Ok(stmt)
			} else {
				Ok(Stmt::Preproc(Preproc::Unsupported))
			}
		}
		_ => unreachable!(),
	});

	// Const qualifier.
	let const_ = just(Token::Const).or_not().map(|t| t.is_some());

	// Variable declaration.
	let var = const_
		.clone()
		.then(var_type_ident)
		.then(ident)
		.then(arr.clone().repeated())
		.then_ignore(just(Token::Eq))
		.then(expr.clone())
		.then_ignore(just(Token::Semi))
		.map(
			|((((is_const, type_ident), ident), size), rhs)| Stmt::VarDecl {
				type_: Type::new(type_ident, size),
				ident,
				value: Some(rhs),
				is_const,
			},
		);
	let var_uninit = const_
		.then(var_type_ident)
		.then(ident)
		.then(arr.clone().repeated())
		.then_ignore(just(Token::Semi))
		.map(|(((is_const, type_ident), ident), size)| Stmt::VarDecl {
			type_: Type::new(type_ident, size),
			ident,
			value: None,
			is_const,
		});

	// Empty statement.
	let empty = just(Token::Semi).map(|_| Stmt::Empty);

	// All statements within a function body.
	let stmt = recursive(|stmt| {
		let break_ = preproc.or(just(Token::Break)
			.then_ignore(just(Token::Semi))
			.to(Stmt::Break));
		let return_ = break_.or(just(Token::Return)
			.ignored()
			.then(expr.clone().or_not())
			.then_ignore(just(Token::Semi))
			.map(|(_, expr)| Stmt::Return(expr)));
		let discard = return_.or(just(Token::Discard)
			.then_ignore(just(Token::Semi))
			.to(Stmt::Discard));

		let var_eq = discard.or(expr
			.clone()
			.then_ignore(just(Token::Semi))
			.try_map(|expr, span| match expr {
				Expr::Binary { left, op, right } => {
					let ident = match *left {
						Expr::Ident(i) => i,
						_ => {
							return Err(Simple::custom(
								span,
								"Expected an identifier",
							))
						}
					};
					match op {
						OpType::AddEq
						| OpType::SubEq
						| OpType::MulEq
						| OpType::DivEq
						| OpType::RemEq
						| OpType::AndEq
						| OpType::XorEq
						| OpType::OrEq
						| OpType::LShiftEq
						| OpType::RShiftEq => {}
						_ => {
							return Err(Simple::custom(
								span,
								"Invalid operator",
							))
						}
					}

					Ok(Stmt::VarEq {
						ident,
						value: right,
						op,
					})
				}
				_ => return Err(Simple::custom(span, "invalid expression")),
			}));

		let var_assign =
			var_eq.or(var.clone()).or(var_uninit.clone()).or(ident
				.then_ignore(just(Token::Eq))
				.then(expr.clone())
				.then_ignore(just(Token::Semi))
				.map(|(ident, rhs)| Stmt::VarAssign { ident, value: rhs }));

		// Function call on its own.
		let fn_call = var_assign.or(ident
			.then(
				expr.clone()
					.separated_by(just(Token::Comma))
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then_ignore(just(Token::Semi))
			.map(|(ident, args)| Stmt::FnCall { ident, args }));

		// For statement.
		let for_ = just(Token::For)
			.ignored()
			.then(
				var.clone()
					.or(var_uninit.clone())
					.or(empty.clone())
					.or_not()
					.then(expr.clone().or_not().then_ignore(just(Token::Semi)))
					.then(expr.clone().or_not())
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then(
				stmt.clone()
					.repeated()
					.delimited_by(just(Token::LBrace), just(Token::RBrace)),
			)
			.map(|((_, ((var, cond), inc)), stmts)| Stmt::For {
				var: var.map(|s| Box::from(s)),
				cond,
				inc,
				body: stmts,
			});

		// If statement.
		let if_ =
			just(Token::If)
				.ignored()
				.then(
					expr.clone()
						.delimited_by(just(Token::LParen), just(Token::RParen)),
				)
				.then(
					stmt.clone()
						.repeated()
						.delimited_by(just(Token::LBrace), just(Token::RBrace)),
				)
				.then(
					// else ifs
					just(Token::Else)
						.ignored()
						.then_ignore(just(Token::If))
						.then(expr.clone().delimited_by(
							just(Token::LParen),
							just(Token::RParen),
						))
						.then(stmt.clone().repeated().delimited_by(
							just(Token::LBrace),
							just(Token::RBrace),
						))
						.repeated(),
				)
				.then(
					just(Token::Else)
						.ignored()
						.then(stmt.clone().repeated().delimited_by(
							just(Token::LBrace),
							just(Token::RBrace),
						))
						.or_not(),
				)
				.map(|((((_, cond), body), nth), opt): ((_, Vec<_>), _)| {
					Stmt::If {
						cond,
						body,
						else_ifs: nth
							.into_iter()
							.map(|((_, cond), stmts)| (cond, stmts))
							.collect(),
						else_: if let Some(opt) = opt {
							Some(opt.1)
						} else {
							None
						},
					}
				})
				.boxed();

		// Switch statement.
		let switch = just(Token::Switch)
			.ignored()
			.then(
				expr.clone()
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then(
				just(Token::Case)
					.ignored()
					.then(expr.clone())
					.then_ignore(just(Token::Colon))
					.then(stmt.clone().repeated())
					.map(|((_, expr), stmt)| (Some(expr), stmt))
					.or(just(Token::Default)
						.ignored()
						.then_ignore(just(Token::Colon))
						.then(stmt.clone().repeated())
						.map(|(_, stmt)| (None, stmt)))
					.repeated()
					.delimited_by(just(Token::LBrace), just(Token::RBrace)),
			)
			.map(|((_, expr), cases)| Stmt::Switch { expr, cases })
			.boxed();

		fn_call.or(if_).or(switch).or(for_).or(empty.clone())
	})
	.boxed();

	// Function parameter.
	let param = type_ident
		.clone()
		.then(ident.clone())
		.map(|(type_, ident)| (Type::Basic(type_), ident));

	// Function declaration.
	let func = type_ident
		.then(ident)
		.then(
			param
				.separated_by(just(Token::Comma))
				.delimited_by(just(Token::LParen), just(Token::RParen)),
		)
		.then(
			stmt.repeated()
				.delimited_by(just(Token::LBrace), just(Token::RBrace)),
		)
		.map(|(((type_ident, ident), params), body)| Stmt::FnDecl {
			type_: Type::Basic(type_ident),
			ident,
			params,
			body,
		});

	// Struct member.
	let member = var_type_ident
		.then(ident)
		.then(arr.repeated())
		.then_ignore(just(Token::Semi))
		.map(|((type_ident, ident), size)| {
			(Type::new(type_ident, size), ident)
		});

	// Struct declaration.
	let struct_ = just(Token::Struct)
		.ignored()
		.then(ident)
		.then(
			member
				.repeated()
				.delimited_by(just(Token::LBrace), just(Token::RBrace)),
		)
		.then_ignore(just(Token::Semi))
		.map(|((_, ident), members)| Stmt::StructDecl { ident, members });

	func.or(var)
		.or(var_uninit)
		.or(struct_)
		.or(empty)
		.or(preproc)
		.repeated()
}

fn preproc_parser() -> impl Parser<char, Stmt, Error = Simple<char>> {
	let version = text::keyword("version")
		.ignored()
		.padded()
		.then(text::digits(10).padded())
		.then(text::ident().padded().or_not())
		.try_map(|((_, v), p), span| {
			let is_core = if let Some(p) = p {
				if p == "core" {
					true
				} else if p == "compatibility" {
					false
				} else {
					return Err(Simple::custom(span, "invalid profile"));
				}
			} else {
				true
			};

			if v != "450" {
				return Err(Simple::custom(span, "invalid version"));
			}

			Ok(Stmt::Preproc(Preproc::Version {
				version: 450,
				is_core,
			}))
		});

	let extension = text::keyword("extension")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(just(':').padded())
		.then(text::ident().padded())
		.try_map(|((_, name), ext), span| {
			let ext = match ext.as_str() {
				"enable" => ExtBehaviour::Enable,
				"disable" => ExtBehaviour::Disable,
				"warn" => ExtBehaviour::Warn,
				"require" => ExtBehaviour::Require,
				_ => return Err(Simple::custom(span, "Invalid behaviour")),
			};

			Ok(Stmt::Preproc(Preproc::Extension {
				name,
				behaviour: ext,
			}))
		});

	let line = text::keyword("line")
		.ignored()
		.padded()
		.then(text::digits(10).padded())
		.then(text::digits(10).padded().or_not())
		.try_map(
			|((_, line), src_str): (((), String), Option<String>), span| {
				let line = match usize::from_str_radix(line.as_str(), 10) {
					Ok(i) => i,
					Err(_) => {
						return Err(Simple::custom(span, "Invalid line number"))
					}
				};

				let src_str = if let Some(src_str) = src_str {
					match usize::from_str_radix(src_str.as_str(), 10) {
						Ok(i) => Some(i),
						Err(_) => {
							return Err(Simple::custom(
								span,
								"Invalid line number",
							))
						}
					}
				} else {
					None
				};

				Ok(Stmt::Preproc(Preproc::Line { line, src_str }))
			},
		);

	let include = text::keyword("include")
		.ignored()
		.padded()
		.then(
			filter(|c: &char| {
				// TODO: Check which characters are actually valid within an include path.
				c.is_ascii_alphanumeric()
					|| c.is_ascii_whitespace()
					|| *c == '.' || *c == '/'
					|| *c == '\\'
			})
			.repeated()
			.delimited_by(just('"'), just('"')),
		)
		.then_ignore(end())
		.map(|(_, v)| Stmt::Preproc(Preproc::Include(v.iter().collect())));

	let error = text::keyword("error")
		.ignored()
		.padded()
		.then(
			filter(|c: &char| {
				// TODO: Check which characters are actually valid within a message.
				c.is_ascii_alphanumeric()
					|| c.is_ascii_punctuation()
					|| c.is_ascii_whitespace()
			})
			.repeated(),
		)
		.map(|(_, v)| Stmt::Preproc(Preproc::Error(v.iter().collect())));

	let pragma = text::keyword("pragma")
		.ignored()
		.padded()
		.then(
			// TODO: Check which characters are actually valid within pragma options.
			filter(|c: &char| {
				c.is_ascii_alphanumeric()
					|| c.is_ascii_punctuation()
					|| c.is_ascii_whitespace()
			})
			.repeated(),
		)
		.map(|(_, v)| Stmt::Preproc(Preproc::Pragma(v.iter().collect())));

	let undef = text::keyword("undef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::UnDef(symbol)));

	let ifdef = text::keyword("ifdef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::IfDef(symbol)));

	let ifndef = text::keyword("ifdef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::IfnDef(symbol)));

	let else_ = text::keyword("else")
		.ignored()
		.padded()
		.then_ignore(end())
		.to(Stmt::Preproc(Preproc::Else));

	let endif = text::keyword("endif")
		.ignored()
		.padded()
		.then_ignore(end())
		.to(Stmt::Preproc(Preproc::EndIf));

	version
		.or(include)
		.or(ifdef)
		.or(ifndef)
		.or(undef)
		.or(else_)
		.or(endif)
		.or(extension)
		.or(line)
		.or(error)
		.or(pragma)
		.or(any()
			.repeated()
			.then_ignore(end())
			.to(Stmt::Preproc(Preproc::Unsupported)))
}
 */