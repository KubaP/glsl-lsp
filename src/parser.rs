use crate::{
	ast::{Expr, Stmt, Type},
	expression::expr_parser,
	lexer::{lexer, Token},
	span::Spanned,
	Either,
};

pub struct Walker {
	pub cst: Vec<Spanned<Token>>,
	pub cursor: usize,
}

impl Walker {
	/// Returns the current token under the cursor, without advancing the cursor.
	pub fn peek(&self) -> Option<&Spanned<Token>> {
		self.cst.get(self.cursor)
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	pub fn lookahead_1(&self) -> Option<&Spanned<Token>> {
		self.cst.get(self.cursor + 1)
	}

	/// Advances the cursor by one.
	pub fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	pub fn next(&mut self) -> Option<&Spanned<Token>> {
		// If we are successful in getting the token, advance the cursor.
		match self.cst.get(self.cursor) {
			Some(i) => {
				self.cursor += 1;
				Some(i)
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

pub fn parse_file(source: &str) {
	let stmts = parse(source);
	for stmt in stmts {
		print_stmt(&stmt, 0);
	}
	print!("\r\n");
}

pub fn parse(source: &str) -> Vec<Stmt> {
	let cst = lexer(source);
	println!("{cst:?}");

	let mut walker = Walker { cst, cursor: 0 };
	let mut stmts = Vec::new();

	'parser: while !walker.is_done() {
		match expr_parser(&mut walker) {
			// We tried to parse an expression and succeeded. We have an expression consisting of at least one
			// token.
			Some(expr) => {
				if let Some(type_) = expr.to_type() {
					match parse_type_start(&mut walker, type_) {
						Some(s) => stmts.push(s),
						None => 'till_next: loop {
							// We did not successfully parse a statement.
							let (next, _) = match walker.peek() {
								Some(t) => t,
								None => break 'parser,
							};

							if *next == Token::Semi {
								walker.advance();
								break 'till_next;
							} else if next.starts_statement() {
								// We don't advance because we are currently at a token which begins a new statement, so we
								// don't want to consume it before we rerun the main loop.
								break 'till_next;
							} else {
								walker.advance();
								continue 'till_next;
							}
						},
					};
				}
			}
			// We tried to parse an expression but that immediately failed. This means the current token is one
			// which cannot start an expression.
			None => {
				let (token, _) = walker.peek().unwrap();

				match token {
					Token::Struct => {
						walker.advance();
						match parse_struct(&mut walker) {
							Some(s) => stmts.push(s),
							None => break 'parser,
						}
					}
					_ => break 'parser,
				}
			}
		}
	}

	stmts
}

/// Parse statements which begin with a type.
fn parse_type_start(walker: &mut Walker, type_: Type) -> Option<Stmt> {
	let next = match expr_parser(walker) {
		Some(e) => e,
		None => return None,
	};

	let idents = next.to_var_decl();
	if idents.len() == 0 {
		return None;
	}
	let mut typenames = idents
		.into_iter()
		.map(|i| match i {
			Either::Left(ident) => (type_.clone(), ident),
			Either::Right((ident, v)) => {
				(type_.clone().add_var_decl_arr_size(v), ident)
			}
		})
		.collect::<Vec<_>>();

	let (next, _) = match walker.peek() {
		Some(t) => t,
		None => return None,
	};

	if *next == Token::Semi {
		// We have a variable definition.
		walker.advance();
		return match typenames.len() {
			1 => {
				let (type_, ident) = typenames.remove(0);
				Some(Stmt::VarDef { type_, ident })
			}
			_ => Some(Stmt::VarDefs(typenames)),
		};
	} else if *next == Token::Eq {
		walker.advance();
		// We have a variable declaration.
		let value = match expr_parser(walker) {
			Some(e) => e,
			None => return None,
		};

		let (next, _) = match walker.peek() {
			Some(t) => t,
			None => return None,
		};
		if *next == Token::Semi {
			walker.advance();
		} else {
			return None;
		}

		return match typenames.len() {
			1 => {
				let (type_, ident) = typenames.remove(0);
				Some(Stmt::VarDecl {
					type_,
					ident,
					value,
					is_const: false,
				})
			}
			_ => Some(Stmt::VarDecls {
				vars: typenames,
				value,
				is_const: false,
			}),
		};
	} else {
		None
	}
}

/// Parse a struct declaration.
fn parse_struct(walker: &mut Walker) -> Option<Stmt> {
	let ident = match expr_parser(walker) {
		Some(e) => match e {
			Expr::Ident(i) => i,
			_ => return None,
		},
		None => return None,
	};

	let (next, _) = match walker.peek() {
		Some(t) => t,
		None => return None,
	};
	if *next == Token::LBrace {
		walker.advance();
	} else {
		return None;
	}

	let mut members = Vec::new();
	'members: loop {
		match expr_parser(walker) {
			Some(expr) => {
				if let Some(type_) = expr.to_type() {
					let next = match expr_parser(walker) {
						Some(e) => e,
						None => return None,
					};

					let idents = next.to_var_decl();
					if idents.len() == 0 {
						return None;
					}
					let mut typenames = idents
						.into_iter()
						.map(|i| match i {
							Either::Left(ident) => (type_.clone(), ident),
							Either::Right((ident, v)) => {
								(type_.clone().add_var_decl_arr_size(v), ident)
							}
						})
						.collect::<Vec<_>>();

					let (next, _) = match walker.peek() {
						Some(t) => t,
						None => return None,
					};

					if *next == Token::Semi {
						// We have a variable definition.
						walker.advance();
						members.push(match typenames.len() {
							1 => {
								let (type_, ident) = typenames.remove(0);
								Stmt::VarDef { type_, ident }
							}
							_ => Stmt::VarDefs(typenames),
						});
					} else {
						return None;
					}
				} else {
					return None;
				}
			}
			None => break 'members,
		}
	}

	let (next, _) = match walker.peek() {
		Some(t) => t,
		None => return None,
	};
	if *next == Token::RBrace {
		walker.advance();
	} else {
		return None;
	}

	let (next, _) = match walker.peek() {
		Some(t) => t,
		None => return None,
	};
	if *next == Token::Semi {
		walker.advance();
	} else {
		return None;
	}

	Some(Stmt::StructDecl { ident, members })
}

fn print_stmt(stmt: &Stmt, indent: usize) {
	match stmt {
		Stmt::Empty => print!(
			"\r\n{:indent$}\x1b[9m(Empty)\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::VarDef { type_, ident } => {
			print!("\r\n{:indent$}\x1b[32mVar\x1b[0m(type: {type_}, ident: {ident})", "", indent = indent*4);
		}
		Stmt::VarDefs(vars) => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(",
				"",
				indent = indent * 4
			);
			for var in vars {
				print!("[type: {}, ident: {}], ", var.0, var.1);
			}
			print!(")");
		}
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
			print!(") = {value}");
		}
		Stmt::VarDecls {
			vars,
			value,
			is_const,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(",
				"",
				indent = indent * 4
			);
			for var in vars {
				print!("[type: {}, ident: {}],", var.0, var.1);
			}
			if *is_const {
				print!(" \x1b[4mconst\x1b[0m");
			}
			print!(") = {value}");
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
				"\r\n{:indent$}\x1b[32mStruct\x1b[0m(ident: {ident}, members: {{",
				"",
				indent = indent * 4
			);
			for stmt in members {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}})", "", indent = indent * 4);
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

/// Asserts the list of statements from the `parse()` function matches the right hand side.
#[cfg(test)]
macro_rules! assert_stmt {
    ($src:expr, $($stmt:expr),*) => {
        assert_eq!(parse($src), vec![
            $(
                $stmt,
            )*
        ])
    };
}

#[cfg(test)]
use crate::ast::{Fundamental, Ident, Lit, Primitive};

#[test]
#[rustfmt::skip]
fn var_def_decl() {
	// Variable definitions.
	assert_stmt!("int i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
		ident: Ident("i".into())
	});
	assert_stmt!("bool[2] b;", Stmt::VarDef {
		type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(Expr::Lit(Lit::Int(2)))),
		ident: Ident("b".into())
	});
	assert_stmt!("mat4 m[2][6];", Stmt::VarDef {
		type_: Type::Array2D(Primitive::Matrix(4, 4), Some(Expr::Lit(Lit::Int(2))), Some(Expr::Lit(Lit::Int(6)))),
		ident: Ident("m".into())
	});
	assert_stmt!("double[6] d[2];", Stmt::VarDef {
		type_: Type::Array2D(
			Primitive::Scalar(Fundamental::Double),
			Some(Expr::Lit(Lit::Int(2))),
			Some(Expr::Lit(Lit::Int(6)))
		),
		ident: Ident("d".into())
	});
	assert_stmt!("float a, b;", Stmt::VarDefs(vec![
		(Type::Basic(Primitive::Scalar(Fundamental::Float)), Ident("a".into())),
		(Type::Basic(Primitive::Scalar(Fundamental::Float)), Ident("b".into())),
	]));
	assert_stmt!("vec3[7][9] a[1], b[3];", Stmt::VarDefs(vec![
		(
			Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
				Some(Expr::Lit(Lit::Int(1))),
				Some(Expr::Lit(Lit::Int(7))),
				Some(Expr::Lit(Lit::Int(9))),
				]),
			Ident("a".into())
		),
		(
			Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
				Some(Expr::Lit(Lit::Int(3))),
				Some(Expr::Lit(Lit::Int(7))),
				Some(Expr::Lit(Lit::Int(9))),
				]),
			Ident("b".into())
		)
	]));

	// Variable declarations.
	assert_stmt!("uint u = 5;", Stmt::VarDecl {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Uint)),
		ident: Ident("u".into()),
		value: Expr::Lit(Lit::Int(5)),
		is_const: false
	});
	assert_stmt!("int[3] a[1] = {{4, 5, 6}};", Stmt::VarDecl {
		type_: Type::Array2D(
			Primitive::Scalar(Fundamental::Int),
			Some(Expr::Lit(Lit::Int(1))),
			Some(Expr::Lit(Lit::Int(3)))
		),
		ident: Ident("a".into()),
		value: Expr::Init(vec![Expr::Init(vec![
			Expr::Lit(Lit::Int(4)),
			Expr::Lit(Lit::Int(5)),
			Expr::Lit(Lit::Int(6))
		])]),
		is_const: false
	});
	assert_stmt!("double[] d = {1.0LF, 2.0LF};", Stmt::VarDecl {
		type_: Type::Array(Primitive::Scalar(Fundamental::Double), None),
		ident: Ident("d".into()),
		value: Expr::Init(vec![
			Expr::Lit(Lit::Double(1.0)),
			Expr::Lit(Lit::Double(2.0))
		]),
		is_const: false
	});
	assert_stmt!("vec2 a, b = vec2(1, 2);", Stmt::VarDecls {
		vars: vec![
			(Type::Basic(Primitive::Vector(Fundamental::Float, 2)), Ident("a".into())),
			(Type::Basic(Primitive::Vector(Fundamental::Float, 2)), Ident("b".into())),
		],
		value: Expr::Fn {
			ident: Ident("vec2".into()),
			args: vec![
				Expr::Lit(Lit::Int(1)),
				Expr::Lit(Lit::Int(2)),
			]
		},
		is_const: false
	});
	assert_stmt!("float[2] a, b = float[](5, 6);", Stmt::VarDecls {
		vars: vec![
			(Type::Array(Primitive::Scalar(Fundamental::Float), Some(Expr::Lit(Lit::Int(2)))), Ident("a".into())),
			(Type::Array(Primitive::Scalar(Fundamental::Float), Some(Expr::Lit(Lit::Int(2)))), Ident("b".into()))
		],
		value: Expr::ArrInit {
			arr: Box::from(Expr::Index {
				item: Box::from(Expr::Ident(Ident("float".into()))),
				i: None
			}),
			args: vec![
				Expr::Lit(Lit::Int(5)),
				Expr::Lit(Lit::Int(6))
			]
		},
		is_const: false
	});
}

#[test]
#[rustfmt::skip]
fn struct_decl() {
	assert_stmt!("struct S { int i; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
			ident: Ident("i".into())
		}]
	});
	assert_stmt!("struct S { bool[2] b; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(Expr::Lit(Lit::Int(2)))),
			ident: Ident("b".into())
		}]
	});
	assert_stmt!("struct S { mat4 m[2][6]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Array2D(Primitive::Matrix(4, 4), Some(Expr::Lit(Lit::Int(2))), Some(Expr::Lit(Lit::Int(6)))),
			ident: Ident("m".into())
		}]
	});
	assert_stmt!("struct S { vec3[7][9] a[1], b[3]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDefs(vec![
			(
				Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
					Some(Expr::Lit(Lit::Int(1))),
					Some(Expr::Lit(Lit::Int(7))),
					Some(Expr::Lit(Lit::Int(9))),
					]),
				Ident("a".into())
			),
			(
				Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
					Some(Expr::Lit(Lit::Int(3))),
					Some(Expr::Lit(Lit::Int(7))),
					Some(Expr::Lit(Lit::Int(9))),
					]),
				Ident("b".into())
			)
		])]
	});

	assert_stmt!("struct S { int i; bool b; float f1, f2; dvec2[1] d[2]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![
			Stmt::VarDef {
				type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
				ident: Ident("i".into())
			},
			Stmt::VarDef {
				type_: Type::Basic(Primitive::Scalar(Fundamental::Bool)),
				ident: Ident("b".into())
			},
			Stmt::VarDefs(vec![
				(
					Type::Basic(Primitive::Scalar(Fundamental::Float)),
					Ident("f1".into())
				),
				(
					Type::Basic(Primitive::Scalar(Fundamental::Float)),
					Ident("f2".into())
				)
			]),
			Stmt::VarDef {
				type_: Type::Array2D(
					Primitive::Vector(Fundamental::Double, 2),
					Some(Expr::Lit(Lit::Int(2))),
					Some(Expr::Lit(Lit::Int(1)))
				),
				ident: Ident("d".into())
			}
		]
	});
}
