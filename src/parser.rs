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
		let start = match expr_parser(&mut walker) {
			Some(e) => e,
			None => break 'parser,
		};

		if let Some(type_) = start.to_type() {
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
