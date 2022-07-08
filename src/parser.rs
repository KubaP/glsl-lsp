use crate::{
	ast::{Expr, Ident, Qualifier, Stmt, Type},
	expression::{expr_parser, Mode},
	lexer::{lexer, Op, Token},
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

/// Parse all of the top-level statements in the file.
pub fn parse(source: &str) -> Vec<Stmt> {
	let cst = lexer(source);
	println!("{cst:?}");

	let mut walker = Walker { cst, cursor: 0 };
	let mut stmts = Vec::new();

	'parser: while !walker.is_done() {
		// First, we look for any qualifiers which are always located first in a statement.
		let qualifiers = parse_qualifier_list(&mut walker);

		// Next, we look for any syntax which can be parsed as an expression, e.g. a `int[3]`.
		match expr_parser(&mut walker, Mode::Default) {
			// We tried to parse an expression and succeeded. We have an expression consisting of at least one
			// token.
			Some(expr) => {
				// Check if the expression can be parsed as a typename. If so, then we try to parse the following
				// tokens as statements which can start with a typename, i.e. variable or function defs/decls.
				if let Some(type_) = expr.to_type() {
					match parse_type_start(&mut walker, type_, qualifiers) {
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
					// After the `struct` keyword we are expecting a struct def/decl.
					Token::Struct => {
						walker.advance();
						match parse_struct(&mut walker, qualifiers) {
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

/// Parse a list of qualifiers if there are any, e.g.
/// - `const in ...`
/// - `flat uniform ...`
/// - `layout(location = 1) ...`.
fn parse_qualifier_list(walker: &mut Walker) -> Vec<Qualifier> {
	// Take tokens until we've run out of qualifiers.
	let mut qualifiers = Vec::new();
	'outer: loop {
		let current = match walker.peek() {
			Some((t, _)) => t,
			None => break 'outer,
		};

		use crate::ast::{Interpolation, Memory, Storage};

		match current {
			Token::Const => qualifiers.push(Qualifier::Storage(Storage::Const)),
			Token::In => qualifiers.push(Qualifier::Storage(Storage::In)),
			Token::Out => qualifiers.push(Qualifier::Storage(Storage::Out)),
			Token::InOut => qualifiers.push(Qualifier::Storage(Storage::InOut)),
			Token::Attribute => {
				qualifiers.push(Qualifier::Storage(Storage::Attribute))
			}
			Token::Uniform => {
				qualifiers.push(Qualifier::Storage(Storage::Uniform))
			}
			Token::Varying => {
				qualifiers.push(Qualifier::Storage(Storage::Varying))
			}
			Token::Buffer => {
				qualifiers.push(Qualifier::Storage(Storage::Buffer))
			}
			Token::Shared => {
				qualifiers.push(Qualifier::Storage(Storage::Shared))
			}
			Token::Centroid => {
				qualifiers.push(Qualifier::Storage(Storage::Centroid))
			}
			Token::Sample => {
				qualifiers.push(Qualifier::Storage(Storage::Sample))
			}
			Token::Patch => qualifiers.push(Qualifier::Storage(Storage::Patch)),
			Token::Flat => {
				qualifiers.push(Qualifier::Interpolation(Interpolation::Flat))
			}
			Token::Smooth => {
				qualifiers.push(Qualifier::Interpolation(Interpolation::Smooth))
			}
			Token::NoPerspective => qualifiers
				.push(Qualifier::Interpolation(Interpolation::NoPerspective)),
			Token::HighP => qualifiers.push(Qualifier::Precision),
			Token::MediumP => qualifiers.push(Qualifier::Precision),
			Token::LowP => qualifiers.push(Qualifier::Precision),
			Token::Invariant => qualifiers.push(Qualifier::Invariant),
			Token::Precise => qualifiers.push(Qualifier::Precise),
			Token::Coherent => {
				qualifiers.push(Qualifier::Memory(Memory::Coherent))
			}
			Token::Volatile => {
				qualifiers.push(Qualifier::Memory(Memory::Volatile))
			}
			Token::Restrict => {
				qualifiers.push(Qualifier::Memory(Memory::Restrict))
			}
			Token::Readonly => {
				qualifiers.push(Qualifier::Memory(Memory::Readonly))
			}
			Token::Writeonly => {
				qualifiers.push(Qualifier::Memory(Memory::Writeonly))
			}
			Token::Layout => {
				walker.advance();

				// Consume the opening `(` parenthesis.
				let current = match walker.peek() {
					Some((t, _)) => t,
					None => break,
				};
				if *current == Token::LParen {
					walker.advance();
				} else {
					break 'outer;
				}

				// Take layout identifiers until we reach the closing `)` parenthesis.
				let mut layouts = Vec::new();
				'identifiers: loop {
					let current = match walker.peek() {
						Some((t, _)) => t,
						None => break 'outer,
					};

					match current {
						Token::Comma => {
							walker.advance();
							continue 'identifiers;
						}
						// We don't consume the token because we perform that at the end of the 'outer loop.
						Token::RParen => break 'identifiers,
						Token::Semi => break 'outer,
						_ => {}
					}

					match current.to_layout() {
						Some(e) => {
							walker.advance();

							match e {
								Either::Left(layout) => {
									layouts.push(layout);
								}
								Either::Right(constructor) => {
									// Consume the `=` in `ident = expression`.
									let current = match walker.peek() {
										Some((t, _)) => t,
										None => break 'outer,
									};
									if *current == Token::Op(Op::Eq) {
										walker.advance();
									} else {
										break 'outer;
									}

									let expr = match expr_parser(
										walker,
										Mode::DisallowTopLevelList,
									) {
										Some(e) => e,
										None => break 'outer,
									};
									layouts.push(constructor(expr));
								}
							}
						}
						None => break 'outer,
					}
				}

				qualifiers.push(Qualifier::Layout(layouts));
			}
			// If we encounter anything other than a qualifier, that means we have reached the end of this list of
			// qualifiers and can move onto the next parsing step without consuming the current token.
			_ => break 'outer,
		}

		walker.advance();
	}

	qualifiers
}

/// Parse statements which begin with a type.
fn parse_type_start(
	walker: &mut Walker,
	type_: Type,
	qualifiers: Vec<Qualifier>,
) -> Option<Stmt> {
	// Check whether we have a function definition/declaration.
	match walker.peek() {
		Some((t, _)) => match t {
			Token::Ident(i) => match walker.lookahead_1() {
				Some((t2, _)) => match t2 {
					Token::LParen => {
						let ident = Ident(i.clone());
						walker.advance();
						walker.advance();
						return parse_fn(walker, type_, ident, qualifiers);
					}
					_ => {}
				},
				None => return None,
			},
			_ => {}
		},
		None => return None,
	};

	let next = match expr_parser(walker, Mode::BreakAtEq) {
		Some(e) => e,
		None => return None,
	};

	let idents = next.to_var_def_decl_or_fn_ident();
	if idents.is_empty() {
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
				Some(Stmt::VarDef {
					type_,
					ident,
					qualifiers,
				})
			}
			_ => Some(Stmt::VarDefs(typenames, qualifiers)),
		};
	} else if *next == Token::Op(Op::Eq) {
		walker.advance();
		// We have a variable declaration.
		let value = match expr_parser(walker, Mode::Default) {
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
					qualifiers,
				})
			}
			_ => Some(Stmt::VarDecls {
				vars: typenames,
				value,
				qualifiers,
			}),
		};
	} else {
		None
	}
}

/// Parse a function definition or declaration.
fn parse_fn(
	walker: &mut Walker,
	return_type: Type,
	ident: Ident,
	qualifiers: Vec<Qualifier>,
) -> Option<Stmt> {
	let mut params = Vec::new();

	loop {
		let qualifiers = parse_qualifier_list(walker);

		let expr = match expr_parser(walker, Mode::DisallowTopLevelList) {
			Some(e) => e,
			None => {
				let (current, _) = match walker.peek() {
					Some(t) => t,
					None => return None,
				};

				if *current == Token::RParen {
					walker.advance();
					break;
				} else if *current == Token::Comma {
					walker.advance();
					continue;
				} else {
					return None;
				}
			}
		};

		let type_ = match Type::parse(&expr) {
			Some(t) => t,
			None => return None,
		};

		let expr_2 = match expr_parser(walker, Mode::DisallowTopLevelList) {
			Some(e) => e,
			None => {
				let (current, _) = match walker.peek() {
					Some(t) => t,
					None => return None,
				};

				if *current == Token::Comma {
					walker.advance();
					params.push((type_, None, qualifiers));
					continue;
				} else if *current == Token::RParen {
					walker.advance();
					params.push((type_, None, qualifiers));
					break;
				} else {
					return None;
				}
			}
		};

		let (type_, ident) =
			match expr_2.to_var_def_decl_or_fn_ident().remove(0) {
				Either::Left(ident) => (type_.clone(), ident),
				Either::Right((ident, v)) => {
					(type_.clone().add_var_decl_arr_size(v), ident)
				}
			};

		params.push((type_, Some(ident), qualifiers));
	}

	let (next, _) = match walker.peek() {
		Some(t) => t,
		None => return None,
	};
	if *next == Token::Semi {
		walker.advance();
	} else if *next == Token::LBrace {
		walker.advance();

		let stmts = parse_scope_contents(walker, BRACE_DELIMITER);

		return Some(Stmt::FnDecl {
			return_type,
			ident,
			params,
			body: stmts,
			qualifiers,
		});
	} else {
		return None;
	}

	Some(Stmt::FnDef {
		return_type,
		ident,
		params,
		qualifiers,
	})
}

/// A function, which given in the current `walker`, determines whether to end parsing the current scope of
/// statements, and return back to the caller.
type EndScope = fn(&mut Walker) -> bool;

const BRACE_DELIMITER: EndScope = |walker| {
	let current = match walker.peek() {
		Some((t, _)) => t,
		None => return true,
	};

	if *current == Token::RBrace {
		walker.advance();
		true
	} else {
		false
	}
};

const SWITCH_CASE_DELIMITER: EndScope = |walker| {
	let current = match walker.peek() {
		Some((t, _)) => t,
		None => return true,
	};

	match current {
		Token::RBrace | Token::Case | Token::Default => true,
		_ => false,
	}
};

/// Parse the statements within a scope, up until the scope exit condition is encountered.
///
/// Whether the end delimiter is or is not consumed by the parser depends on the [`EndScope`] function passed in.
fn parse_scope_contents(
	walker: &mut Walker,
	exit_condition: EndScope,
) -> Vec<Stmt> {
	let mut stmts = Vec::new();

	'stmt: loop {
		// If we have reached a closing delimiter, break out of the loop and return the parsed statements.
		if exit_condition(walker) {
			break 'stmt;
		}

		// First, we look for any qualifiers because they are always located first in a statement.
		let qualifiers = parse_qualifier_list(walker);

		// Next, we look for any syntax which can be parsed as an expression, e.g. a `int[3]`.
		match expr_parser(walker, Mode::Default) {
			// We tried to parse an expression and succeeded. We have an expression consisting of at least one
			// token.
			Some(expr) => {
				// Check if the expression can be parsed as a typename. If so, then we try to parse the following
				// tokens as statements which can start with a typename, i.e. variable or function defs/decls.
				// FIXME: Cannot have a function within a function?
				if let Some(type_) = expr.to_type() {
					match parse_type_start(walker, type_, qualifiers) {
						Some(s) => stmts.push(s),
						None => 'till_next: loop {
							// We did not successfully parse a statement.
							let (next, _) = match walker.peek() {
								Some(t) => t,
								None => break 'stmt,
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
				} else {
					let current = match walker.peek() {
						Some((t, _)) => t,
						None => continue,
					};
					if *current == Token::Semi {
						walker.advance();
						stmts.push(Stmt::Expr(expr));
					} else {
						continue;
					}
				}
			}
			// We tried to parse an expression but that immediately failed. This means the current token is one
			// which cannot start an expression.
			None => {
				let (token, _) = walker.peek().unwrap();

				match token {
					Token::Semi => {
						walker.advance();
						stmts.push(Stmt::Empty);
					}
					Token::If => {
						walker.advance();

						// Consume the opening `(` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LParen {
							walker.advance();
						} else {
							continue;
						}

						let cond = match expr_parser(walker, Mode::Default) {
							Some(e) => e,
							None => continue,
						};

						// Consume the closing `)` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::RParen {
							walker.advance();
						} else {
							continue;
						}

						// Consume the opening `{` scope brace.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LBrace {
							walker.advance();
						} else {
							continue;
						}

						let body =
							parse_scope_contents(walker, BRACE_DELIMITER);

						let mut else_ = None;
						let mut else_ifs = Vec::new();
						'elseifs: loop {
							// Consume the opening `}` scope brace.
							let current = match walker.peek() {
								Some((t, _)) => t,
								None => continue,
							};
							if *current == Token::Else {
								walker.advance();
							} else {
								break 'elseifs;
							}

							let current = match walker.peek() {
								Some((t, _)) => t,
								None => continue,
							};
							if *current == Token::LBrace {
								// A final else branch.
								walker.advance();

								let body = parse_scope_contents(
									walker,
									BRACE_DELIMITER,
								);

								else_ = Some(body);
								break 'elseifs;
							} else if *current == Token::If {
								walker.advance();

								// Consume the opening `(` parenthesis.
								let current = match walker.peek() {
									Some((t, _)) => t,
									None => continue,
								};
								if *current == Token::LParen {
									walker.advance();
								} else {
									continue;
								}

								let cond =
									match expr_parser(walker, Mode::Default) {
										Some(e) => e,
										None => continue,
									};

								// Consume the closing `)` parenthesis.
								let current = match walker.peek() {
									Some((t, _)) => t,
									None => continue,
								};
								if *current == Token::RParen {
									walker.advance();
								} else {
									continue;
								}

								// Consume the opening `{` scope brace.
								let current = match walker.peek() {
									Some((t, _)) => t,
									None => continue,
								};
								if *current == Token::LBrace {
									walker.advance();
								} else {
									continue;
								}

								let body = parse_scope_contents(
									walker,
									BRACE_DELIMITER,
								);

								else_ifs.push((cond, body));
							} else {
								continue;
							}
						}

						stmts.push(Stmt::If {
							cond,
							body,
							else_ifs,
							else_,
						});
					}
					Token::Switch => {
						walker.advance();

						// Consume the opening `(` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LParen {
							walker.advance();
						} else {
							continue;
						}

						let expr = match expr_parser(walker, Mode::Default) {
							Some(e) => e,
							None => continue,
						};

						// Consume the closing `)` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::RParen {
							walker.advance();
						} else {
							continue;
						}

						// Consume the opening `{` scope brace.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LBrace {
							walker.advance();
						} else {
							continue;
						}

						let mut cases = Vec::new();
						'cases: loop {
							let current = match walker.peek() {
								Some((t, _)) => t,
								None => break 'cases,
							};

							match current {
								Token::Case => {
									walker.advance();

									let expr = match expr_parser(
										walker,
										Mode::Default,
									) {
										Some(e) => e,
										None => continue,
									};

									let current = match walker.peek() {
										Some((t, _)) => t,
										None => break 'cases,
									};
									if *current == Token::Colon {
										walker.advance();
									} else {
										continue;
									}

									let body = parse_scope_contents(
										walker,
										SWITCH_CASE_DELIMITER,
									);

									cases.push((Some(expr), body));
								}
								Token::Default => {
									walker.advance();

									let current = match walker.peek() {
										Some((t, _)) => t,
										None => break 'cases,
									};
									if *current == Token::Colon {
										walker.advance();
									} else {
										continue;
									}

									let body = parse_scope_contents(
										walker,
										SWITCH_CASE_DELIMITER,
									);

									cases.push((None, body));
								}
								Token::RBrace => {
									walker.advance();
									break 'cases;
								}
								_ => continue,
							}
						}

						stmts.push(Stmt::Switch { expr, cases });
					}
					Token::For => {
						walker.advance();

						// Consume the opening `(` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LParen {
							walker.advance();
						} else {
							continue;
						}

						let var = match expr_parser(walker, Mode::Default) {
							Some(expr) => {
								if let Some(type_) = expr.to_type() {
									match parse_type_start(
										walker,
										type_,
										vec![],
									) {
										Some(s) => Some(Box::from(s)),
										None => None,
									}
								} else {
									Some(Box::from(Stmt::Expr(expr)))
								}
							}
							None => None,
						};

						// Consume the seperator `;` semicolon.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							// parse_type_start consumes the `;` if there is one.
							//continue;
						}

						let cond = expr_parser(walker, Mode::Default);

						// Consume the seperator `;` semicolon.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						let inc = expr_parser(walker, Mode::Default);

						// Consume the closing `)` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::RParen {
							walker.advance();
						} else {
							continue;
						}

						// Consume the opening `{` scope brace.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LBrace {
							walker.advance();
						} else {
							continue;
						}

						let body =
							parse_scope_contents(walker, BRACE_DELIMITER);

						stmts.push(Stmt::For {
							var,
							cond,
							inc,
							body,
						});
					}
					Token::While => {
						walker.advance();

						// Consume the opening `(` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LParen {
							walker.advance();
						} else {
							continue;
						}

						let cond = match expr_parser(walker, Mode::Default) {
							Some(e) => e,
							None => continue,
						};

						// Consume the closing `)` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::RParen {
							walker.advance();
						} else {
							continue;
						}

						// Consume the opening `{` scope brace.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LBrace {
							walker.advance();
						} else {
							continue;
						}

						let body =
							parse_scope_contents(walker, BRACE_DELIMITER);

						stmts.push(Stmt::While { cond, body });
					}
					Token::Do => {
						walker.advance();

						// Consume the opening `{` scope brace.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LBrace {
							walker.advance();
						} else {
							continue;
						}

						let body =
							parse_scope_contents(walker, BRACE_DELIMITER);

						// Consume the `while` keyword.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::While {
							walker.advance();
						} else {
							continue;
						}

						// Consume the opening `(` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::LParen {
							walker.advance();
						} else {
							continue;
						}

						let cond = match expr_parser(walker, Mode::Default) {
							Some(e) => e,
							None => continue,
						};

						// Consume the closing `)` parenthesis.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::RParen {
							walker.advance();
						} else {
							continue;
						}

						// Consume the statement-ending `;` semicolon.
						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						stmts.push(Stmt::DoWhile { cond, body });
					}
					Token::Return => {
						walker.advance();

						// Look for the optional return value expression.
						let return_expr = expr_parser(walker, Mode::Default);

						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						stmts.push(Stmt::Return(return_expr));
					}
					Token::Break => {
						walker.advance();

						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						stmts.push(Stmt::Break);
					}
					Token::Continue => {
						walker.advance();

						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						stmts.push(Stmt::Continue);
					}
					Token::Discard => {
						walker.advance();

						let current = match walker.peek() {
							Some((t, _)) => t,
							None => continue,
						};
						if *current == Token::Semi {
							walker.advance();
						} else {
							continue;
						}

						stmts.push(Stmt::Discard);
					}
					_ => break 'stmt,
				}
			}
		}
	}

	stmts
}

/// Parse a struct definition or declaration.
fn parse_struct(
	walker: &mut Walker,
	qualifiers: Vec<Qualifier>,
) -> Option<Stmt> {
	let ident = match expr_parser(walker, Mode::Default) {
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
	} else if *next == Token::Semi {
		walker.advance();
		return Some(Stmt::StructDef { ident, qualifiers });
	} else {
		return None;
	}

	let mut members = Vec::new();
	'members: loop {
		let qualifiers = parse_qualifier_list(walker);

		match expr_parser(walker, Mode::Default) {
			Some(expr) => {
				if let Some(type_) = expr.to_type() {
					let next = match expr_parser(walker, Mode::Default) {
						Some(e) => e,
						None => return None,
					};

					let idents = next.to_var_def_decl_or_fn_ident();
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
								Stmt::VarDef {
									type_,
									ident,
									qualifiers,
								}
							}
							_ => Stmt::VarDefs(typenames, qualifiers),
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

	let instance = match expr_parser(walker, Mode::Default) {
		Some(e) => match e {
			Expr::Ident(i) => Some(i),
			_ => return None,
		},
		None => None,
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

	Some(Stmt::StructDecl {
		ident,
		members,
		qualifiers,
		instance,
	})
}

fn print_stmt(stmt: &Stmt, indent: usize) {
	match stmt {
		Stmt::Empty => print!(
			"\r\n{:indent$}\x1b[9m(Empty)\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::VarDef {
			type_,
			ident,
			qualifiers,
		} => {
			print!("\r\n{:indent$}\x1b[32mVar\x1b[0m(type: {type_}, ident: {ident}, qualifiers: [", "", indent = indent*4);
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("])");
		}
		Stmt::VarDefs(vars, qualifiers) => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(",
				"",
				indent = indent * 4
			);
			for var in vars {
				print!("[type: {}, ident: {}], ", var.0, var.1);
			}
			print!(" qualifiers: [");
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("])");
		}
		Stmt::VarDecl {
			type_,
			ident,
			value,
			qualifiers,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(type: {type_}, ident: {ident}, qualifiers: [",
				"",
				indent = indent * 4
			);
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("]) = {value}");
		}
		Stmt::VarDecls {
			vars,
			value,
			qualifiers,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(",
				"",
				indent = indent * 4
			);
			for var in vars {
				print!("[type: {}, ident: {}], ", var.0, var.1);
			}
			print!(" qualifiers: [");
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("]) = {value}");
		}
		Stmt::FnDef {
			return_type,
			ident,
			params,
			qualifiers,
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return: {return_type}, ident: {ident}, params: [",
				"",
				indent = indent * 4
			);
			for (type_, ident, qualifiers) in params {
				match (ident, qualifiers) {
					(Some(ident), _) if !qualifiers.is_empty() => {
						print!("{type_}: {ident} qualifiers: [");
						for qualifier in qualifiers {
							print!("{qualifier}, ");
						}
						print!("], ");
					}
					(Some(ident), _) => print!("{type_}: {ident}, "),
					(None, _) if !qualifiers.is_empty() => {
						print!("{type_} qualifiers: [");
						for qualifier in qualifiers {
							print!("{qualifier}, ");
						}
						print!("], ");
					}
					(None, _) => print!("{type_}, "),
				}
			}
			print!("], qualifiers: [");
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("])");
		}
		Stmt::FnDecl {
			return_type,
			ident,
			params,
			body,
			qualifiers,
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return: {return_type}, ident: {ident}, params: [",
				"",
				indent = indent * 4
			);
			for (type_, ident, qualifiers) in params {
				match (ident, qualifiers) {
					(Some(ident), _) if !qualifiers.is_empty() => {
						print!("{type_}: {ident} qualifiers: [");
						for qualifier in qualifiers {
							print!("{qualifier}, ");
						}
						print!("], ");
					}
					(Some(ident), _) => print!("{type_}: {ident}, "),
					(None, _) if !qualifiers.is_empty() => {
						print!("{type_} qualifiers: [");
						for qualifier in qualifiers {
							print!("{qualifier}, ");
						}
						print!("], ");
					}
					(None, _) => print!("{type_}, "),
				}
			}
			print!("], qualifiers: [");
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("]) {{");
			for inner in body {
				print_stmt(inner, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::StructDef { ident, qualifiers } => {
			print!(
				"\r\n{:indent$}\x1b[90;9mStruct\x1b[0m(ident: {ident}, qualifiers: [",
				"",
				indent = indent * 4
			);
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			print!("])");
		}
		Stmt::StructDecl {
			ident,
			members,
			qualifiers,
			instance,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mStruct\x1b[0m(ident: {ident}, members: {{",
				"",
				indent = indent * 4
			);
			for stmt in members {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}, qualifiers: [", "", indent = indent * 4);
			for qualifier in qualifiers {
				print!("{qualifier}, ");
			}
			if let Some(instance) = instance {
				print!("], instance: {instance})");
			} else {
				print!("])");
			}
		}
		Stmt::Expr(expr) => {
			print!("\r\n{:indent$}{expr}", "", indent = indent * 4);
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
		Stmt::While { cond, body } => {
			print!("\r\n{:indent$}While({cond}) {{", "", indent = indent * 4);
			for stmt in body {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::DoWhile { cond, body } => {
			print!(
				"\r\n{:indent$}Do-While({cond}) {{",
				"",
				indent = indent * 4
			);
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
		Stmt::Continue => {
			print!("\r\n{:indent$}CONTINUE", "", indent = indent * 4)
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
use crate::ast::{Fundamental, Lit, Primitive};

#[test]
#[rustfmt::skip]
fn var_def_decl() {
	// Variable definitions.
	assert_stmt!("int i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
		ident: Ident("i".into()),
		qualifiers: vec![]
	});
	assert_stmt!("bool[2] b;", Stmt::VarDef {
		type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(Expr::Lit(Lit::Int(2)))),
		ident: Ident("b".into()),
		qualifiers: vec![]
	});
	assert_stmt!("mat4 m[2][6];", Stmt::VarDef {
		type_: Type::Array2D(Primitive::Matrix(4, 4), Some(Expr::Lit(Lit::Int(2))), Some(Expr::Lit(Lit::Int(6)))),
		ident: Ident("m".into()),
		qualifiers: vec![]
	});
	assert_stmt!("double[6] d[2];", Stmt::VarDef {
		type_: Type::Array2D(
			Primitive::Scalar(Fundamental::Double),
			Some(Expr::Lit(Lit::Int(2))),
			Some(Expr::Lit(Lit::Int(6)))
		),
		ident: Ident("d".into()),
		qualifiers: vec![]
	});
	assert_stmt!("float a, b;", Stmt::VarDefs(vec![
		(Type::Basic(Primitive::Scalar(Fundamental::Float)), Ident("a".into())),
		(Type::Basic(Primitive::Scalar(Fundamental::Float)), Ident("b".into())),
	], vec![]));
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
	], vec![]));

	// Variable declarations.
	assert_stmt!("uint u = 5;", Stmt::VarDecl {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Uint)),
		ident: Ident("u".into()),
		value: Expr::Lit(Lit::Int(5)),
		qualifiers: vec![]
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
		qualifiers: vec![]
	});
	assert_stmt!("double[] d = {1.0LF, 2.0LF};", Stmt::VarDecl {
		type_: Type::Array(Primitive::Scalar(Fundamental::Double), None),
		ident: Ident("d".into()),
		value: Expr::Init(vec![
			Expr::Lit(Lit::Double(1.0)),
			Expr::Lit(Lit::Double(2.0))
		]),
		qualifiers: vec![]
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
		qualifiers: vec![]
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
		qualifiers: vec![]
	});
}

#[test]
#[rustfmt::skip]
fn struct_def_decl() {
	// Single-member structs.
	assert_stmt!("struct S;", Stmt::StructDef { ident: Ident("S".into()), qualifiers: vec![] });
	assert_stmt!("struct S { int i; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
			ident: Ident("i".into()),
			qualifiers: vec![]
		}],
		qualifiers: vec![],
		instance: None,
	});
	assert_stmt!("struct S { bool[2] b; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(Expr::Lit(Lit::Int(2)))),
			ident: Ident("b".into()),
			qualifiers: vec![]
		}],
		qualifiers: vec![],
		instance: None,
	});
	assert_stmt!("struct S { mat4 m[2][6]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Array2D(Primitive::Matrix(4, 4), Some(Expr::Lit(Lit::Int(2))), Some(Expr::Lit(Lit::Int(6)))),
			ident: Ident("m".into()),
			qualifiers: vec![]
		}],
		qualifiers: vec![],
		instance: None,
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
		], vec![])],
		qualifiers: vec![],
		instance: None,
	});

	// Multi-member struct.
	assert_stmt!("struct S { int i; bool b; float f1, f2; dvec2[1] d[2]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![
			Stmt::VarDef {
				type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
				ident: Ident("i".into()),
				qualifiers: vec![]
			},
			Stmt::VarDef {
				type_: Type::Basic(Primitive::Scalar(Fundamental::Bool)),
				ident: Ident("b".into()),
				qualifiers: vec![]
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
			], vec![]),
			Stmt::VarDef {
				type_: Type::Array2D(
					Primitive::Vector(Fundamental::Double, 2),
					Some(Expr::Lit(Lit::Int(2))),
					Some(Expr::Lit(Lit::Int(1)))
				),
				ident: Ident("d".into()),
				qualifiers: vec![]
			}
		],
		qualifiers: vec![],
		instance: None,
	});
}
