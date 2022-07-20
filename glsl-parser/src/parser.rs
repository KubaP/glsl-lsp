use crate::{
	ast::{ExprTy, Ident, Qualifier, Stmt, Type},
	error::SyntaxErr,
	expression::{expr_parser, Mode},
	lexer::{lexer, OpTy, Token},
	log,
	span::{Span, Spanned},
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

	/// Returns the [`Span`] of the current `Token`.
	///
	/// *Note:* If we have reached the end of the tokens, this will return the value of
	/// [`get_last_span()`](Self::get_last_span).
	pub fn get_current_span(&self) -> Span {
		match self.cst.get(self.cursor) {
			Some(t) => t.1,
			None => self.get_last_span(),
		}
	}

	/// Returns the [`Span`] of the previous `Token`.
	///
	/// *Note:* If the current token is the first, the span returned will be `0-0`.
	pub fn get_previous_span(&self) -> Span {
		self.cst.get(self.cursor - 1).map_or(Span::empty(), |t| t.1)
	}

	/// Returns the [`Span`] of the last `Token`.
	///
	/// *Note:* If there are no tokens, the span returned will be `0-0`.
	pub fn get_last_span(&self) -> Span {
		self.cst.last().map_or(Span::empty(), |t| t.1)
	}
}

/// Parse all of the top-level statements in the file.
pub fn parse(source: &str) -> (Vec<Stmt>, Vec<SyntaxErr>) {
	let cst = lexer(source);
	log!("{cst:?}");

	let mut walker = Walker { cst, cursor: 0 };
	let mut stmts = Vec::new();
	let mut errors = Vec::new();

	'parser: while !walker.is_done() {
		// First, we look for any qualifiers which are always located first in a statement.
		let (qualifiers, mut qualifier_errs) =
			parse_qualifier_list(&mut walker);
		errors.append(&mut qualifier_errs);

		// Next, we look for any syntax which can be parsed as an expression, e.g. a `int[3]`.
		match expr_parser(&mut walker, Mode::Default, &[]) {
			// We tried to parse an expression and succeeded. We have an expression consisting of at least one
			// token.
			(Some(expr), _) => {
				// Check if the expression can be parsed as a typename. If so, then we try to parse the following
				// tokens as statements which can start with a typename, i.e. variable or function defs/decls.
				if let Some(type_) = expr.to_type() {
					match parse_type_start(&mut walker, type_, qualifiers) {
						(Some(s), mut errs) => {
							errors.append(&mut errs);
							stmts.push(s);
						}
						(None, mut errs) => {
							errors.append(&mut errs);

							'till_next: loop {
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
							}
						}
					};
				}
			}
			// We tried to parse an expression but that immediately failed. This means the current token is one
			// which cannot start an expression.
			(None, _) => {
				let (token, current_span) =
					walker.peek().map(|t| (&t.0, t.1.clone())).unwrap();

				match token {
					// After the `struct` keyword we are expecting a struct def/decl.
					Token::Struct => {
						walker.advance();
						match parse_struct(
							&mut walker,
							qualifiers,
							current_span,
						) {
							(Some(s), mut errs) => {
								errors.append(&mut errs);
								stmts.push(s);
							}
							(None, mut errs) => {
								errors.append(&mut errs);
								break 'parser;
							}
						}
					}
					_ => break 'parser,
				}
			}
		}
	}

	(stmts, errors)
}

/// Parse a list of qualifiers if there are any, e.g.
/// - `const in ...`
/// - `flat uniform ...`
/// - `layout(location = 1) ...`.
fn parse_qualifier_list(
	walker: &mut Walker,
) -> (Vec<Qualifier>, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	let mut qualifiers = Vec::new();
	// Consume tokens until we've run out of qualifiers.
	'outer: loop {
		let (current, current_span) = match walker.peek() {
			Some(t) => t,
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
				let kw_span = *current_span;
				walker.advance();

				// Consume the opening `(` parenthesis.
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterLayout(
							kw_span.end_zero_width(),
						));
						break 'outer;
					}
				};

				let l_paren_span;
				if *current == Token::LParen {
					l_paren_span = *current_span;
					walker.advance();
				} else {
					errors.push(SyntaxErr::ExpectedParenAfterLayout(
						kw_span.end_zero_width(),
					));
					break 'outer;
				};

				let mut layouts = Vec::new();
				// Consume layout identifiers until we reach the closing `)` parenthesis.
				'identifiers: loop {
					let (current, current_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// Since we are still in this loop, that means we haven't found the closing `)`
							// parenthesis yet, but we've now reached the end of the token stream.
							errors.push(SyntaxErr::ExpectedParenAtEndOfLayout(
								l_paren_span,
								walker.get_last_span().end_zero_width(),
							));
							break 'outer;
						}
					};

					match current {
						// Consume the `,` separator and continue looking for a layout identifier.
						Token::Comma => {
							walker.advance();
							continue 'identifiers;
						}
						// Consume the closing `)` parenthesis and stop parsing this `layout`. We don't consume the
						// token because we perform that at the end of the 'outer loop.
						Token::RParen => break 'identifiers,
						Token::Semi => break 'outer,
						_ => {}
					}

					let ident_span = *current_span;
					// We are expecting a token which is a valid layout identifier.
					match current.to_layout() {
						Some(e) => {
							walker.advance();

							match e {
								Either::Left(layout) => {
									layouts.push(layout);
								}
								Either::Right(constructor) => {
									// Consume the `=` in `ident = expression`.
									let (current, current_span) =
										match walker.peek() {
											Some(t) => t,
											None => {
												errors.push(SyntaxErr::ExpectedEqAfterLayoutIdent(
													walker.get_last_span().end_zero_width()
												));
												break 'outer;
											}
										};
									if *current == Token::Op(OpTy::Eq) {
										walker.advance();
									} else {
										errors.push(SyntaxErr::ExpectedEqAfterLayoutIdent(
											*current_span
										));
										break 'outer;
									}

									// Consume the next `expression` in `ident = expression`.
									let expr = match expr_parser(
										walker,
										Mode::DisallowTopLevelList,
										&[Token::Comma, Token::RParen],
									) {
										(Some(e), mut err) => {
											errors.append(&mut err);
											e
										}
										(None, _) => {
											errors.push(SyntaxErr::ExpectedValExprAfterLayoutIdent(
												ident_span.end_zero_width()
											));
											break 'outer;
										}
									};
									layouts.push(constructor(expr));
								}
							}
						}
						None => {
							// We found a token which can not be a valid layout identifier.
							errors.push(SyntaxErr::InvalidLayoutIdentifier(
								*current_span,
							));
							break 'outer;
						}
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

	(qualifiers, errors)
}

/// Parse statements which begin with a type.
fn parse_type_start(
	walker: &mut Walker,
	type_: Type,
	qualifiers: Vec<Qualifier>,
) -> (Option<Stmt>, Vec<SyntaxErr>) {
	// Check whether we have a function definition/declaration.
	match walker.peek() {
		Some((t, t_span)) => match t {
			Token::Ident(i) => match walker.lookahead_1() {
				Some((t2, paren_span)) => match t2 {
					Token::LParen => {
						let ident = Ident {
							name: i.clone(),
							span: *t_span,
						};
						let l_paren_span = *paren_span;
						walker.advance();
						walker.advance();
						return parse_fn(
							walker,
							type_,
							ident,
							qualifiers,
							l_paren_span,
						);
					}
					_ => {}
				},
				None => return (None, vec![]),
			},
			_ => {}
		},
		None => return (None, vec![]),
	};

	let next = match expr_parser(walker, Mode::BreakAtEq, &[]) {
		(Some(e), _) => e,
		(None, _) => return (None, vec![]),
	};

	let idents = next.to_var_def_decl_or_fn_ident();
	if idents.is_empty() {
		return (None, vec![]);
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
		None => return (None, vec![]),
	};

	if *next == Token::Semi {
		// We have a variable definition.
		walker.advance();
		return match typenames.len() {
			1 => {
				let (type_, ident) = typenames.remove(0);
				(
					Some(Stmt::VarDef {
						type_,
						ident,
						qualifiers,
					}),
					vec![],
				)
			}
			_ => (Some(Stmt::VarDefs(typenames, qualifiers)), vec![]),
		};
	} else if *next == Token::Op(OpTy::Eq) {
		walker.advance();
		// We have a variable declaration.
		let value = match expr_parser(walker, Mode::Default, &[Token::Semi]) {
			(Some(e), _) => e,
			(None, _) => return (None, vec![]),
		};

		let (next, _) = match walker.peek() {
			Some(t) => t,
			None => return (None, vec![]),
		};
		if *next == Token::Semi {
			walker.advance();
		} else {
			return (None, vec![]);
		}

		return match typenames.len() {
			1 => {
				let (type_, ident) = typenames.remove(0);
				(
					Some(Stmt::VarDecl {
						type_,
						ident,
						value,
						qualifiers,
					}),
					vec![],
				)
			}
			_ => (
				Some(Stmt::VarDecls {
					vars: typenames,
					value,
					qualifiers,
				}),
				vec![],
			),
		};
	} else {
		(None, vec![])
	}
}

/// Parse a function definition or declaration.
fn parse_fn(
	walker: &mut Walker,
	return_type: Type,
	ident: Ident,
	qualifiers: Vec<Qualifier>,
	l_paren_span: Span,
) -> (Option<Stmt>, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	let mut params = Vec::new();

	// If this is set to `true`, that means we have just started parsing the contents after the opening `(`.
	let mut just_started = true;
	// If this is set to `true`, that means we are expecting either a `,` or a `)`.
	let mut just_finished_param = false;

	// Consume tokens until we've reached the closing `)` parenthesis.
	'param: loop {
		let (current, current_span) = match walker.peek() {
			Some((t, s)) => (t, *s),
			None => {
				// Since we are still in this loop, that means we haven't found the closing `)` parenthesis yet,
				// but we've now reached the end of the token stream.
				errors.push(SyntaxErr::ExpectedParenAtEndOfParamList(
					l_paren_span,
					walker.get_last_span().end_zero_width(),
				));
				return (None, errors);
			}
		};

		match current {
			// Consume the `,` separator and continue looking for a parameter.
			Token::Comma => {
				if !just_finished_param {
					// We have a `,` without a parameter before it, e.g. `int i, ,`.
					errors.push(SyntaxErr::MissingTypeInParamList(
						Span::new_between(
							walker.get_previous_span(),
							current_span,
						),
					));
				}
				just_finished_param = false;
				walker.advance();
				continue 'param;
			}
			// Consume the closing `)` parenthesis and stop looking for parameters.
			Token::RParen => {
				if !just_started && !just_finished_param {
					// We have a `, )`, i.e. are missing a parameter between the comma and parenthesis.
					errors.push(SyntaxErr::MissingTypeInParamList(
						Span::new_between(
							walker.get_previous_span(),
							current_span,
						),
					));
				}
				walker.advance();
				break 'param;
			}
			// Even though we are missing a necessary token to make this a valid function definition, it still
			// makes sense to just treat this as a "valid" function definition for analysis/goto/etc purposes. For
			// the purposes of this, we assume that the current parameters are all the parameters this function
			// will take. We do produce an error though about the missing token.
			Token::Semi => {
				errors.push(SyntaxErr::ExpectedParenAtEndOfParamList(
					l_paren_span,
					current_span,
				));
				return (
					Some(Stmt::FnDef {
						return_type,
						ident,
						params,
						qualifiers,
					}),
					errors,
				);
			}
			// Even though we are missing a necessary token to make this a valid function definition, it still
			// makes sense to just treat this is a potentially "valid" function declaration for analysis/goto/etc
			// purposes. For the purposes of this, we assume that the current parameters are all the parameters
			// this function will take. We do produce an error though about the missing token.
			Token::LBrace => {
				errors.push(SyntaxErr::ExpectedParenAtEndOfParamList(
					l_paren_span,
					current_span,
				));
				break 'param;
			}
			_ => {
				if just_finished_param {
					// We have just finished a parameter and we have neither a `,` nor a `)` nor one of the other
					// parameter-list ending tokens, and we have encountered what may be the next parameter, this
					// an error, e.g. `int i float`.
					errors.push(SyntaxErr::ExpectedCommaAfterParamInParamList(
						Span::new_between(
							walker.get_previous_span(),
							current_span,
						),
					));
				}
			}
		}

		just_started = false;

		// Look for any optional qualifiers.
		let (qualifiers, mut qualifier_errs) = parse_qualifier_list(walker);
		errors.append(&mut qualifier_errs);

		// Look for a type.
		let type_ = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			&[Token::Semi, Token::LBrace],
		) {
			// We found an expression, so we try to parse it as a type.
			(Some(e), errs) => {
				for err in errs {
					match err {
						SyntaxErr::FoundOperandAfterOperand(_, _) => {}
						_ => errors.push(err),
					}
				}

				match Type::parse(&e.ty) {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedType(e.span));
						just_finished_param = true;
						continue 'param;
					}
				}
			}
			// We failed to parse any expression, so this means the current token is one which cannot start an
			// expression.
			(None, _) => {
				just_finished_param = true;
				// Note: We need to `peek()` again because we may have found qualifiers.
				match walker.peek() {
					Some((current, current_span)) => {
						match current {
							// The check at the beginning of the 'param loop will produce the relevant error about
							// the missing type identifier.
							Token::Comma => continue 'param,
							Token::RParen => {
								// Since we are here, that means we have at least one parameter separated by a
								// comma and we've now come across the closing `)` parenthesis, i.e. `int,)`.
								errors.push(SyntaxErr::MissingTypeInParamList(
									current_span.start_zero_width(),
								));
								walker.advance();
								break 'param;
							}
							Token::Semi | Token::LBrace => {
								errors.push(SyntaxErr::MissingTypeInParamList(
									current_span.start_zero_width(),
								));
								continue 'param;
							}
							_ => {
								// We have something like a keyword which is illegal.
								errors.push(SyntaxErr::ExpectedType(
									*current_span,
								));
								walker.advance();
								continue 'param;
							}
						}
					}
					// The first check in the 'param loop deals with reaching the end-of-file.
					None => continue 'param,
				};
			}
		};

		// Look for an identifier.
		let expr = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			&[Token::LBrace, Token::Semi],
		) {
			(Some(e), mut errs) => {
				// TODO: Check if this can be a valid identifier.
				errors.append(&mut errs);
				e
			}
			// Identifiers are optional, so if we haven't found one, we move onto the next parameter.
			(None, _) => {
				just_finished_param = true;
				// Note: We need to `peek()` again because we may have found qualifiers.
				match walker.peek() {
					Some((current, current_span)) => {
						params.push((type_, None, qualifiers));

						match current {
							Token::Comma => continue 'param,
							Token::RParen => {
								walker.advance();
								break 'param;
							}
							Token::Semi | Token::LBrace => {
								continue 'param;
							}
							_ => {
								// We have something like a keyword which is illegal.
								errors.push(SyntaxErr::ExpectedIdent(
									*current_span,
								));
								walker.advance();
								continue 'param;
							}
						}
					}
					// The first check in the 'param loop deals with reaching the end-of-file.
					None => continue 'param,
				}
			}
		};

		// Since a type-identifier definition may be split up, e.g. `int i[3]`, we now convert the two "items"
		// into the actual type and identifier.
		let (type_, ident) = match expr.to_var_def_decl_or_fn_ident().remove(0)
		{
			Either::Left(ident) => (type_.clone(), ident),
			Either::Right((ident, v)) => {
				(type_.clone().add_var_decl_arr_size(v), ident)
			}
		};

		params.push((type_, Some(ident), qualifiers));
		just_finished_param = true;
	}

	// Consume either the `;` for a function definition, or a `{` for a function declaration.
	let (current, _) = match walker.peek() {
		Some(t) => t,
		None => {
			// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
			// treat this as a "valid" function definition for analysis/goto/etc purposes. We do produce an error
			// though about the missing token.
			errors.push(SyntaxErr::ExpectedSemiOrScopeAfterParamList(
				walker.get_last_span().end_zero_width(),
			));
			return (
				Some(Stmt::FnDef {
					return_type,
					ident,
					params,
					qualifiers,
				}),
				errors,
			);
		}
	};
	if *current == Token::Semi {
		walker.advance();
		(
			Some(Stmt::FnDef {
				return_type,
				ident,
				params,
				qualifiers,
			}),
			errors,
		)
	} else if *current == Token::LBrace {
		walker.advance();

		// Parse the function body, including the closing `}` brace.
		let stmts = parse_scope_contents(walker, BRACE_DELIMITER);

		(
			Some(Stmt::FnDecl {
				return_type,
				ident,
				params,
				body: stmts,
				qualifiers,
			}),
			errors,
		)
	} else {
		// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
		// treat this as a "valid" function definition for analysis/goto/etc purposes. We do produce an error
		// though about the missing token.
		errors.push(SyntaxErr::ExpectedSemiOrScopeAfterParamList(
			walker.get_previous_span().end_zero_width(),
		));
		(
			Some(Stmt::FnDef {
				return_type,
				ident,
				params,
				qualifiers,
			}),
			errors,
		)
	}
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

		// If we immediately encounter an opening `{` brace, that means we have a delimited scope.
		let (token, _) = walker.peek().unwrap();
		if *token == Token::LBrace {
			walker.advance();
			stmts.push(Stmt::Scope(parse_scope_contents(
				walker,
				BRACE_DELIMITER,
			)));
			continue 'stmt;
		}

		// First, we look for any qualifiers because they are always located first in a statement.
		let (qualifiers, _qualifier_errs) = parse_qualifier_list(walker);

		// Next, we look for any syntax which can be parsed as an expression, e.g. a `int[3]`.
		match expr_parser(walker, Mode::Default, &[Token::Semi]) {
			// We tried to parse an expression and succeeded. We have an expression consisting of at least one
			// token.
			(Some(expr), _) => {
				// Check if the expression can be parsed as a typename. If so, then we try to parse the following
				// tokens as statements which can start with a typename, i.e. variable or function defs/decls.
				// FIXME: Cannot have a function within a function?
				if let Some(type_) = expr.to_type() {
					match parse_type_start(walker, type_, qualifiers) {
						(Some(s), _errs) => stmts.push(s),
						(None, _) => 'till_next: loop {
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
			(None, _) => {
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

						let cond = match expr_parser(
							walker,
							Mode::Default,
							&[Token::RParen],
						) {
							(Some(e), _) => e,
							(None, _) => continue,
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

								let cond = match expr_parser(
									walker,
									Mode::Default,
									&[Token::RParen],
								) {
									(Some(e), _) => e,
									(None, _) => continue,
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

						let expr = match expr_parser(
							walker,
							Mode::Default,
							&[Token::RParen],
						) {
							(Some(e), _) => e,
							(None, _) => continue,
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
										&[Token::Colon],
									) {
										(Some(e), _) => e,
										(None, _) => continue,
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

						let var = match expr_parser(
							walker,
							Mode::Default,
							&[Token::Semi],
						) {
							(Some(expr), _) => {
								if let Some(type_) = expr.to_type() {
									match parse_type_start(
										walker,
										type_,
										vec![],
									) {
										(Some(s), _errs) => Some(Box::from(s)),
										(None, _) => None,
									}
								} else {
									Some(Box::from(Stmt::Expr(expr)))
								}
							}
							(None, _) => None,
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

						let (cond, _) =
							expr_parser(walker, Mode::Default, &[Token::Semi]);

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

						let (inc, _) = expr_parser(
							walker,
							Mode::Default,
							&[Token::RParen],
						);

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

						let cond = match expr_parser(
							walker,
							Mode::Default,
							&[Token::RParen],
						) {
							(Some(e), _) => e,
							(None, _) => continue,
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

						let cond = match expr_parser(
							walker,
							Mode::Default,
							&[Token::RParen],
						) {
							(Some(e), _) => e,
							(None, _) => continue,
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
						let (return_expr, _) =
							expr_parser(walker, Mode::Default, &[Token::Semi]);

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
	struct_kw_span: Span,
) -> (Option<Stmt>, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	// Look for an identifier.
	let ident = match expr_parser(
		walker,
		Mode::TakeOneUnit,
		&[Token::LBrace, Token::Semi],
	) {
		(Some(e), _) => match e.ty {
			// TODO: Check if this can be a valid identifier with better error recovery.
			ExprTy::Ident(i) => i,
			_ => {
				errors
					.push(SyntaxErr::ExpectedIdent(walker.get_current_span()));
				return (None, errors);
			}
		},
		(None, _) => {
			errors.push(SyntaxErr::ExpectedIdentAfterStructKw(
				walker.get_current_span(),
			));
			return (None, errors);
		}
	};

	// Consume either the `;` for a struct definition, or a `{` for a struct declaration.
	let (current, current_span) = match walker.peek() {
		Some(t) => t,
		None => {
			errors.push(SyntaxErr::ExpectedScopeAfterStructIdent(
				walker.get_last_span().end_zero_width(),
			));
			return (None, errors);
		}
	};
	let l_brace_span = if *current == Token::LBrace {
		*current_span
	} else if *current == Token::Semi {
		// Even though struct definitions are illegal, it still makes sense to just treat this as a "valid"
		// struct definition for analysis/goto/etc purposes. We do produce an error though about the illegality of
		// a struct definition.
		errors.push(SyntaxErr::StructDefIsIllegal(
			*current_span,
			Span::new(struct_kw_span.start, current_span.end),
		));
		walker.advance();
		return (Some(Stmt::StructDef { ident, qualifiers }), errors);
	} else {
		errors.push(SyntaxErr::ExpectedScopeAfterStructIdent(
			Span::new_between(walker.get_last_span(), *current_span),
		));
		return (None, errors);
	};
	walker.advance();

	// Parse the struct body, including the closing `}` brace.
	let members = parse_scope_contents(walker, BRACE_DELIMITER);
	// We don't remove invalid statements because we would loose information for the AST.
	let mut count = 0;
	members.iter().for_each(|stmt| match stmt {
		Stmt::VarDef { .. } | Stmt::VarDefs(_, _) => count += 1,
		// FIXME: Add spans to statements.
		_ => errors.push(SyntaxErr::ExpectedVarDefInStructBody(Span::empty())),
	});
	// Check that there is at least one variable definition within the body.
	if count == 0 {
		let r_brace_span = walker.get_previous_span();
		errors.push(SyntaxErr::ExpectedAtLeastOneMemberInStruct(Span::new(
			l_brace_span.start,
			r_brace_span.end,
		)));
	}

	// Look for an optional instance identifier.
	let instance = match expr_parser(walker, Mode::TakeOneUnit, &[Token::Semi])
	{
		(Some(e), _) => match e.ty {
			ExprTy::Ident(i) => Some(i),
			_ => {
				// Even though we are missing a necessary token to make the syntax valid, it still makes sense to
				// just treat this as a "valid" struct declaration for analysis/goto/etc purposes. We do produce an
				// error though about the missing token.
				errors.push(SyntaxErr::ExpectedSemiAfterStructBody(
					walker.get_previous_span().end_zero_width(),
				));
				return (
					Some(Stmt::StructDecl {
						ident,
						members,
						qualifiers,
						instance: None,
					}),
					errors,
				);
			}
		},
		(None, _) => None,
	};

	// Consume the `;` to end the declaration.
	let (current, _) = match walker.peek() {
		Some(t) => t,
		None => {
			// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
			// treat this as a "valid" struct declaration for analysis/goto/etc purposes. We do produce an error
			// though about the missing token.
			errors.push(SyntaxErr::ExpectedSemiAfterStructBody(
				walker.get_previous_span().end_zero_width(),
			));
			return (
				Some(Stmt::StructDecl {
					ident,
					members,
					qualifiers,
					instance,
				}),
				errors,
			);
		}
	};
	if *current == Token::Semi {
		walker.advance();
		(
			Some(Stmt::StructDecl {
				ident,
				members,
				qualifiers,
				instance,
			}),
			errors,
		)
	} else {
		// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
		// treat this as a "valid" struct declaration for analysis/goto/etc purposes. We do produce an error though
		// about the missing token.
		errors.push(SyntaxErr::ExpectedSemiAfterStructBody(
			walker.get_previous_span().end_zero_width(),
		));
		(
			Some(Stmt::StructDecl {
				ident,
				members,
				qualifiers,
				instance,
			}),
			errors,
		)
	}
}

pub fn print_stmt(stmt: &Stmt, indent: usize) {
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
		Stmt::Scope(v) => {
			print!("\r\n{:indent$}{{", "", indent = indent * 4);
			for stmt in v {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
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
        assert_eq!(parse($src).0, vec![
            $(
                $stmt,
            )*
        ])
    };
}
/*
#[cfg(test)]
use crate::ast::{Fundamental, Lit, Primitive};

#[test]
#[rustfmt::skip]
fn var_def_decl() {
	use crate::ast::{Storage, Layout, Interpolation, Memory};

	// Variable definitions.
	assert_stmt!("int i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
		ident: Ident("i".into()),
		qualifiers: vec![]
	});
	assert_stmt!("bool[2] b;", Stmt::VarDef {
		type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(ExprTy::Lit(Lit::Int(2)))),
		ident: Ident("b".into()),
		qualifiers: vec![]
	});
	assert_stmt!("mat4 m[2][6];", Stmt::VarDef {
		type_: Type::Array2D(Primitive::Matrix(4, 4), Some(ExprTy::Lit(Lit::Int(2))), Some(ExprTy::Lit(Lit::Int(6)))),
		ident: Ident("m".into()),
		qualifiers: vec![]
	});
	assert_stmt!("double[6] d[2];", Stmt::VarDef {
		type_: Type::Array2D(
			Primitive::Scalar(Fundamental::Double),
			Some(ExprTy::Lit(Lit::Int(2))),
			Some(ExprTy::Lit(Lit::Int(6)))
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
				Some(ExprTy::Lit(Lit::Int(1))),
				Some(ExprTy::Lit(Lit::Int(7))),
				Some(ExprTy::Lit(Lit::Int(9))),
				]),
			Ident("a".into())
		),
		(
			Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
				Some(ExprTy::Lit(Lit::Int(3))),
				Some(ExprTy::Lit(Lit::Int(7))),
				Some(ExprTy::Lit(Lit::Int(9))),
				]),
			Ident("b".into())
		)
	], vec![]));

	// Variable declarations.
	assert_stmt!("uint u = 5;", Stmt::VarDecl {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Uint)),
		ident: Ident("u".into()),
		value: ExprTy::Lit(Lit::Int(5)),
		qualifiers: vec![]
	});
	assert_stmt!("int[3] a[1] = {{4, 5, 6}};", Stmt::VarDecl {
		type_: Type::Array2D(
			Primitive::Scalar(Fundamental::Int),
			Some(ExprTy::Lit(Lit::Int(1))),
			Some(ExprTy::Lit(Lit::Int(3)))
		),
		ident: Ident("a".into()),
		value: ExprTy::Init(vec![ExprTy::Init(vec![
			ExprTy::Lit(Lit::Int(4)),
			ExprTy::Lit(Lit::Int(5)),
			ExprTy::Lit(Lit::Int(6))
		])]),
		qualifiers: vec![]
	});
	assert_stmt!("double[] d = {1.0LF, 2.0LF};", Stmt::VarDecl {
		type_: Type::Array(Primitive::Scalar(Fundamental::Double), None),
		ident: Ident("d".into()),
		value: ExprTy::Init(vec![
			ExprTy::Lit(Lit::Double(1.0)),
			ExprTy::Lit(Lit::Double(2.0))
		]),
		qualifiers: vec![]
	});
	assert_stmt!("vec2 a, b = vec2(1, 2);", Stmt::VarDecls {
		vars: vec![
			(Type::Basic(Primitive::Vector(Fundamental::Float, 2)), Ident("a".into())),
			(Type::Basic(Primitive::Vector(Fundamental::Float, 2)), Ident("b".into())),
		],
		value: ExprTy::Fn {
			ident: Ident("vec2".into()),
			args: vec![
				ExprTy::Lit(Lit::Int(1)),
				ExprTy::Lit(Lit::Int(2)),
			]
		},
		qualifiers: vec![]
	});
	assert_stmt!("float[2] a, b = float[](5, 6);", Stmt::VarDecls {
		vars: vec![
			(Type::Array(Primitive::Scalar(Fundamental::Float), Some(ExprTy::Lit(Lit::Int(2)))), Ident("a".into())),
			(Type::Array(Primitive::Scalar(Fundamental::Float), Some(ExprTy::Lit(Lit::Int(2)))), Ident("b".into()))
		],
		value: ExprTy::ArrInit {
			arr: Box::from(ExprTy::Index {
				item: Box::from(ExprTy::Ident(Ident("float".into()))),
				i: None
			}),
			args: vec![
				ExprTy::Lit(Lit::Int(5)),
				ExprTy::Lit(Lit::Int(6))
			]
		},
		qualifiers: vec![]
	});

	// With qualifiers.
	assert_stmt!("const int i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
		ident: Ident("i".into()),
		qualifiers: vec![
			Qualifier::Storage(Storage::Const)
		]
	});
	assert_stmt!("highp float i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Float)),
		ident: Ident("i".into()),
		qualifiers: vec![
			Qualifier::Precision
		]
	});
	assert_stmt!("layout(location = 0) in int i;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
		ident: Ident("i".into()),
		qualifiers: vec![
			Qualifier::Layout(vec![Layout::Location(ExprTy::Lit(Lit::Int(0)))]),
			Qualifier::Storage(Storage::In)
		]
	});
	assert_stmt!("flat uniform vec3 v;", Stmt::VarDef {
		type_: Type::Basic(Primitive::Vector(Fundamental::Float, 3)),
		ident: Ident("v".into()),
		qualifiers: vec![
			Qualifier::Interpolation(Interpolation::Flat),
			Qualifier::Storage(Storage::Uniform)
		]
	});
	assert_stmt!("readonly mat4[1] m;", Stmt::VarDef {
		type_: Type::Array(Primitive::Matrix(4, 4), Some(ExprTy::Lit(Lit::Int(1)))),
		ident: Ident("m".into()),
		qualifiers: vec![
			Qualifier::Memory(Memory::Readonly)
		]
	});
}

#[test]
#[rustfmt::skip]
fn struct_def_decl() {
	use crate::ast::Memory;

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
			type_: Type::Array(Primitive::Scalar(Fundamental::Bool), Some(ExprTy::Lit(Lit::Int(2)))),
			ident: Ident("b".into()),
			qualifiers: vec![]
		}],
		qualifiers: vec![],
		instance: None,
	});
	assert_stmt!("struct S { mat4 m[2][6]; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![Stmt::VarDef {
			type_: Type::Array2D(Primitive::Matrix(4, 4), Some(ExprTy::Lit(Lit::Int(2))), Some(ExprTy::Lit(Lit::Int(6)))),
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
					Some(ExprTy::Lit(Lit::Int(1))),
					Some(ExprTy::Lit(Lit::Int(7))),
					Some(ExprTy::Lit(Lit::Int(9))),
					]),
				Ident("a".into())
			),
			(
				Type::ArrayND(Primitive::Vector(Fundamental::Float, 3), vec![
					Some(ExprTy::Lit(Lit::Int(3))),
					Some(ExprTy::Lit(Lit::Int(7))),
					Some(ExprTy::Lit(Lit::Int(9))),
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
					Some(ExprTy::Lit(Lit::Int(2))),
					Some(ExprTy::Lit(Lit::Int(1)))
				),
				ident: Ident("d".into()),
				qualifiers: vec![]
			}
		],
		qualifiers: vec![],
		instance: None,
	});

	// Struct with member with qualifiers.
	assert_stmt!("struct S { precise writeonly int i; };", Stmt::StructDecl {
		ident: Ident("S".into()),
		members: vec![
			Stmt::VarDef {
				type_: Type::Basic(Primitive::Scalar(Fundamental::Int)),
				ident: Ident("i".into()),
				qualifiers: vec![
					Qualifier::Precise,
					Qualifier::Memory(Memory::Writeonly)
				]
			}
		],
		qualifiers: vec![],
		instance: None,
	});
}
*/
