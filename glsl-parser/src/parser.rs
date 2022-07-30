use crate::{
	ast::{Expr, ExprTy, Ident, Param, Qualifier, Scope, Stmt, StmtTy, Type},
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

	while walker.peek().is_some() {
		match parse_statement_within_fn(&mut walker) {
			Ok((stmt, mut errs)) => {
				errors.append(&mut errs);
				if let Some(stmt) = stmt {
					// Check for the validity of the statement at the top-level.
					match stmt.ty {
						StmtTy::Expr { .. } => errors.push(
							SyntaxErr::ExprStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::Scope { .. } => errors.push(
							SyntaxErr::ScopeStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::If { .. } => errors.push(
							SyntaxErr::IfStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::Switch { .. } => errors.push(
							SyntaxErr::SwitchStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::For { .. } => errors.push(
							SyntaxErr::ForStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::While { .. } => errors.push(
							SyntaxErr::WhileStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::DoWhile { .. } => errors.push(
							SyntaxErr::DoWhileStmtIsIllegalAtTopLevel(
								stmt.span,
							),
						),
						StmtTy::Return { .. } => errors.push(
							SyntaxErr::ReturnStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::Break { .. } => errors.push(
							SyntaxErr::BreakStmtIsIllegalAtTopLevel(stmt.span),
						),
						StmtTy::Continue { .. } => errors.push(
							SyntaxErr::ContinueStmtIsIllegalAtTopLevel(
								stmt.span,
							),
						),
						StmtTy::Discard { .. } => errors.push(
							SyntaxErr::DiscardStmtIsIllegalAtTopLevel(
								stmt.span,
							),
						),
						_ => {}
					}
					stmts.push(stmt);
				}
			}
			Err(mut errs) => {
				errors.append(&mut errs);
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
			Token::Const => qualifiers.push(Qualifier::Storage {
				ty: Storage::Const,
				span: *current_span,
			}),
			Token::In => qualifiers.push(Qualifier::Storage {
				ty: Storage::In,
				span: *current_span,
			}),
			Token::Out => qualifiers.push(Qualifier::Storage {
				ty: Storage::Out,
				span: *current_span,
			}),
			Token::InOut => qualifiers.push(Qualifier::Storage {
				ty: Storage::InOut,
				span: *current_span,
			}),
			Token::Attribute => qualifiers.push(Qualifier::Storage {
				ty: Storage::Attribute,
				span: *current_span,
			}),
			Token::Uniform => qualifiers.push(Qualifier::Storage {
				ty: Storage::Uniform,
				span: *current_span,
			}),
			Token::Varying => qualifiers.push(Qualifier::Storage {
				ty: Storage::Varying,
				span: *current_span,
			}),
			Token::Buffer => qualifiers.push(Qualifier::Storage {
				ty: Storage::Buffer,
				span: *current_span,
			}),
			Token::Shared => qualifiers.push(Qualifier::Storage {
				ty: Storage::Shared,
				span: *current_span,
			}),
			Token::Centroid => qualifiers.push(Qualifier::Storage {
				ty: Storage::Centroid,
				span: *current_span,
			}),
			Token::Sample => qualifiers.push(Qualifier::Storage {
				ty: Storage::Sample,
				span: *current_span,
			}),
			Token::Patch => qualifiers.push(Qualifier::Storage {
				ty: Storage::Patch,
				span: *current_span,
			}),
			Token::Flat => qualifiers.push(Qualifier::Interpolation {
				ty: Interpolation::Flat,
				span: *current_span,
			}),
			Token::Smooth => qualifiers.push(Qualifier::Interpolation {
				ty: Interpolation::Smooth,
				span: *current_span,
			}),
			Token::NoPerspective => qualifiers.push(Qualifier::Interpolation {
				ty: Interpolation::NoPerspective,
				span: *current_span,
			}),
			Token::HighP => qualifiers.push(Qualifier::Precision {
				span: *current_span,
			}),
			Token::MediumP => qualifiers.push(Qualifier::Precision {
				span: *current_span,
			}),
			Token::LowP => qualifiers.push(Qualifier::Precision {
				span: *current_span,
			}),
			Token::Invariant => qualifiers.push(Qualifier::Precision {
				span: *current_span,
			}),
			Token::Precise => qualifiers.push(Qualifier::Precise {
				span: *current_span,
			}),
			Token::Coherent => qualifiers.push(Qualifier::Memory {
				ty: Memory::Coherent,
				span: *current_span,
			}),
			Token::Volatile => qualifiers.push(Qualifier::Memory {
				ty: Memory::Volatile,
				span: *current_span,
			}),

			Token::Restrict => qualifiers.push(Qualifier::Memory {
				ty: Memory::Restrict,
				span: *current_span,
			}),

			Token::Readonly => qualifiers.push(Qualifier::Memory {
				ty: Memory::Readonly,
				span: *current_span,
			}),

			Token::Writeonly => qualifiers.push(Qualifier::Memory {
				ty: Memory::Writeonly,
				span: *current_span,
			}),

			Token::Layout => {
				let kw_span = *current_span;
				walker.advance();

				// Consume the opening `(` parenthesis.
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterLayout(
							kw_span.next_single_width(),
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
						kw_span.next_single_width(),
					));
					break 'outer;
				};

				let mut layouts = Vec::new();
				let mut commas = Vec::new();
				let r_paren_span;
				// Consume layout identifiers until we reach the closing `)` parenthesis.
				'identifiers: loop {
					let (current, current_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// Since we are still in this loop, that means we haven't found the closing `)`
							// parenthesis yet, but we've now reached the end of the token stream.
							errors.push(SyntaxErr::ExpectedParenAtEndOfLayout(
								l_paren_span,
								walker.get_last_span().next_single_width(),
							));
							break 'outer;
						}
					};

					match current {
						// Consume the `,` separator and continue looking for a layout identifier.
						Token::Comma => {
							commas.push(*current_span);
							walker.advance();
							continue 'identifiers;
						}
						// Consume the closing `)` parenthesis and stop parsing this `layout`. We don't consume the
						// token because we perform that at the end of the 'outer loop.
						Token::RParen => {
							r_paren_span = Some(*current_span);
							break 'identifiers;
						}
						Token::Semi => break 'outer,
						_ => {}
					}

					let ident_span = *current_span;
					// We are expecting a token which is a valid layout identifier.
					match current.to_layout() {
						Some(e) => {
							let ident_token = current.clone();
							walker.advance();

							match e {
								Either::Left(layout) => {
									layouts.push((layout, ident_span));
								}
								Either::Right(_) => {
									// Consume the `=` in `ident = expression`.
									let (current, current_span) =
										match walker.peek() {
											Some(t) => t,
											None => {
												errors.push(SyntaxErr::ExpectedEqAfterLayoutIdent(
													walker.get_last_span().next_single_width()
												));
												break 'outer;
											}
										};
									let eq_span;
									if *current == Token::Op(OpTy::Eq) {
										eq_span = *current_span;
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
												ident_span.next_single_width()
											));
											break 'outer;
										}
									};
									let layout_end = expr.span.end;
									layouts.push((
										ident_token.to_layout_expr(
											kw_span, eq_span, expr,
										),
										Span::new(ident_span.start, layout_end),
									));
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
				};

				qualifiers.push(Qualifier::Layout {
					kw: kw_span,
					l_paren: l_paren_span,
					idents: layouts,
					commas,
					r_paren: r_paren_span,
					span: Span::new(kw_span.start, walker.get_previous_span().end)
				});
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
	original_expr: Expr,
	qualifiers: Vec<Qualifier>,
) -> (Option<Stmt>, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	// Check whether we have a function definition/declaration.
	match walker.peek() {
		Some((current, current_span)) => match current {
			Token::Ident(i) => match walker.lookahead_1() {
				Some((next, next_span)) => match next {
					Token::LParen => {
						// We have `TYPE IDENT (` which makes this a function.
						let ident = Ident {
							name: i.clone(),
							span: *current_span,
						};
						let l_paren_span = *next_span;
						walker.advance();
						walker.advance();
						return parse_fn(
							walker,
							type_,
							original_expr.span,
							ident,
							qualifiers,
							l_paren_span,
						);
					}
					_ => {}
				},
				None => {}
			},
			_ => {}
		},
		None => {
			// We have something like `int` which on its own is not a valid statement.
			errors.push(SyntaxErr::ExpectedStmtFoundExpr(original_expr.span));
			return (None, errors);
		}
	};

	// Look for an identifier (or multiple).
	let expr = match expr_parser(walker, Mode::BreakAtEq, &[Token::Semi]) {
		(Some(e), _) => e,
		(None, _) => {
			let (current, current_span) = match walker.peek() {
				Some(t) => t,
				None => {
					// We have something like `int` which on its own is not a valid statement.
					errors.push(SyntaxErr::ExpectedStmtFoundExpr(
						original_expr.span,
					));
					return (None, errors);
				}
			};

			match current {
				Token::Semi => {
					// We have something like `int;` which on its own can be a valid expression statement.
					return (
						Some(Stmt {
							ty: StmtTy::Expr {
								expr: original_expr.clone(),
								semi: Some(*current_span),
							},
							span: Span::new(
								original_expr.span.start,
								current_span.end,
							),
						}),
						errors,
					);
				}
				_ => {
					errors.push(SyntaxErr::ExpectedIdentsAfterVarType(
						*current_span,
					));
					return (None, errors);
				}
			}
		}
	};
	let idents = expr.to_var_def_decl_or_fn_ident();
	if idents.is_empty() {
		errors.push(SyntaxErr::ExpectedIdentsAfterVarType(
			walker.get_previous_span().next_single_width(),
		));
		return (None, errors);
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

	// Consume either the `;` for a variable definition, or a `=` for a variable declaration.
	let (current, current_span) = match walker.peek() {
		Some(t) => (&t.0, t.1),
		None => {
			// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
			// treat this as a "valid" variable definition(s) for analysis/goto/etc purposes. We do produce an
			// error though about the missing token.
			errors.push(SyntaxErr::ExpectedSemiOrEqAfterVarDef(
				walker.get_last_span().next_single_width(),
			));
			return (
				Some(match typenames.len() {
					1 => {
						let (type_, ident) = typenames.remove(0);
						Stmt {
							ty: StmtTy::VarDef {
								type_,
								ident,
								qualifiers,
							},
							span: Span::new(
								original_expr.span.start,
								walker.get_last_span().end,
							),
						}
					}
					_ => Stmt {
						ty: StmtTy::VarDefs(typenames, qualifiers),
						span: Span::new(
							original_expr.span.start,
							walker.get_last_span().end,
						),
					},
				}),
				errors,
			);
		}
	};
	if *current == Token::Semi {
		// We have a variable definition.
		walker.advance();
		(
			Some(match typenames.len() {
				1 => {
					let (type_, ident) = typenames.remove(0);
					Stmt {
						ty: StmtTy::VarDef {
							type_,
							ident,
							qualifiers,
						},
						span: Span::new(
							original_expr.span.start,
							current_span.end,
						),
					}
				}
				_ => Stmt {
					ty: StmtTy::VarDefs(typenames, qualifiers),
					span: Span::new(original_expr.span.start, current_span.end),
				},
			}),
			errors,
		)
	} else if *current == Token::Op(OpTy::Eq) {
		// We have a variable declaration.
		walker.advance();

		// Look for a value.
		let value = match expr_parser(walker, Mode::Default, &[Token::Semi]) {
			(Some(e), _) => e,
			(None, _) => {
				// Even though we are missing a necessary expression to make the syntax valid, it still makes sense
				// to just treat this as a "valid" variable definition(s) for analysis/goto/etc purposes. We do
				// produce an error though about the missing token.
				errors.push(SyntaxErr::ExpectedExprAfterVarDeclEq(
					walker.get_previous_span().next_single_width(),
				));
				return (
					Some(match typenames.len() {
						1 => {
							let (type_, ident) = typenames.remove(0);
							Stmt {
								ty: StmtTy::VarDef {
									type_,
									ident,
									qualifiers,
								},
								span: Span::new(
									original_expr.span.start,
									walker.get_last_span().end,
								),
							}
						}
						_ => Stmt {
							ty: StmtTy::VarDefs(typenames, qualifiers),
							span: Span::new(
								original_expr.span.start,
								walker.get_last_span().end,
							),
						},
					}),
					errors,
				);
			}
		};

		// Consume the `;` to end the declaration.
		let (current, current_span) = match walker.peek() {
			Some(t) => (&t.0, t.1),
			None => {
				// Even though we are missing a necessary token to make the syntax valid, it still makes sense to
				// just treat this as a "valid" variable declaration(s) for analysis/goto/etc purposes. We do
				// produce an error though about the missing token.
				errors.push(SyntaxErr::ExpectedSemiAfterVarDeclExpr(
					walker.get_previous_span().next_single_width(),
				));
				return (
					Some(match typenames.len() {
						1 => {
							let (type_, ident) = typenames.remove(0);
							Stmt {
								ty: StmtTy::VarDecl {
									type_,
									ident,
									value,
									qualifiers,
								},
								span: Span::new(
									original_expr.span.start,
									walker.get_last_span().end,
								),
							}
						}
						_ => Stmt {
							ty: StmtTy::VarDecls {
								vars: typenames,
								value,
								qualifiers,
							},
							span: Span::new(
								original_expr.span.start,
								walker.get_last_span().end,
							),
						},
					}),
					errors,
				);
			}
		};
		if *current == Token::Semi {
			walker.advance();
		} else {
			// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
			// treat this as a "valid" variable declaration(s) for analysis/goto/etc purposes. We do produce an
			// error though about the missing token.
			errors.push(SyntaxErr::ExpectedSemiAfterVarDeclExpr(
				walker.get_previous_span().next_single_width(),
			));
			return (
				Some(match typenames.len() {
					1 => {
						let (type_, ident) = typenames.remove(0);
						Stmt {
							ty: StmtTy::VarDecl {
								type_,
								ident,
								value,
								qualifiers,
							},
							span: Span::new(
								original_expr.span.start,
								walker.get_previous_span().end,
							),
						}
					}
					_ => Stmt {
						ty: StmtTy::VarDecls {
							vars: typenames,
							value,
							qualifiers,
						},
						span: Span::new(
							original_expr.span.start,
							walker.get_previous_span().end,
						),
					},
				}),
				errors,
			);
		}

		(
			Some(match typenames.len() {
				1 => {
					let (type_, ident) = typenames.remove(0);
					Stmt {
						ty: StmtTy::VarDecl {
							type_,
							ident,
							value,
							qualifiers,
						},
						span: Span::new(
							original_expr.span.start,
							current_span.end,
						),
					}
				}
				_ => Stmt {
					ty: StmtTy::VarDecls {
						vars: typenames,
						value,
						qualifiers,
					},
					span: Span::new(original_expr.span.start, current_span.end),
				},
			}),
			errors,
		)
	} else {
		// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
		// treat this as a "valid" variable definition(s) for analysis/goto/etc purposes. We do produce an error
		// though about the missing token.
		errors.push(SyntaxErr::ExpectedSemiOrEqAfterVarDef(
			walker.get_previous_span().next_single_width(),
		));
		(
			Some(match typenames.len() {
				1 => {
					let (type_, ident) = typenames.remove(0);
					Stmt {
						ty: StmtTy::VarDef {
							type_,
							ident,
							qualifiers,
						},
						span: Span::new(
							original_expr.span.start,
							walker.get_previous_span().end,
						),
					}
				}
				_ => Stmt {
					ty: StmtTy::VarDefs(typenames, qualifiers),
					span: Span::new(
						original_expr.span.start,
						walker.get_previous_span().end,
					),
				},
			}),
			errors,
		)
	}
}

/// Parse a function definition or declaration.
fn parse_fn(
	walker: &mut Walker,
	return_type: Type,
	start_span: Span,
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
					walker.get_last_span().next_single_width(),
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
					Some(Stmt {
						ty: StmtTy::FnDef {
							return_type,
							ident,
							params,
							qualifiers,
							semi: Some(current_span),
						},
						span: Span::new(start_span.start, current_span.end),
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
						params.push(Param {
							qualifiers,
							type_,
							ident: None,
						});

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

		params.push(Param {
			qualifiers,
			type_,
			ident: Some(ident),
		});
		just_finished_param = true;
	}

	// Consume either the `;` for a function definition, or a `{` for a function declaration.
	let (current, current_span) = match walker.peek() {
		Some(t) => (&t.0, t.1),
		None => {
			// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
			// treat this as a "valid" function definition for analysis/goto/etc purposes. We do produce an error
			// though about the missing token.
			errors.push(SyntaxErr::ExpectedSemiOrScopeAfterParamList(
				walker.get_last_span().next_single_width(),
			));
			return (
				Some(Stmt {
					ty: StmtTy::FnDef {
						return_type,
						ident,
						params,
						qualifiers,
						semi: None,
					},
					span: Span::new(
						start_span.start,
						walker.get_last_span().end,
					),
				}),
				errors,
			);
		}
	};
	if *current == Token::Semi {
		walker.advance();
		(
			Some(Stmt {
				ty: StmtTy::FnDef {
					qualifiers,
					return_type,
					ident,
					params,
					semi: Some(current_span),
				},
				span: Span::new(start_span.start, current_span.end),
			}),
			errors,
		)
	} else if *current == Token::LBrace {
		walker.advance();

		// Parse the function body, including the closing `}` brace.
		let (body, mut errs) =
			parse_scope(walker, BRACE_DELIMITER, current_span);
		errors.append(&mut errs);

		(
			Some(Stmt {
				span: Span::new(start_span.start, body.span.end),
				ty: StmtTy::FnDecl {
					qualifiers,
					return_type,
					ident,
					params,
					body,
				},
			}),
			errors,
		)
	} else {
		// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
		// treat this as a "valid" function definition for analysis/goto/etc purposes. We do produce an error
		// though about the missing token.
		errors.push(SyntaxErr::ExpectedSemiOrScopeAfterParamList(
			walker.get_previous_span().next_single_width(),
		));
		(
			Some(Stmt {
				ty: StmtTy::FnDef {
					qualifiers,
					return_type,
					ident,
					params,
					semi: None,
				},
				span: Span::new(
					start_span.start,
					walker.get_previous_span().end,
				),
			}),
			errors,
		)
	}
}

/// A function, which given the current `walker`, determines whether to end parsing the current scope of
/// statements, and return back to the caller. If this returns `Some`, we have reached the end of the scope. If the
/// span returned is zero-width, that means we have no closing delimiter.
///
/// This also takes a mutable reference to a vector of syntax errors, and a span of the opening delimiter, which
/// allows for the creation of a syntax error if the function never encounters the desired ending delimiter.
type EndScope = fn(&mut Walker, &mut Vec<SyntaxErr>, Span) -> Option<Span>;

const BRACE_DELIMITER: EndScope = |walker, errors, l_brace_span| {
	let (current, current_span) = match walker.peek() {
		Some((t, s)) => (t, *s),
		None => {
			// We did not encounter a `}` at all.
			errors.push(SyntaxErr::ExpectedBraceScopeEnd(
				l_brace_span,
				walker.get_last_span().next_single_width(),
			));
			return Some(walker.get_last_span().end_zero_width());
		}
	};

	if *current == Token::RBrace {
		walker.advance();
		Some(current_span)
	} else {
		None
	}
};

const SWITCH_CASE_DELIMITER: EndScope = |walker, errors, colon_span| {
	let (current, current_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// We did not encounter one of the closing tokens at all.
			errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
				Some(colon_span),
				walker.get_last_span().next_single_width(),
			));
			return Some(walker.get_last_span().end_zero_width());
		}
	};

	match current {
		Token::RBrace | Token::Case | Token::Default => Some(*current_span),
		_ => None,
	}
};

/// Parse the statements within a scope, up until the scope exit condition is encountered.
///
/// - `exit_condition` - a function which determines the end of the scope; (whether the end delimiter is or is not
///   consumed depends on the [`EndScope`] function passed in),
/// - `opening_delim` - the span of the opening delimiter; (commonly a `{` but may be empty).
fn parse_scope(
	walker: &mut Walker,
	exit_condition: EndScope,
	opening_delim: Span,
) -> (Scope, Vec<SyntaxErr>) {
	let mut stmts = Vec::new();
	let mut errors = Vec::new();

	// Invariant: Cannot `break` out of a while-loop with a value, but this variable is assigned-to in every branch
	// that `break` is called in.
	let mut ending_span = Span::empty();
	let mut closing_delim = None;

	'stmt: while let Some(_) = walker.peek() {
		// If we have reached a closing delimiter, break out of the loop and return the parsed statements.
		if let Some(span) = exit_condition(walker, &mut errors, opening_delim) {
			if !span.is_zero_width() {
				closing_delim = Some(span)
			}
			ending_span = span;
			break 'stmt;
		}

		match parse_statement_within_fn(walker) {
			Ok((stmt, mut errs)) => {
				errors.append(&mut errs);
				if let Some(stmt) = stmt {
					stmts.push(stmt);
				}
			}
			Err(mut errs) => {
				errors.append(&mut errs);
				ending_span = walker.get_last_span().end_zero_width();
				break 'stmt;
			}
		}
	}

	(
		Scope {
			opening: Some(opening_delim),
			stmts,
			closing: closing_delim,
			span: Span::new(opening_delim.start, ending_span.end),
		},
		errors,
	)
}

/// [`Ok`] is returned if the following:
/// - a fully valid statement was found (in which case there will be no syntax errors),
/// - a partially valid statement was found and recovered (in which case there will be some syntax errors),
/// - a partially valid statement was found but could not recover a meaningful AST node (in which case there will
///   be some syntax errors).
///
/// [`Err`] is returned if the following:
/// - the end of the token stream was reached without being able to produce either a fully valid statement or a
///   recovered partially valid statement.
fn parse_statement_within_fn(
	walker: &mut Walker,
) -> Result<(Option<Stmt>, Vec<SyntaxErr>), Vec<SyntaxErr>> {
	let mut errors = Vec::new();

	// Panics: This is guaranteed to unwrap without panic because of the while-loop precondition.
	let (current, current_span) = walker.peek().unwrap();

	// If we immediately encounter an opening `{` brace, that means we have an new inner scope. We need to
	// perform this check before the `expr_parser()` call because that would treat the `{` as the beginning of
	// an initializer list.
	if *current == Token::LBrace {
		let l_brace_span = *current_span;
		walker.advance();

		let (inner_scope, mut inner_errs) =
			parse_scope(walker, BRACE_DELIMITER, l_brace_span);
		errors.append(&mut inner_errs);

		return Ok((
			Some(Stmt {
				span: Span::new(l_brace_span.start, inner_scope.span.end),
				ty: StmtTy::Scope(inner_scope),
			}),
			errors,
		));
	}

	// First, we look for any qualifiers because they are always located first in a statement.
	let (qualifiers, mut errs) = parse_qualifier_list(walker);
	errors.append(&mut errs);

	// Next, we look for any syntax which can be parsed as an expression, e.g. a `int[3]`.
	if let (Some(expr), _) = expr_parser(walker, Mode::Default, &[Token::Semi])
	{
		// We tried to parse an expression and succeeded. We have an expression consisting of at least one
		// token.

		// Check if the expression can be parsed as a typename. If so, then we try to parse the following
		// tokens as statements which can start with a typename, i.e. variable or function defs/decls.
		// FIXME: Cannot have a function within a function?
		return if let Some(type_) = expr.to_type() {
			match parse_type_start(walker, type_, expr, qualifiers) {
				(Some(s), mut errs) => {
					errors.append(&mut errs);
					return Ok((Some(s), errors));
				}
				(None, mut errs) => {
					errors.append(&mut errs);

					'till_next: loop {
						// We did not successfully parse a statement.
						let (next, _) = match walker.peek() {
							Some(t) => t,
							None => return Err(errors),
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
			Ok((None, errors))
		} else {
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => return Err(errors),
			};
			if *current == Token::Semi {
				walker.advance();
				Ok((
					Some(Stmt {
						ty: StmtTy::Expr {
							expr: expr.clone(),
							semi: Some(current_span),
						},
						span: expr.span,
					}),
					errors,
				))
			} else {
				Ok((None, errors))
			}
		};
	}

	// We tried to parse an expression but that immediately failed. This means the current token is one
	// which cannot start an expression.
	let (token, token_span) = walker.peek().map(|t| (&t.0, t.1)).unwrap();

	match token {
		Token::Semi => {
			walker.advance();
			return Ok((
				Some(Stmt {
					ty: StmtTy::Empty,
					span: token_span,
				}),
				errors,
			));
		}
		Token::If => {
			let kw_span = token_span;
			walker.advance();

			// Parse the first `if ...` branch.
			let (l_paren_span, cond, r_paren_span, body, mut errs) =
				match parse_if(walker, token_span, true) {
					Ok((l, expr, r, body, errs)) => {
						let expr = match expr {
							Some(e) => e,
							None => return Ok((None, errors)),
						};
						(l, expr, r, body, errs)
					}
					Err(mut errs) => {
						errors.append(&mut errs);
						return Ok((None, errors));
					}
				};
			errors.append(&mut errs);

			let mut branches = Vec::new();
			'branches: loop {
				let (token, token_span) = match walker.peek() {
					Some(t) => (&t.0, t.1),
					None => {
						return Ok((
							Some(Stmt {
								ty: StmtTy::If {
									kw: kw_span,
									l_paren: l_paren_span,
									cond,
									r_paren: r_paren_span,
									body,
									branches,
								},
								span: Span::new(
									token_span.start,
									walker.get_last_span().end,
								),
							}),
							errors,
						));
					}
				};

				match token {
					Token::Else => {
						let else_span = token_span;
						walker.advance();

						let (current, current_span) = match walker.peek() {
							Some(t) => (&t.0, t.1),
							None => {
								errors.push(
									SyntaxErr::ExpectedIfOrBodyAfterElseKw(
										walker
											.get_last_span()
											.next_single_width(),
									),
								);
								return Err(errors);
							}
						};

						if *current == Token::If {
							let if_span = current_span;
							// We have `else if`.
							walker.advance();

							let (
								l_paren_span,
								cond,
								r_paren_span,
								body,
								mut errs,
							) = match parse_if(walker, current_span, true) {
								Ok((l, expr, r, body, errs)) => {
									(l, expr, r, body, errs)
								}
								Err(_) => return Ok((None, errors)),
							};
							errors.append(&mut errs);
							branches.push((
								else_span,
								Some(if_span),
								l_paren_span,
								cond,
								r_paren_span,
								body,
							));
						} else {
							// We just have `else`.

							let (
								l_paren_span,
								cond,
								r_paren_span,
								body,
								mut errs,
							) = match parse_if(walker, token_span, false) {
								Ok((l, expr, r, body, errs)) => {
									(l, expr, r, body, errs)
								}
								Err(_) => return Ok((None, errors)),
							};
							errors.append(&mut errs);
							branches.push((
								else_span,
								None,
								l_paren_span,
								cond,
								r_paren_span,
								body,
							));
						}
					}
					_ => break 'branches,
				}
			}

			return Ok((
				Some(Stmt {
					ty: StmtTy::If {
						kw: kw_span,
						l_paren: l_paren_span,
						cond,
						r_paren: r_paren_span,
						body,
						branches,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				}),
				errors,
			));
		}
		Token::Switch => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedParenAfterSwitchKw(
						token_span.next_single_width(),
					));
					return Err(errors);
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				walker.advance();

				// We are completely missing the condition expression, but we treat this as "valid" for
				// better recovery.
				errors.push(SyntaxErr::MissingSwitchHeader(Span::new_between(
					token_span,
					current_span,
				)));

				// Consume the body, including the closing `}` brace.
				let (cases, mut errs) = parse_switch_body(walker, current_span);
				errors.append(&mut errs);

				return Ok((
					Some(Stmt {
						ty: StmtTy::Switch {
							kw: kw_span,
							l_paren: None,
							expr: Expr {
								ty: ExprTy::Missing,
								span: token_span.next_single_width(),
							},
							r_paren: None,
							cases,
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					}),
					errors,
				));
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
					token_span.next_single_width(),
				));
				None
			};

			// Consume the conditional expression.
			let expr =
				match expr_parser(walker, Mode::Default, &[Token::RParen]) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						e
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either a `)` or a `{`.
						let expr = 'expr_4: loop {
							let (current, current_span) =
								match walker.peek() {
									Some(t) => (&t.0, t.1),
									None => {
										errors.push(
											SyntaxErr::ExpectedExprInSwitchHeader(
												walker.get_last_span().next_single_width()
											),
										);
										return Err(errors);
									}
								};

							match current {
								Token::RParen | Token::RBrace => {
									if let Some(l_paren_span) = l_paren_span {
										errors.push(
											SyntaxErr::ExpectedExprInSwitchHeader(
												Span::new_between(l_paren_span, current_span)
											),
										);
									} else {
										errors.push(
											SyntaxErr::ExpectedExprInSwitchHeader(
												current_span.previous_single_width()
											),
										);
									}
									break 'expr_4 Expr {
										ty: ExprTy::Missing,
										span: current_span
											.previous_single_width(),
									};
								}
								_ => continue 'expr_4,
							}
						};

						expr
					}
				};

			// Consume the closing `)` parenthesis. We loop until we hit either a `)` or a `{`. If we
			// have something like `switch (i b - 5)`, we already get an error about the missing binary
			// operator, so no need to further produce errors; we just silently consume.
			let mut r_paren_span = None;
			let span_after_header = 'r_paren_3: loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterSwitchHeader(
							l_paren_span,
							walker.get_last_span().next_single_width(),
						));
						return Err(errors);
					}
				};

				match current {
					Token::RParen => {
						let current_span = *current_span;
						r_paren_span = Some(current_span);
						walker.advance();
						break 'r_paren_3 current_span;
					}
					Token::LBrace => {
						// We don't do anything apart from creating a syntax error since the next check
						// deals with the `{`.
						errors.push(SyntaxErr::ExpectedParenAfterSwitchHeader(
							l_paren_span,
							current_span.previous_single_width(),
						));
						break 'r_paren_3 current_span.previous_single_width();
					}
					_ => {
						walker.advance();
						continue 'r_paren_3;
					}
				}
			};

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Even though switch statements without a body are illegal, we treat this as
					// "valid" for better recovery.
					errors.push(SyntaxErr::ExpectedBraceAfterSwitchHeader(
						walker.get_last_span().next_single_width(),
					));
					return Ok((
						Some(Stmt {
							ty: StmtTy::Switch {
								kw: kw_span,
								l_paren: l_paren_span,
								expr,
								r_paren: r_paren_span,
								cases: vec![],
							},
							span: Span::new(
								token_span.start,
								walker.get_last_span().end,
							),
						}),
						errors,
					));
				}
			};
			if *current == Token::LBrace {
				walker.advance();
			} else {
				errors.push(SyntaxErr::ExpectedBraceAfterSwitchHeader(
					span_after_header.next_single_width(),
				));
				return Ok((
					Some(Stmt {
						ty: StmtTy::Switch {
							kw: kw_span,
							l_paren: l_paren_span,
							expr,
							r_paren: r_paren_span,
							cases: vec![],
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					}),
					errors,
				));
			}

			// Consume the body, including the closing `}` brace.
			let (cases, mut errs) = parse_switch_body(walker, current_span);
			errors.append(&mut errs);

			return Ok((
				Some(Stmt {
					ty: StmtTy::Switch {
						kw: kw_span,
						l_paren: l_paren_span,
						expr,
						r_paren: r_paren_span,
						cases,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				}),
				errors,
			));
		}
		Token::For => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedParenAfterForKw(
						kw_span.next_single_width(),
					));
					return Err(errors);
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				walker.advance();

				// We are completely missing the header, but we treat this as "valid" for better
				// recovery.
				errors.push(SyntaxErr::MissingForHeader(Span::new_between(
					kw_span,
					current_span,
				)));

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				errors.append(&mut errs);

				return Ok((
					Some(Stmt {
						span: Span::new(kw_span.start, body.span.end),
						ty: StmtTy::For {
							kw: kw_span,
							l_paren: None,
							var: None,
							first_semi: None,
							cond: None,
							second_semi: None,
							inc: None,
							r_paren: None,
							body: Some(body),
						},
					}),
					errors,
				));
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				errors.push(SyntaxErr::ExpectedParenAfterForKw(
					kw_span.next_single_width(),
				));
				None
			};

			let mut just_started = true;
			let mut count = 0;
			let mut just_parsed_semi = false;
			let mut extra_arg_start = 0;
			let mut var = None;
			let mut exprs = vec![None, None];
			let mut semi_spans = Vec::new();
			let mut r_paren_span = None;
			let span_after_header = 'for_header: loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => (&t.0, t.1),
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterForHeader(
							l_paren_span,
							walker.get_last_span().next_single_width(),
						));
						return Err(errors);
					}
				};

				match current {
					Token::Semi => {
						count += 1;
						// We have just parsed the 3rd expression and we've come across a `;`, which is
						// unnecessary.
						if count == 3 {
							errors.push(
								SyntaxErr::FoundTrailingSemiAfter3rdExprInFor(
									current_span,
								),
							);
							extra_arg_start = current_span.end;
						}
						semi_spans.push(current_span);
						just_parsed_semi = true;
						walker.advance();
					}
					Token::RParen if just_started => {
						// We just had the `(`, which means this is an empty header.
						errors.push(SyntaxErr::FoundEmptyForHeader(
							if let Some(l_paren_span) = l_paren_span {
								Span::new_between(l_paren_span, current_span)
							} else {
								current_span.previous_single_width()
							},
						));
						walker.advance();
						r_paren_span = Some(current_span);
						break 'for_header current_span;
					}
					Token::RParen if !just_started => {
						// Whether it's `some - expr)` or it's `expr; )`, we want to increase the
						// argument count in both scenarios.
						count += 1;

						if count < 3 {
							errors.push(SyntaxErr::Expected3StmtExprInFor(
								if let Some(l_paren_span) = l_paren_span {
									Span::new_between(
										l_paren_span,
										current_span,
									)
								} else {
									current_span.previous_single_width()
								},
							));
						} else if count >= 4 {
							errors.push(
								SyntaxErr::FoundMoreThan3StmtExprInFor(
									Span::new_between(
										Span::new_zero_width(extra_arg_start),
										current_span,
									),
								),
							);
						}

						walker.advance();
						r_paren_span = Some(current_span);
						break 'for_header current_span;
					}
					Token::LBrace => {
						// Even though we are missing the `)` token, we still treat this as a "valid"
						// for loop for better error recovery. We don't consume because the next check
						// deals with `{`.
						errors.push(SyntaxErr::ExpectedParenAfterForHeader(
							l_paren_span,
							current_span.previous_single_width(),
						));
						break 'for_header current_span;
					}
					_ => {
						// We just finished parsing a stmt/expr and we are expecting a semi-colon, but
						// we found something else instead.
						if !just_parsed_semi && !just_started {
							errors.push(
								SyntaxErr::ExpectedSemiAfterForStmtExpr(
									walker
										.get_previous_span()
										.next_single_width(),
								),
							);
						}
					}
				}

				just_started = false;

				match expr_parser(
					walker,
					Mode::Default,
					&[Token::Semi, Token::RParen],
				) {
					(Some(expr), mut errs) => {
						if count == 0 {
							// We are looking for the variable statement or expression.
							if let Some(type_) = expr.to_type() {
								let walker_cursor = walker.cursor;
								match parse_type_start(
									walker,
									type_,
									expr.clone(),
									vec![],
								) {
									(Some(s), mut errs) => {
										errors.append(&mut errs);
										var = Some(s);
										// The `parse_type_start()` consumes the `;`, so we have to
										// manually increment the count.
										count += 1;
										just_parsed_semi = true;
									}
									(None, _) => {
										walker.cursor = walker_cursor;
										errors.append(&mut errs);
										var = Some(Stmt {
											ty: StmtTy::Expr {
												expr: expr.clone(),
												semi: None,
											},
											span: expr.span,
										});
									}
								}
							} else {
								var = Some(Stmt {
									ty: StmtTy::Expr {
										expr: expr.clone(),
										semi: None,
									},
									span: expr.span,
								});
							}
						} else if count == 1 {
							errors.append(&mut errs);
							exprs[0] = Some(expr);
						} else if count == 2 {
							errors.append(&mut errs);
							exprs[1] = Some(expr);
						} else {
							errors.append(&mut errs);
							exprs.push(Some(expr));
						}
					}
					(None, _) => {
						// Look for a `;` or `)` or `{` that follows immediately from the last. We let
						// the next loop iteration deal with that.
						let (current, _) = match walker.peek() {
							Some(t) => (&t.0, t.1),
							None => {
								errors.push(
									SyntaxErr::ExpectedParenAfterForHeader(
										l_paren_span,
										walker
											.get_last_span()
											.next_single_width(),
									),
								);
								return Err(errors);
							}
						};
						match current {
							Token::Semi | Token::RParen | Token::LBrace => {
								continue 'for_header
							}
							_ => {}
						}

						// We have a token which cannot start an expression. We loop until we come
						// across either a `;`, a `)` or a `{`.
						'inner: loop {
							let (current, current_span) =
								match walker.peek() {
									Some(t) => (&t.0, t.1),
									None => {
										errors.push(
												SyntaxErr::ExpectedParenAfterForHeader(
													l_paren_span, walker.get_last_span().next_single_width())
											);
										return Err(errors);
									}
								};

							match current {
								Token::Semi | Token::RParen | Token::LBrace => {
									// We need to work out the last span that's valid.
									let last_expr_span = exprs
										.iter()
										.rev()
										.find(|o| o.is_some())
										.map(|e| e.as_ref().unwrap().span);
									let last_semi_span = semi_spans.last();
									let beginning_span =
										if let (Some(expr), Some(semi)) =
											(last_expr_span, last_semi_span)
										{
											if expr.is_after(semi) {
												expr
											} else {
												*semi
											}
										} else if let Some(l_paren_span) =
											l_paren_span
										{
											l_paren_span
										} else {
											kw_span
										};
									errors.push(
										SyntaxErr::ExpectedExprInForFoundElse(
											Span::new_between(
												beginning_span,
												current_span,
											),
										),
									);
									break 'inner;
								}
								_ => walker.advance(),
							}
						}
					}
				}
			};

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Even though for loops without a body are illegal, we treat this as "valid" for
					// better error recovery.
					errors.push(SyntaxErr::ExpectedBraceAfterForHeader(
						walker.get_last_span().next_single_width(),
					));
					return Ok((
						Some(Stmt {
							ty: StmtTy::For {
								kw: kw_span,
								l_paren: l_paren_span,
								var: var.map(|s| Box::from(s)),
								first_semi: semi_spans.get(0).cloned(),
								cond: exprs.remove(0),
								second_semi: semi_spans.get(1).cloned(),
								inc: exprs.remove(0),
								r_paren: r_paren_span,
								body: None,
							},
							span: Span::new(
								token_span.start,
								walker.get_last_span().end,
							),
						}),
						errors,
					));
				}
			};
			if *current == Token::LBrace {
				walker.advance();
			} else {
				// Even though for loops without a body are illegal, we treat this as "valid" for
				// better error recovery.
				errors.push(SyntaxErr::ExpectedBraceAfterForHeader(
					span_after_header.next_single_width(),
				));
				return Ok((
					Some(Stmt {
						ty: StmtTy::For {
							kw: kw_span,
							l_paren: l_paren_span,
							var: var.map(|s| Box::from(s)),
							first_semi: semi_spans.get(0).cloned(),
							cond: exprs.remove(0),
							second_semi: semi_spans.get(1).cloned(),
							inc: exprs.remove(0),
							r_paren: r_paren_span,
							body: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					}),
					errors,
				));
			}

			// Consume the body, including the closing `}` brace.
			let (body, mut errs) =
				parse_scope(walker, BRACE_DELIMITER, current_span);
			errors.append(&mut errs);

			return Ok((
				Some(Stmt {
					span: Span::new(token_span.start, body.span.end),
					ty: StmtTy::For {
						kw: kw_span,
						l_paren: l_paren_span,
						var: var.map(|s| Box::from(s)),
						first_semi: semi_spans.get(0).cloned(),
						cond: exprs.remove(0),
						second_semi: semi_spans.get(1).cloned(),
						inc: exprs.remove(0),
						r_paren: r_paren_span,
						body: Some(body),
					},
				}),
				errors,
			));
		}
		Token::While => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
						kw_span.next_single_width(),
					));
					return Err(errors);
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				walker.advance();

				// We are completely missing the condition expression, but we treat this as "valid" for
				// better recovery.
				errors.push(SyntaxErr::ExpectedCondExprAfterWhile(
					Span::new_between(kw_span, current_span),
				));

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				errors.append(&mut errs);

				return Ok((
					Some(Stmt {
						span: Span::new(kw_span.start, body.span.end),
						ty: StmtTy::While {
							kw: kw_span,
							l_paren: None,
							cond: Expr {
								ty: ExprTy::Missing,
								span: kw_span.end_zero_width(),
							},
							r_paren: None,
							body: Some(body),
						},
					}),
					errors,
				));
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
					kw_span.next_single_width(),
				));
				None
			};

			// Consume the conditional expression.
			let cond =
				match expr_parser(walker, Mode::Default, &[Token::RParen]) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						e
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either a `)` or a `{`.
						let expr = 'expr: loop {
							let (current, current_span) =
								match walker.peek() {
									Some(t) => (&t.0, t.1),
									None => {
										errors.push(
											SyntaxErr::ExpectedCondExprAfterWhile(
												walker.get_last_span().next_single_width()
											),
										);
										return Err(errors);
									}
								};

							match current {
								Token::RParen | Token::RBrace => {
									if let Some(l_paren_span) = l_paren_span {
										errors.push(
													SyntaxErr::ExpectedCondExprAfterWhile(
														Span::new_between(l_paren_span, current_span)
													),
												);
									} else {
										errors.push(
													SyntaxErr::ExpectedCondExprAfterWhile(
														current_span.previous_single_width()
													),
												);
									}
									break 'expr Expr {
										ty: ExprTy::Missing,
										span: current_span
											.previous_single_width(),
									};
								}
								_ => continue 'expr,
							}
						};

						expr
					}
				};

			// Consume the closing `)` parenthesis. We loop until we hit either a `)` or a `{`. If we
			// have something like `while (i b - 5)`, we already get an error about the missing binary
			// operator, so no need to further produce errors; we just silently consume.
			let mut r_paren_span = None;
			let span_before_body = 'r_paren: loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterWhileCond(
							l_paren_span,
							walker.get_last_span().next_single_width(),
						));
						return Err(errors);
					}
				};

				match current {
					Token::RParen => {
						let current_span = *current_span;
						r_paren_span = Some(current_span);
						walker.advance();
						break 'r_paren current_span;
					}
					Token::LBrace => {
						// We don't do anything apart from creating a syntax error since the next check
						// deals with the `{`.
						errors.push(SyntaxErr::ExpectedParenAfterWhileCond(
							l_paren_span,
							current_span.previous_single_width(),
						));
						break 'r_paren current_span.start_zero_width();
					}
					_ => {
						walker.advance();
						continue 'r_paren;
					}
				}
			};

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Even though while loops without a body are illegal, we treat this as "valid" for
					// better recovery.
					errors.push(SyntaxErr::ExpectedScopeAfterControlFlowExpr(
						walker.get_last_span().next_single_width(),
					));
					return Ok((
						Some(Stmt {
							ty: StmtTy::While {
								kw: token_span,
								l_paren: l_paren_span,
								cond,
								r_paren: r_paren_span,
								body: None,
							},
							span: Span::new(
								token_span.start,
								walker.get_last_span().end,
							),
						}),
						errors,
					));
				}
			};
			if *current == Token::LBrace {
				walker.advance();
			} else {
				errors.push(SyntaxErr::ExpectedScopeAfterControlFlowExpr(
					span_before_body.next_single_width(),
				));
				return Ok((
					Some(Stmt {
						ty: StmtTy::While {
							kw: token_span,
							l_paren: l_paren_span,
							cond,
							r_paren: r_paren_span,
							body: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					}),
					errors,
				));
			}

			// Consume the body, including the closing `}` brace.
			let (body, mut errs) =
				parse_scope(walker, BRACE_DELIMITER, current_span);
			errors.append(&mut errs);

			return Ok((
				Some(Stmt {
					ty: StmtTy::While {
						kw: token_span,
						l_paren: l_paren_span,
						cond,
						r_paren: r_paren_span,
						body: Some(body),
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				}),
				errors,
			));
		}
		Token::Do => {
			let do_kw_span = token_span;
			walker.advance();

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedBraceAfterDoKw(
						token_span.next_single_width(),
					));
					return Err(errors);
				}
			};
			let (body, span_after_body) = if *current == Token::LBrace {
				walker.advance();

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				errors.append(&mut errs);

				(Some(body.clone()), body.span.end_zero_width())
			} else if *current == Token::While {
				// We are completely missing the body, but we treat this as "valid" for better error
				// recovery; we still try to parse the condition. We do nothing because the next check
				// deals with the `while` keyword.
				errors.push(SyntaxErr::ExpectedScopeAfterDoKw(
					token_span.next_single_width(),
				));
				(None, do_kw_span.end_zero_width())
			} else {
				errors.push(SyntaxErr::ExpectedBraceAfterDoKw(
					token_span.next_single_width(),
				));
				return Ok((None, errors));
			};

			// Consume the `while` keyword.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						walker.get_last_span(),
					));
					return Err(errors);
				}
			};
			let while_kw_span = if *current == Token::While {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LParen {
				// Even though we are missing the `while` token, we will still try to parse this syntax
				// as the condition expression. We don't do anything else since the next check deals
				// with the `(`.

				// Since the position of a missing body and a missing `while` keyword can potentially
				// overlap if both are missing, we avoid this error if we already have the first.
				if let Some(_) = body {
					errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						span_after_body.next_single_width(),
					));
				}
				None
			} else {
				// Since the position of a missing body and a missing `while` keyword can potentially
				// overlap if both are missing, we avoid this error if we already have the first.
				if let Some(_) = body {
					errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						span_after_body.next_single_width(),
					));
				}
				return Ok((None, errors));
			};

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Since the position of a missing `while` keyword and a missing `(` token can
					// potentially overlap if both are missing, we avoid this error if we already have
					// the first error.
					if let Some(while_kw_span) = while_kw_span {
						errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
							while_kw_span.next_single_width(),
						));
					}
					return Err(errors);
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::Semi {
				walker.advance();

				// Since the position of a missing `while` keyword and a missing `(` token can
				// potentially overlap if both are missing, we avoid this error if we already have the
				// first error.
				if let Some(while_kw_span) = while_kw_span {
					errors.push(SyntaxErr::ExpectedCondExprAfterWhile(
						Span::new_between(while_kw_span, current_span),
					));
				}

				return Ok((
					Some(Stmt {
						ty: StmtTy::DoWhile {
							do_kw: do_kw_span,
							body,
							while_kw: while_kw_span,
							l_paren: None,
							cond: Expr {
								ty: ExprTy::Missing,
								span: current_span.start_zero_width(),
							},
							r_paren: None,
							semi: Some(current_span),
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					}),
					errors,
				));
			} else {
				// Since the position of a missing `while` keyword and a missing `(` token can
				// potentially overlap if both are missing, we avoid this error if we already have the
				// first error.
				if let Some(while_kw_span) = while_kw_span {
					errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
						while_kw_span.next_single_width(),
					));
				}
				None
			};

			// Consume the conditional expression.
			let cond = match expr_parser(
				walker,
				Mode::Default,
				&[Token::RParen, Token::Semi],
			) {
				(Some(e), mut errs) => {
					errors.append(&mut errs);
					e
				}
				(None, _) => {
					// We found tokens which cannot even start an expression. We loop until we come
					// across either a `)` or a `;`.
					let expr =
						'expr_2: loop {
							let (current, current_span) =
								match walker.peek() {
									Some(t) => (&t.0, t.1),
									None => {
										errors.push(
											SyntaxErr::ExpectedCondExprAfterWhile(
												walker.get_last_span().next_single_width()
											),
										);
										return Err(errors);
									}
								};

							match current {
								Token::RParen => {
									if let Some(l_paren_span) = l_paren_span {
										errors.push(
													SyntaxErr::ExpectedCondExprAfterWhile(
														Span::new_between(l_paren_span, current_span)
													),
												);
									} else {
										errors.push(
													SyntaxErr::ExpectedCondExprAfterWhile(
														current_span.previous_single_width()
													),
												);
									}
									break 'expr_2 Expr {
										ty: ExprTy::Missing,
										span: current_span
											.previous_single_width(),
									};
								}
								Token::Semi => {
									if let Some(l_paren_span) = l_paren_span {
										errors.push(
													SyntaxErr::ExpectedCondExprAfterWhile(
														l_paren_span.next_single_width()
													),
												);
									} else {
										// We do nothing since the next check deals with the `;` and
										// produces an error for it.
									}
									break 'expr_2 Expr {
										ty: ExprTy::Missing,
										span: current_span
											.previous_single_width(),
									};
								}
								_ => continue 'expr_2,
							}
						};

					expr
				}
			};

			// Consume the closing `)` parenthesis. We loop until we hit either a `)` or a `;`. If we
			// have something like `while (i b - 5)`, we already get an error about the missing binary
			// operator, so no need to further produce errors; we just silently consume.
			let mut r_paren_span = None;
			let span_after_while_header = 'r_paren_2: loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						errors.push(SyntaxErr::ExpectedParenAfterWhileCond(
							l_paren_span,
							walker.get_last_span().next_single_width(),
						));
						return Err(errors);
					}
				};

				match current {
					Token::RParen => {
						let current_span = *current_span;
						r_paren_span = Some(current_span);
						walker.advance();
						break 'r_paren_2 current_span;
					}
					Token::Semi => {
						// We don't do anything apart from creating a syntax error since the next check
						// deals with the `;`.
						errors.push(SyntaxErr::ExpectedParenAfterWhileCond(
							l_paren_span,
							current_span.previous_single_width(),
						));
						break 'r_paren_2 current_span.previous_single_width();
					}
					_ => {
						walker.advance();
						continue 'r_paren_2;
					}
				}
			};

			// Consume the statement-ending `;` semicolon.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedSemiAfterDoWhileStmt(
						walker.get_last_span(),
					));
					return Err(errors);
				}
			};
			let semi_span = if *current == Token::Semi {
				walker.advance();
				Some(current_span)
			} else {
				// Even though we are missing a necessary token, it still makes sense to just treat
				// this as a "valid" loop for analysis. We do produce an error about the missing token.
				errors.push(SyntaxErr::ExpectedSemiAfterDoWhileStmt(
					span_after_while_header.next_single_width(),
				));
				None
			};

			return Ok((
				Some(Stmt {
					ty: StmtTy::DoWhile {
						do_kw: do_kw_span,
						body,
						while_kw: while_kw_span,
						l_paren: l_paren_span,
						cond,
						r_paren: r_paren_span,
						semi: semi_span,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				}),
				errors,
			));
		}
		Token::Return => {
			walker.advance();

			// Look for the optional return value expression.
			let (return_expr, mut errs) =
				expr_parser(walker, Mode::Default, &[Token::Semi]);
			errors.append(&mut errs);

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, _)) => {
					if *current == Token::Semi {
						walker.advance();
						Some(token_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				errors.push(SyntaxErr::ExpectedSemiAfterReturnKw(
					walker.get_previous_span().next_single_width(),
					return_expr.is_some(),
				));
			}

			return Ok((
				Some(Stmt {
					ty: StmtTy::Return {
						kw: token_span,
						value: return_expr,
						semi: semi_span,
					},
					span: Span::new(
						token_span.start,
						if let Some(semi_span) = semi_span {
							semi_span.end
						} else {
							// If an expression was found, this will point to the end of the expression, otherwise
							// it will point to the end of the `return` keyword.
							walker.get_previous_span().end
						},
					),
				}),
				errors,
			));
		}
		Token::Break => {
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, _)) => {
					if *current == Token::Semi {
						walker.advance();
						Some(token_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				errors.push(SyntaxErr::ExpectedSemiAfterBreakKw(
					token_span.next_single_width(),
				));
			}

			return Ok((
				Some(Stmt {
					ty: StmtTy::Break {
						kw: token_span,
						semi: semi_span,
					},
					span: Span::new(
						token_span.start,
						if let Some(semi_span) = semi_span {
							semi_span.end
						} else {
							token_span.end
						},
					),
				}),
				errors,
			));
		}
		Token::Continue => {
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, _)) => {
					if *current == Token::Semi {
						walker.advance();
						Some(token_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				errors.push(SyntaxErr::ExpectedSemiAfterContinueKw(
					token_span.next_single_width(),
				));
			}

			return Ok((
				Some(Stmt {
					ty: StmtTy::Continue {
						kw: token_span,
						semi: semi_span,
					},
					span: Span::new(
						token_span.start,
						if let Some(semi_span) = semi_span {
							semi_span.end
						} else {
							token_span.end
						},
					),
				}),
				errors,
			));
		}
		Token::Discard => {
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, _)) => {
					if *current == Token::Semi {
						walker.advance();
						Some(token_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				errors.push(SyntaxErr::ExpectedSemiAfterDiscardKw(
					token_span.next_single_width(),
				));
			}

			return Ok((
				Some(Stmt {
					ty: StmtTy::Discard {
						kw: token_span,
						semi: semi_span,
					},
					span: Span::new(
						token_span.start,
						if let Some(semi_span) = semi_span {
							semi_span.end
						} else {
							token_span.end
						},
					),
				}),
				errors,
			));
		}
		Token::Struct => {
			walker.advance();

			let (stmt, mut errs) = parse_struct(walker, qualifiers, token_span);
			errors.append(&mut errs);
			return Ok((stmt, errors));
		}
		_ => return Ok((None, errors)),
	}
}

/// Parses the body of a switch statement.
fn parse_switch_body(
	walker: &mut Walker,
	l_brace_span: Span,
) -> (Vec<(Option<Expr>, Option<Span>, Scope)>, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	// Check if the body is empty.
	match walker.peek() {
		Some((token, token_span)) => match token {
			Token::RBrace => {
				errors.push(SyntaxErr::FoundEmptySwitchBody(
					Span::new_between(l_brace_span, *token_span),
				));
				return (vec![], errors);
			}
			_ => {}
		},
		None => {
			errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
				Some(l_brace_span),
				walker.get_last_span().next_single_width(),
			));
			return (vec![], errors);
		}
	}

	// Consume cases until we reach the end of the body.
	let mut cases = Vec::new();
	'cases: loop {
		let (current, current_span) = match walker.peek() {
			Some(t) => (&t.0, t.1),
			None => {
				errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
					Some(l_brace_span),
					walker.get_last_span().next_single_width(),
				));
				break 'cases;
			}
		};

		match current {
			Token::Case => {
				let keyword_span = current_span;
				walker.advance();

				// Consume the expression.
				let expr = match expr_parser(
					walker,
					Mode::Default,
					&[Token::Colon, Token::Case, Token::Default, Token::RBrace],
				) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						e
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either `case`, `default` or a `}`.
						errors.push(SyntaxErr::ExpectedExprAfterCaseKw(
							keyword_span.next_single_width(),
						));
						loop {
							let (current, _) = match walker.peek() {
								Some(t) => (&t.0, t.1),
								None => {
									errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
											Some(l_brace_span),
											walker.get_last_span().next_single_width()
										));
									break 'cases;
								}
							};

							match current {
								Token::Case | Token::Default => continue 'cases,
								Token::RBrace => break 'cases,
								_ => walker.advance(),
							}
						}
					}
				};

				// Consume the `:` to begin the scope.
				let (current, current_span) = match walker.peek() {
					Some(t) => (&t.0, t.1),
					None => {
						errors.push(SyntaxErr::ExpectedColonAfterCase(
							walker.get_last_span().next_single_width(),
						));
						break 'cases;
					}
				};
				let mut colon_span = None;
				let scope_begin_span = if *current == Token::Colon {
					walker.advance();
					colon_span = Some(current_span);
					current_span
				} else {
					// Even though we are missing a necessary token, we treat this as "valid" for better error
					// recovery.
					errors.push(SyntaxErr::ExpectedColonAfterCase(
						expr.span.next_single_width(),
					));
					walker.get_last_span()
				};

				// Consume the body of the case. This does not consume a `case` or `default` keyword or `}`.
				let (body, mut errs) = parse_scope(
					walker,
					SWITCH_CASE_DELIMITER,
					scope_begin_span,
				);
				errors.append(&mut errs);

				cases.push((Some(expr), colon_span, body));
			}
			Token::Default => {
				let keyword_span = current_span;
				walker.advance();

				// Consume the `:` to begin the scope.
				let (current, current_span) = match walker.peek() {
					Some(t) => (&t.0, t.1),
					None => {
						errors.push(SyntaxErr::ExpectedColonAfterCase(
							walker.get_last_span().next_single_width(),
						));
						break 'cases;
					}
				};
				let mut colon_span = None;
				let scope_begin_span = if *current == Token::Colon {
					walker.advance();
					colon_span = Some(current_span);
					current_span
				} else {
					// Even though we are missing a necessary token, we treat this as "valid" for better error
					// recovery.
					errors.push(SyntaxErr::ExpectedColonAfterCase(
						keyword_span.next_single_width(),
					));
					keyword_span
				};

				// Consume the body of the case. This does not consume a `case` or `default` keyword or `}`.
				let (body, mut errs) = parse_scope(
					walker,
					SWITCH_CASE_DELIMITER,
					scope_begin_span,
				);
				errors.append(&mut errs);

				cases.push((None, colon_span, body));
			}
			Token::RBrace => break 'cases,
			_ => {
				// We have a token which cannot begin a case, so loop until we hit either `case`, `default` or a
				// `}`.
				errors.push(SyntaxErr::InvalidSwitchCaseBegin(current_span));
				'inner: loop {
					let (current, _) = match walker.peek() {
						Some(t) => (&t.0, t.1),
						None => {
							errors.push(
								SyntaxErr::MissingSwitchBodyClosingBrace(
									Some(l_brace_span),
									walker.get_last_span().next_single_width(),
								),
							);
							break 'cases;
						}
					};

					match current {
						Token::Case | Token::Default | Token::RBrace => {
							break 'inner
						}
						_ => walker.advance(),
					}
				}
			}
		}
	}

	(cases, errors)
}

/// Parse an if statement body.
fn parse_if(
	walker: &mut Walker,
	kw_span: Span,
	expects_condition: bool,
) -> Result<
	(
		Option<Span>,
		Option<Expr>,
		Option<Span>,
		Scope,
		Vec<SyntaxErr>,
	),
	Vec<SyntaxErr>,
> {
	let mut errors = Vec::new();

	let (l_paren_span, r_paren_span, header_end_span, cond) =
		if expects_condition {
			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedParenAfterIfKw(
						kw_span.next_single_width(),
					));
					return Err(errors);
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else {
				errors.push(SyntaxErr::ExpectedParenAfterIfKw(
					kw_span.next_single_width(),
				));
				None
			};

			// Consume the conditional expression.
			let cond =
				match expr_parser(walker, Mode::Default, &[Token::RParen]) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						e
					}
					(None, _) => {
						// Unlike with the other control flow statements, we don't loop until we hit a `)`
						// or a `{` because an if statement can omit the `{`, in which case we could
						// potentially loop until we hit the end of the file. So, if the next check doesn't
						// detect either token, we can quit parsing this statement. We do check for a
						// potential `( )` situation since that is easy to detect and cannot produce false
						// positives.
						if let Some((current, current_span)) = walker.peek() {
							if *current == Token::RParen
								|| *current == Token::LBrace
							{
								errors.push(SyntaxErr::ExpectedExprInIfHeader(
									Span::new_between(
										if let Some(l_paren_span) = l_paren_span
										{
											l_paren_span
										} else {
											kw_span
										},
										*current_span,
									),
								));
							} else {
								errors.push(SyntaxErr::ExpectedExprInIfHeader(
									walker.get_current_span(),
								));
							}
						} else {
							errors.push(SyntaxErr::ExpectedExprInIfHeader(
								walker.get_current_span(),
							));
						}
						Expr {
							ty: ExprTy::Missing,
							span: walker.get_current_span(),
						}
					}
				};

			// Consume the closing `)` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					errors.push(SyntaxErr::ExpectedParenAfterIfHeader(
						l_paren_span,
						walker.get_last_span().next_single_width(),
					));
					return Err(errors);
				}
			};
			if *current == Token::RParen {
				walker.advance();
				(l_paren_span, Some(current_span), current_span, Some(cond))
			} else if *current == Token::LBrace {
				// We don't do anything apart from creating a syntax error since the next check deals
				// with the optional `{`.
				errors.push(SyntaxErr::ExpectedParenAfterIfHeader(
					l_paren_span,
					current_span.previous_single_width(),
				));
				(l_paren_span, None, current_span, Some(cond))
			} else {
				errors.push(SyntaxErr::ExpectedParenAfterIfHeader(
					l_paren_span,
					Span::new_between(walker.get_previous_span(), current_span),
				));
				return Err(errors);
			}
		} else {
			(None, None, kw_span, None)
		};

	// Consume the optional opening `{` scope brace.
	let (current, current_span) = match walker.peek() {
		Some(t) => (&t.0, t.1),
		None => {
			// Even though if statements without a body are illegal, we treat this as "valid"
			// to produce better error recovery.
			errors.push(SyntaxErr::ExpectedBraceOrStmtAfterIfHeader(
				walker.get_last_span().next_single_width(),
			));
			return Ok((
				l_paren_span,
				cond,
				r_paren_span,
				Scope {
					opening: None,
					stmts: vec![],
					closing: None,
					span: walker.get_last_span().end_zero_width(),
				},
				errors,
			));
		}
	};
	let body = if *current == Token::LBrace {
		let l_brace_span = current_span;
		walker.advance();

		// Consume the body, including the closing `}` brace.
		let (body, mut errs) =
			parse_scope(walker, BRACE_DELIMITER, current_span);
		errors.append(&mut errs);

		body
	} else {
		// Since we are missing a `{`, we are expecting a single statement.
		let (stmt, mut errs) = match parse_statement_within_fn(walker) {
			Ok((stmt, err)) => (stmt, err),
			Err(err) => (None, err),
		};
		errors.append(&mut errs);

		match stmt {
			Some(s) => Scope {
				span: s.span,
				opening: None,
				stmts: vec![s],
				closing: None,
			},
			None => {
				errors.push(SyntaxErr::ExpectedStmtAfterIfHeader(
					// Panics: `r_paren_span` will be `None` if a `{` was encountered, but in that
					// case, the branch above will be chosen instead, and if we didn't encounter a
					// `)`, we will have already quit this parse, so this is always guaranteed to
					// be `Some` if we are in this branch.
					header_end_span.next_single_width(),
				));
				Scope {
					opening: None,
					stmts: vec![],
					closing: None,
					span: walker.get_last_span().end_zero_width(),
				}
			}
		}
	};

	Ok((l_paren_span, cond, r_paren_span, body, errors))
}

/// Parse a struct definition or declaration.
fn parse_struct(
	walker: &mut Walker,
	qualifiers: Vec<Qualifier>,
	kw_span: Span,
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
		Some(t) => (&t.0, t.1),
		None => {
			errors.push(SyntaxErr::ExpectedScopeAfterStructIdent(
				walker.get_last_span().next_single_width(),
			));
			return (None, errors);
		}
	};
	let l_brace_span = if *current == Token::LBrace {
		current_span
	} else if *current == Token::Semi {
		// Even though struct definitions are illegal, it still makes sense to just treat this as a "valid"
		// struct definition for analysis/goto/etc purposes. We do produce an error though about the illegality of
		// a struct definition.
		errors.push(SyntaxErr::StructDefIsIllegal(
			current_span,
			Span::new(kw_span.start, current_span.end),
		));
		walker.advance();
		return (
			Some(Stmt {
				ty: StmtTy::StructDef {
					kw: kw_span,
					ident,
					qualifiers,
					semi: current_span,
				},
				span: Span::new(kw_span.start, current_span.end),
			}),
			errors,
		);
	} else {
		errors.push(SyntaxErr::ExpectedScopeAfterStructIdent(
			Span::new_between(walker.get_previous_span(), current_span),
		));
		return (None, errors);
	};
	walker.advance();

	// Parse the struct body, including the closing `}` brace.
	let (body, mut errs) = parse_scope(walker, BRACE_DELIMITER, l_brace_span);

	// Check if there is an unclosed-scope syntax error, because if so, we can return early without produce further
	// error messages which would become confusing since they would be overlaid over each other.
	let mut missing_body_delim = false;
	errs.iter().for_each(|e| match e {
		SyntaxErr::ExpectedBraceScopeEnd(_, _) => missing_body_delim = true,
		_ => {}
	});
	errors.append(&mut errs);
	if missing_body_delim {
		return (
			Some(Stmt {
				span: Span::new(kw_span.start, body.span.end),
				ty: StmtTy::StructDecl {
					kw: kw_span,
					ident,
					body,
					qualifiers,
					instance: None,
					semi: None,
				},
			}),
			errors,
		);
	}

	// We don't remove invalid statements because we would loose information for the AST.
	let mut count = 0;
	body.stmts.iter().for_each(|stmt| match stmt.ty {
		StmtTy::VarDef { .. } | StmtTy::VarDefs(_, _) => count += 1,
		_ => errors.push(SyntaxErr::ExpectedVarDefInStructBody(stmt.span)),
	});
	// Check that there is at least one variable definition within the body.
	if count == 0 {
		let r_brace_span = walker.get_previous_span();
		errors.push(SyntaxErr::ExpectedAtLeastOneMemberInStruct(Span::new(
			l_brace_span.start,
			r_brace_span.end,
		)));
	}

	let after_body_span = walker.get_current_span();

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
					walker.get_previous_span().next_single_width(),
				));
				return (
					Some(Stmt {
						ty: StmtTy::StructDecl {
							kw: kw_span,
							ident,
							body,
							qualifiers,
							instance: None,
							semi: None,
						},
						span: Span::new(kw_span.start, after_body_span.end),
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
				walker.get_previous_span().next_single_width(),
			));
			return (
				Some(Stmt {
					ty: StmtTy::StructDecl {
						kw: kw_span,
						ident,
						body,
						qualifiers,
						instance,
						semi: None,
					},
					span: Span::new(kw_span.start, walker.get_last_span().end),
				}),
				errors,
			);
		}
	};
	if *current == Token::Semi {
		walker.advance();
		(
			Some(Stmt {
				ty: StmtTy::StructDecl {
					kw: kw_span,
					ident,
					body,
					qualifiers,
					instance,
					semi: Some(current_span),
				},
				span: Span::new(kw_span.start, current_span.end),
			}),
			errors,
		)
	} else {
		// Even though we are missing a necessary token to make the syntax valid, it still makes sense to just
		// treat this as a "valid" struct declaration for analysis/goto/etc purposes. We do produce an error though
		// about the missing token.
		errors.push(SyntaxErr::ExpectedSemiAfterStructBody(
			walker.get_previous_span().next_single_width(),
		));
		(
			Some(Stmt {
				ty: StmtTy::StructDecl {
					kw: kw_span,
					ident,
					body,
					qualifiers,
					instance,
					semi: None,
				},
				span: Span::new(kw_span.start, walker.get_previous_span().end),
			}),
			errors,
		)
	}
}

pub fn print_stmt(stmt: &Stmt, indent: usize) {
	match &stmt.ty {
		StmtTy::Empty => print!(
			"\r\n{:indent$}\x1b[9m(Empty)\x1b[0m",
			"",
			indent = indent * 4
		),
		StmtTy::VarDef {
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
		StmtTy::VarDefs(vars, qualifiers) => {
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
		StmtTy::VarDecl {
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
		StmtTy::VarDecls {
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
		StmtTy::FnDef {
			return_type,
			ident,
			params,
			qualifiers,
			..
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return: {return_type}, ident: {ident}, params: [",
				"",
				indent = indent * 4
			);
			for Param {
				qualifiers,
				type_,
				ident,
			} in params
			{
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
		StmtTy::FnDecl {
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
			for Param {
				qualifiers,
				type_,
				ident,
			} in params
			{
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
			for inner in &body.stmts {
				print_stmt(&inner, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::StructDef {
			ident, qualifiers, ..
		} => {
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
		StmtTy::StructDecl {
			ident,
			body,
			qualifiers,
			instance,
			..
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mStruct\x1b[0m(ident: {ident}, members: {{",
				"",
				indent = indent * 4
			);
			for stmt in &body.stmts {
				print_stmt(&stmt, indent + 1);
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
		StmtTy::Expr { expr, .. } => {
			print!("\r\n{:indent$}{expr}", "", indent = indent * 4);
		}
		StmtTy::Scope(scope) => {
			print!("\r\n{:indent$}{{", "", indent = indent * 4);
			for stmt in &scope.stmts {
				print_stmt(&stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::Preproc(p) => print!(
			"\r\n{:indent$}\x1b[4mPreproc({p})\x1b[0m",
			"",
			indent = indent * 4
		),
		StmtTy::If {
			cond,
			body,
			branches,
			..
		} => {
			print!("\r\n{:indent$}If({cond}) {{", "", indent = indent * 4);
			for stmt in &body.stmts {
				print_stmt(&stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);

			for (_, _, _, cond, _, body) in branches {
				if let Some(cond) = cond {
					print!(
						"\r\n{:indent$}ElseIf({cond}) {{",
						"",
						indent = indent * 4
					);
				} else {
					print!("\r\n{:indent$}Else {{", "", indent = indent * 4);
				}
				for stmt in &body.stmts {
					print_stmt(&stmt, indent + 1);
				}
				print!("\r\n{:indent$}}}", "", indent = indent * 4);
			}
		}
		StmtTy::Switch { expr, cases, .. } => {
			print!("\r\n{:indent$}Switch({expr}) {{", "", indent = indent * 4);
			for (expr, _, body) in cases {
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
				for stmt in &body.stmts {
					print_stmt(&stmt, indent + 2);
				}
				print!("\r\n{:indent$}}}", "", indent = (indent + 1) * 4);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::For {
			var,
			cond,
			inc,
			body,
			..
		} => {
			print!("\r\n{:indent$}For(", "", indent = indent * 4);
			if let Some(var) = var {
				print!("var:");
				print_stmt(&var, indent + 2);
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
			if let Some(body) = body {
				for stmt in &body.stmts {
					print_stmt(&stmt, indent + 1);
				}
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::While { cond, body, .. } => {
			print!("\r\n{:indent$}While({cond}) {{", "", indent = indent * 4);
			if let Some(body) = body {
				for stmt in &body.stmts {
					print_stmt(&stmt, indent + 1);
				}
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::DoWhile { cond, body, .. } => {
			print!(
				"\r\n{:indent$}Do-While({cond}) {{",
				"",
				indent = indent * 4
			);
			if let Some(body) = body {
				for stmt in &body.stmts {
					print_stmt(&stmt, indent + 1);
				}
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		StmtTy::Return { value, .. } => {
			print!("\r\n{:indent$}RETURN", "", indent = indent * 4);
			if let Some(expr) = value {
				print!("(value: {expr})");
			}
		}
		StmtTy::Break { .. } => {
			print!("\r\n{:indent$}BREAK", "", indent = indent * 4)
		}
		StmtTy::Continue { .. } => {
			print!("\r\n{:indent$}CONTINUE", "", indent = indent * 4)
		}
		StmtTy::Discard { .. } => {
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
