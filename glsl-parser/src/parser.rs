mod printing;

use crate::{
	ast::Type,
	cst::{
		Cst, Expr, ExprTy, Ident, IfBranch, IfTy, List, Node, NodeTy, Nodes,
		Param, Qualifier, Scope, SwitchBranch,
	},
	error::SyntaxErr,
	expression::{expr_parser, Mode},
	lexer::{lexer, OpTy, Token, TokenStream},
	log,
	span::{Span, Spanned},
	Either,
};

pub struct Walker {
	pub token_stream: TokenStream,
	pub cursor: usize,
}

impl Walker {
	/// Returns the current token under the cursor, without advancing the cursor.
	pub fn peek(&self) -> Option<&Spanned<Token>> {
		self.token_stream.get(self.cursor)
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	pub fn lookahead_1(&self) -> Option<&Spanned<Token>> {
		self.token_stream.get(self.cursor + 1)
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
		match self.token_stream.get(self.cursor) {
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
		self.cursor == self.token_stream.len()
	}

	/// Returns the [`Span`] of the current `Token`.
	///
	/// *Note:* If we have reached the end of the tokens, this will return the value of
	/// [`get_last_span()`](Self::get_last_span).
	pub fn get_current_span(&self) -> Span {
		match self.token_stream.get(self.cursor) {
			Some(t) => t.1,
			None => self.get_last_span(),
		}
	}

	/// Returns the [`Span`] of the previous `Token`.
	///
	/// *Note:* If the current token is the first, the span returned will be `0-0`.
	pub fn get_previous_span(&self) -> Span {
		self.token_stream
			.get(self.cursor - 1)
			.map_or(Span::empty(), |t| t.1)
	}

	/// Returns the [`Span`] of the last `Token`.
	///
	/// *Note:* If there are no tokens, the span returned will be `0-0`.
	pub fn get_last_span(&self) -> Span {
		self.token_stream.last().map_or(Span::empty(), |t| t.1)
	}
}

/// Parse a source file into a Concrete Syntax Tree.
pub fn parse(source: &str) -> (Cst, Vec<SyntaxErr>) {
	let token_stream = lexer(source);
	log!("{token_stream:?}");

	let mut walker = Walker {
		token_stream,
		cursor: 0,
	};
	let mut nodes = Vec::new();
	let mut errors = Vec::new();
	while walker.peek().is_some() {
		parse_stmt(&mut walker, &mut nodes, &mut errors);
	}

	(nodes, errors)
}

/// Try to parse a list of qualifiers beginning at the current position, if there are any. E.g.
/// - `const in ...`,
/// - `flat uniform ...`,
/// - `layout(location = 1) ...`.
///
/// This function makes no assumption as to what the current token is. This function does not produce a syntax
/// error if no qualifiers were found.
fn try_parse_qualifier_list(
	walker: &mut Walker,
	syntax_errors: &mut Vec<SyntaxErr>,
) -> Vec<Qualifier> {
	// Consume tokens until we've run out of qualifiers.
	let mut qualifiers = Vec::new();
	'qualifiers: loop {
		let (current, current_span) = match walker.peek() {
			Some(t) => t,
			None => break 'qualifiers,
		};

		use crate::cst::{
			Interpolation, Layout, Memory, Precision, QualifierTy, Storage,
		};

		match current {
			Token::Const => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Const),
				span: *current_span,
			}),
			Token::In => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::In),
				span: *current_span,
			}),
			Token::Out => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Out),
				span: *current_span,
			}),
			Token::InOut => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::InOut),
				span: *current_span,
			}),
			Token::Attribute => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Attribute),
				span: *current_span,
			}),
			Token::Uniform => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Uniform),
				span: *current_span,
			}),
			Token::Varying => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Varying),
				span: *current_span,
			}),
			Token::Buffer => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Buffer),
				span: *current_span,
			}),
			Token::Shared => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Shared),
				span: *current_span,
			}),
			Token::Centroid => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Centroid),
				span: *current_span,
			}),
			Token::Sample => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Sample),
				span: *current_span,
			}),
			Token::Patch => qualifiers.push(Qualifier {
				ty: QualifierTy::Storage(Storage::Patch),
				span: *current_span,
			}),
			Token::Flat => qualifiers.push(Qualifier {
				ty: QualifierTy::Interpolation(Interpolation::Flat),
				span: *current_span,
			}),
			Token::Smooth => qualifiers.push(Qualifier {
				ty: QualifierTy::Interpolation(Interpolation::Smooth),
				span: *current_span,
			}),
			Token::NoPerspective => qualifiers.push(Qualifier {
				ty: QualifierTy::Interpolation(Interpolation::NoPerspective),
				span: *current_span,
			}),
			Token::HighP => qualifiers.push(Qualifier {
				ty: QualifierTy::Precision(Precision::HighP),
				span: *current_span,
			}),
			Token::MediumP => qualifiers.push(Qualifier {
				ty: QualifierTy::Precision(Precision::MediumP),
				span: *current_span,
			}),
			Token::LowP => qualifiers.push(Qualifier {
				ty: QualifierTy::Precision(Precision::LowP),
				span: *current_span,
			}),
			Token::Invariant => qualifiers.push(Qualifier {
				ty: QualifierTy::Invariant,
				span: *current_span,
			}),
			Token::Precise => qualifiers.push(Qualifier {
				ty: QualifierTy::Precise,
				span: *current_span,
			}),
			Token::Coherent => qualifiers.push(Qualifier {
				ty: QualifierTy::Memory(Memory::Coherent),
				span: *current_span,
			}),
			Token::Volatile => qualifiers.push(Qualifier {
				ty: QualifierTy::Memory(Memory::Volatile),
				span: *current_span,
			}),

			Token::Restrict => qualifiers.push(Qualifier {
				ty: QualifierTy::Memory(Memory::Restrict),
				span: *current_span,
			}),

			Token::Readonly => qualifiers.push(Qualifier {
				ty: QualifierTy::Memory(Memory::Readonly),
				span: *current_span,
			}),

			Token::Writeonly => qualifiers.push(Qualifier {
				ty: QualifierTy::Memory(Memory::Writeonly),
				span: *current_span,
			}),

			Token::Layout => {
				let kw_span = *current_span;
				let node_span_start = kw_span.start;
				walker.advance();

				// Consume the opening `(` parenthesis.
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => {
						// We haven't found the opening `(` parenthesis, but we've reached the end of the token
						// stream.

						// Error recovery: we are missing the opening parenthesis.
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterLayout(
								kw_span.next_single_width(),
							),
						);
						qualifiers.push(Qualifier {
							ty: QualifierTy::Layout {
								kw: kw_span,
								l_paren: None,
								idents: None,
								r_paren: None,
							},
							span: kw_span,
						});
						break 'qualifiers;
					}
				};
				let l_paren_span;
				if *current == Token::LParen {
					l_paren_span = *current_span;
					walker.advance();
				} else {
					// Error recovery: we are missing the opening parenthesis.
					syntax_errors.push(SyntaxErr::ExpectedParenAfterLayout(
						kw_span.next_single_width(),
					));
					qualifiers.push(Qualifier {
						ty: QualifierTy::Layout {
							kw: kw_span,
							l_paren: None,
							idents: None,
							r_paren: None,
						},
						span: kw_span,
					});
					continue 'qualifiers;
				};

				// Consume layout identifiers (and optionally expressions) until we reach the closing `)`
				// parenthesis.
				let mut layouts = List::<Layout>::new();
				let r_paren_span = 'layouts: loop {
					let (current, current_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// We haven't found the closing `)` parenthesis yet, but we've reached the end of the
							// token stream.

							// Error recovery: we are missing the closing parenthesis.
							let node_last_span = walker.get_last_span();
							syntax_errors.push(
								SyntaxErr::ExpectedParenAtEndOfLayout(
									l_paren_span,
									node_last_span.next_single_width(),
								),
							);
							qualifiers.push(Qualifier {
								ty: QualifierTy::Layout {
									kw: kw_span,
									l_paren: Some(l_paren_span),
									idents: layouts.wrap_in_option(),
									r_paren: None,
								},
								span: Span::new(
									node_span_start,
									node_last_span.end,
								),
							});
							break 'qualifiers;
						}
					};

					match current {
						Token::Comma => {
							// Consume the `,` separator and continue looking for a layout identifier.
							layouts.push_separator(*current_span);
							walker.advance();
							continue 'layouts;
						}
						Token::RParen => {
							// Consume the closing `)` parenthesis and stop parsing this layout qualifier.
							let r_paren_span = *current_span;
							walker.advance();
							break 'layouts r_paren_span;
						}
						// Note: Any other tokens, such as `;`, will be detected in the `.to_layout()` method as
						// invalid and will exit the layout loop.
						_ => {}
					}

					let layout_ident_span = *current_span;
					// We are expecting a token which is a valid layout identifier.
					match current.to_layout() {
						Some(e) => {
							match e {
								Either::Left(ty) => {
									// We have a simple layout identifier.
									walker.advance();
									layouts.push_item(Layout {
										ty,
										span: layout_ident_span,
									});
								}
								Either::Right(_) => {
									// We have a layout identifier that expects a value afterwards.
									let layout_ident_token = current.clone();
									walker.advance();

									// Consume the `=` in `ident = expression`.
									let (current, current_span) = match walker
										.peek()
									{
										Some(t) => t,
										None => {
											// We haven't found the equals sign `=`, but we've reached the end
											// of the token stream.

											// Error recovery: we are missing an equals sign.
											layouts.push_item(
												layout_ident_token
													.to_layout_expr(
														layout_ident_span,
														None,
														None,
													),
											);
											let node_last_span =
												walker.get_last_span();
											syntax_errors.push(SyntaxErr::ExpectedEqAfterLayoutIdent(
												node_last_span.next_single_width()
											));
											qualifiers.push(Qualifier {
												ty: QualifierTy::Layout {
													kw: kw_span,
													l_paren: Some(l_paren_span),
													idents: layouts
														.wrap_in_option(),
													r_paren: None,
												},
												span: Span::new(
													node_span_start,
													node_last_span.end,
												),
											});
											break 'qualifiers;
										}
									};
									let eq_span;
									if *current == Token::Op(OpTy::Eq) {
										eq_span = *current_span;
										walker.advance();
									} else {
										// Error recovery: we are missing an equals sign.
										syntax_errors.push(SyntaxErr::ExpectedEqAfterLayoutIdent(
											kw_span.next_single_width()
										));
										layouts.push_item(
											layout_ident_token.to_layout_expr(
												kw_span, None, None,
											),
										);
										continue 'layouts;
									}

									// Consume the next `expression` in `ident = expression`.
									let expr = match expr_parser(
										walker,
										Mode::DisallowTopLevelList,
										&[Token::Comma, Token::RParen],
									) {
										(Some(e), mut err) => {
											syntax_errors.append(&mut err);
											e
										}
										(None, _) => {
											// Error recovery: we are missing an expression.
											syntax_errors.push(SyntaxErr::ExpectedValExprAfterLayoutIdent(
												layout_ident_span.next_single_width()
											));
											layouts.push_item(
												layout_ident_token
													.to_layout_expr(
														kw_span,
														Some(eq_span),
														None,
													),
											);
											continue 'layouts;
										}
									};

									layouts.push_item(
										layout_ident_token.to_layout_expr(
											layout_ident_span,
											Some(eq_span),
											Some(expr),
										),
									);
								}
							}
						}
						None => {
							// We found a token which can not be a valid layout identifier. This may however be a
							// different qualifier, such as `const`, so we don't consume the token and re-run the
							// outer loop. If it's not another qualifier, the outer loop will just exit.

							// Error recovery: we have a token which isn't a valid layout identifier. This means we
							// have ended the layout qualifier but we are missing a closing parenthesis.
							let node_last_span =
								if let Some(span) = layouts.span() {
									span
								} else {
									l_paren_span
								};
							syntax_errors.push(
								SyntaxErr::ExpectedParenAtEndOfLayout(
									l_paren_span,
									node_last_span.next_single_width(),
								),
							);
							qualifiers.push(Qualifier {
								ty: QualifierTy::Layout {
									kw: kw_span,
									l_paren: Some(l_paren_span),
									idents: layouts.wrap_in_option(),
									r_paren: None,
								},
								span: Span::new(
									node_span_start,
									node_last_span.end,
								),
							});
							continue 'qualifiers;
						}
					}
				};

				// TODO: Analyze list for syntax errors.

				let node_span_end = r_paren_span.end;
				qualifiers.push(Qualifier {
					ty: QualifierTy::Layout {
						kw: kw_span,
						l_paren: Some(l_paren_span),
						idents: layouts.wrap_in_option(),
						r_paren: Some(r_paren_span),
					},
					span: Span::new(node_span_start, node_span_end),
				});
				continue 'qualifiers;
			}
			// If we encounter anything other than a qualifier, that means we have reached the end of this list of
			// qualifiers and can return out of this function to move onto the next parsing step without consuming
			// the current token.
			_ => break 'qualifiers,
		}

		walker.advance();
	}

	qualifiers
}

/// Try to parse a single statement beginning at the current position which **doesn't** begin with a keyword. E.g.
/// - `int i;`,
/// - `i + 5;`,
/// - `void fn(...`.
///
/// This function makes no assumption as to what the current token is. This function does not produce a syntax
/// error if no statement was found. If successful, this function returns: `Some(nodes,
/// semi_colon_span, syntax_errors)`. If unsuccessful, this function returns `None` which means that no
/// tokens were consumed.
///
/// Note that if the current token is `{`, this function treats it as a start to an initializer list. If you want
/// to treat `{` as a beginning of a scope, the check must be performed *before* this function is called.
fn try_parse_stmt_not_beginning_with_keyword(
	walker: &mut Walker,
	qualifiers: &Vec<Qualifier>,
	end_tokens: &[Token],
) -> Option<(Vec<Node>, Option<Span>, Vec<SyntaxErr>)> {
	let mut errors = Vec::new();

	// Test to see if we have an expression, as all statements in this parsing branch start with an expression.
	let (start, mut errs) = match expr_parser(walker, Mode::Default, end_tokens)
	{
		(Some(e), errs) => (e, errs),
		// If the current token cannot begin any form of expression, that means this will be either a statement
		// beginning with a keyword or this is not a valid statement at all. In either case, we return back to the
		// caller.
		(None, _) => return None,
	};

	// Test to see if the expression can be converted to a type.
	if let Some(_) = Type::parse(&start) {
		// What we have parsed so far can be converted to a type. Since we ran the parser in `Mode::Default`, we
		// know that this cannot be a scenario such as `i` in `i = 5`; it must be something like `int` in `int i`.

		// This may be a more complex expression which includes brackets. We want to keep those syntax errors, but
		// we want to remove any syntax error about a missing operator between operands, so that we don't get a
		// syntax error for the fact that `int i` has no operator between `int` and `i`.
		errs.retain(|e| match e {
			SyntaxErr::FoundOperandAfterOperand(_, _) => false,
			_ => true,
		});
		errors.append(&mut errs);

		let type_ = start;

		// Check whether we have a function def/decl.
		match walker.peek() {
			Some((current, current_span)) => match current {
				Token::Ident(i) => match walker.lookahead_1() {
					Some((next, next_span)) => match next {
						Token::LParen => {
							// We have something like `int name (` which makes this a function def/decl.
							let ident = Ident {
								name: i.clone(),
								span: *current_span,
							};
							let l_paren_span = *next_span;
							walker.advance();
							walker.advance();
							let (ret, mut errs) = parse_fn(
								walker,
								type_,
								ident,
								qualifiers,
								l_paren_span,
							);
							errors.append(&mut errs);
							return Some((vec![ret], None, errors));
						}
						_ => {}
					},
					None => {}
				},
				_ => {}
			},
			None => {
				// We have something like `int` or `ident`, and we've reached the end of the token stream.

				// Error recovery: we are missing a semi colon after an expression statement.
				errors.push(SyntaxErr::ExpectedSemiAfterStmt(
					walker.get_last_span().next_single_width(),
				));
				return Some((
					vec![Node {
						span: type_.span,
						ty: NodeTy::ExprStmt {
							expr: type_,
							semi: None,
						},
					}],
					None,
					errors,
				));
			}
		}

		// We don't have a function def/decl, so this can only be a variable def/decl and nothing else.

		// Look for an identifier(s) expression following the type expression.
		let (ident_expr, mut errs) =
			match expr_parser(walker, Mode::BreakAtEq, &[Token::Semi]) {
				(Some(e), errs) => (e, errs),
				(None, _) => {
					// We have a single expression followed by something that can't be parsed as an expression (or
					// nothing), so we treat this as an expression statement.

					// Error recovery: we are missing a semi-colon after an expression statement.
					errors.push(SyntaxErr::ExpectedStmtFoundExpr(
						type_.span.next_single_width(),
					));
					return Some((
						vec![Node {
							span: type_.span,
							ty: NodeTy::ExprStmt {
								expr: type_,
								semi: None,
							},
						}],
						None,
						errors,
					));
				}
			};

		// Test to see if we can convert the expression into a list of identifiers. This is necessary because the
		// expression can contain one or more identifiers, and these identifiers can also contain an array size.
		let ident_exprs = ident_expr.to_ident_list();
		if ident_exprs.is_empty() {
			// We could not convert the expression into multiple identifier sub-expressions. This could be
			// something like `i + 5`.

			// Error recovery: we have an expression after the type expression that is not an identifier(s)
			// expression. We don't try to save this.
			errors.push(SyntaxErr::ExpectedIdentsAfterVarType(ident_expr.span));
			let mut nodes = vec![
				Node {
					span: type_.span,
					ty: NodeTy::Invalid,
				},
				Node {
					span: ident_expr.span,
					ty: NodeTy::Invalid,
				},
			];

			// Consume tokens until we come across a token which can unambiguously end this statement, this could
			// be another semi-colon `;` or a keyword which starts a new statement.
			let mut ending_semi_span = None;
			loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => break,
				};

				if *current == Token::Semi {
					nodes.push(Node {
						ty: NodeTy::Punctuation,
						span: *current_span,
					});
					ending_semi_span = Some(*current_span);
					walker.advance();
					break;
				} else if current.starts_statement() {
					break;
				} else {
					nodes.push(Node {
						ty: NodeTy::Invalid,
						span: *current_span,
					});
					walker.advance();
					continue;
				}
			}

			return Some((nodes, ending_semi_span, errors));
		}

		let ident_count = ident_exprs.len();
		errors.append(&mut errs);

		// Declare constructors here to avoid duplicating the code all over the place.
		fn var_def_constructor(
			qualifiers: &Vec<Qualifier>,
			type_: Expr,
			idents: Expr,
			count: usize,
			semi: Option<Span>,
		) -> Node {
			let start = if let Some(qualifier) = qualifiers.first() {
				qualifier.span.start
			} else {
				type_.span.start
			};
			let end = if let Some(semi) = semi {
				semi.end
			} else {
				idents.span.end
			};
			let span = Span::new(start, end);

			match count {
				1 => Node {
					ty: NodeTy::VarDef {
						qualifiers: qualifiers.to_vec(),
						type_,
						ident: idents,
						semi,
					},
					span,
				},
				_ => Node {
					ty: NodeTy::VarDefs {
						qualifiers: qualifiers.to_vec(),
						type_,
						idents,
						semi,
					},
					span,
				},
			}
		}
		fn var_decl_constructor(
			qualifiers: &Vec<Qualifier>,
			type_: Expr,
			idents: Expr,
			count: usize,
			eq: Option<Span>,
			value: Option<Expr>,
			semi: Option<Span>,
		) -> Node {
			let start = if let Some(qualifier) = qualifiers.first() {
				qualifier.span.start
			} else {
				type_.span.start
			};
			let end = if let Some(semi) = semi {
				semi.end
			} else if let Some(value) = &value {
				value.span.end
			} else if let Some(eq) = eq {
				eq.end
			} else {
				idents.span.end
			};
			let span = Span::new(start, end);

			match count {
				1 => Node {
					ty: NodeTy::VarDecl {
						qualifiers: qualifiers.to_vec(),
						type_,
						ident: idents,
						eq,
						value,
						semi,
					},
					span,
				},
				_ => Node {
					ty: NodeTy::VarDecls {
						qualifiers: qualifiers.to_vec(),
						type_,
						idents,
						eq,
						value,
						semi,
					},
					span,
				},
			}
		}

		// Consume either the `;` for a definition or a `=` for a declaration.
		let (current, current_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We haven't found the semi colon `;` or the equals sign `=` yet, but we've reached the end of the
				// token stream.

				// Error recovery: we are missing the semi colon or equals sign.
				errors.push(SyntaxErr::ExpectedSemiOrEqAfterVarDef(
					walker.get_last_span().next_single_width(),
				));
				return Some((
					vec![var_def_constructor(
						qualifiers,
						type_,
						ident_expr,
						ident_count,
						None,
					)],
					None,
					errors,
				));
			}
		};
		if *current == Token::Semi {
			// We have a variable definition.
			let semi_span = *current_span;
			walker.advance();

			return Some((
				vec![var_def_constructor(
					qualifiers,
					type_,
					ident_expr,
					ident_count,
					Some(semi_span),
				)],
				Some(semi_span),
				errors,
			));
		} else if *current == Token::Op(OpTy::Eq) {
			// We have a variable declarations.
			let eq_span = *current_span;
			walker.advance();

			// Look for a value expression.
			let value_expr =
				match expr_parser(walker, Mode::Default, &[Token::Semi]) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						e
					}
					(None, _) => {
						// Error recovery: we are missing the value expression.
						errors.push(SyntaxErr::ExpectedExprAfterVarDeclEq(
							eq_span.next_single_width(),
						));
						return Some((
							vec![var_decl_constructor(
								qualifiers,
								type_,
								ident_expr,
								ident_count,
								Some(eq_span),
								None,
								None,
							)],
							None,
							errors,
						));
					}
				};

			// Consume the `;` to end the declarations.
			let (current, current_span) = match walker.peek() {
				Some(t) => t,
				None => {
					// Error recovery: we are missing the semi colon.
					errors.push(SyntaxErr::ExpectedSemiAfterVarDeclExpr(
						walker.get_last_span().next_single_width(),
					));
					return Some((
						vec![var_decl_constructor(
							qualifiers,
							type_,
							ident_expr,
							ident_count,
							Some(eq_span),
							Some(value_expr),
							None,
						)],
						None,
						errors,
					));
				}
			};

			if *current == Token::Semi {
				let semi_span = *current_span;
				walker.advance();

				return Some((
					vec![var_decl_constructor(
						qualifiers,
						type_,
						ident_expr,
						ident_count,
						Some(eq_span),
						Some(value_expr),
						Some(semi_span),
					)],
					Some(semi_span),
					errors,
				));
			} else {
				let mut nodes = vec![var_decl_constructor(
					qualifiers,
					type_,
					ident_expr,
					ident_count,
					Some(eq_span),
					Some(value_expr),
					None,
				)];

				// Consume tokens until we come across a token which can unambiguously end this statement, this could
				// be another semi-colon `;` or a keyword which starts a new statement.
				let mut consumed_semi = None;
				loop {
					let (current, current_span) = match walker.peek() {
						Some(t) => t,
						None => break,
					};

					if *current == Token::Semi {
						nodes.push(Node {
							ty: NodeTy::Punctuation,
							span: *current_span,
						});
						consumed_semi = Some(*current_span);
						walker.advance();
						break;
					} else if current.starts_statement() {
						break;
					} else {
						nodes.push(Node {
							ty: NodeTy::Invalid,
							span: *current_span,
						});
						walker.advance();
						continue;
					}
				}

				return Some((nodes, consumed_semi, errors));
			}
		} else {
			// Error recovery: we are missing the semi colon or equals sign.
			errors.push(SyntaxErr::ExpectedSemiOrEqAfterVarDef(
				ident_expr.span.next_single_width(),
			));
			let mut nodes = vec![var_def_constructor(
				qualifiers,
				type_,
				ident_expr,
				ident_count,
				None,
			)];

			// Consume tokens until we come across a token which can unambiguously end this statement, this could
			// be another semi-colon `;` or a keyword which starts a new statement.
			let mut consumed_semi = None;
			loop {
				let (current, current_span) = match walker.peek() {
					Some(t) => t,
					None => break,
				};

				if *current == Token::Semi {
					nodes.push(Node {
						ty: NodeTy::Punctuation,
						span: *current_span,
					});
					consumed_semi = Some(*current_span);
					walker.advance();
					break;
				} else if current.starts_statement() {
					break;
				} else {
					nodes.push(Node {
						ty: NodeTy::Invalid,
						span: *current_span,
					});
					walker.advance();
					continue;
				}
			}

			return Some((nodes, consumed_semi, errors));
		}
	}

	// Whatever we have cannot be the start of a variable/function def/decl, hence it must just be an expression
	// statement in its own right.
	let expr = start;
	errors.append(&mut errs);

	// Consume the `;` to end the statement.
	let (current, current_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// We have an expression, and we've reached the end of the token stream.

			// Error recovery: we are missing a semi-colon after the expression.
			errors.push(SyntaxErr::ExpectedSemiAfterStmt(
				expr.span.next_single_width(),
			));
			return Some((
				vec![Node {
					span: expr.span,
					ty: NodeTy::ExprStmt { expr, semi: None },
				}],
				None,
				errors,
			));
		}
	};
	if *current == Token::Semi {
		let node = Node {
			span: Span::new(expr.span.start, current_span.end),
			ty: NodeTy::ExprStmt {
				expr,
				semi: Some(*current_span),
			},
		};
		let semi = Some(*current_span);
		walker.advance();

		Some((vec![node], semi, errors))
	} else {
		// Error recovery: we are missing a semi-colon after the expression.
		errors.push(SyntaxErr::ExpectedSemiAfterStmt(
			expr.span.next_single_width(),
		));
		let mut nodes = vec![Node {
			span: expr.span,
			ty: NodeTy::ExprStmt { expr, semi: None },
		}];

		// Consume tokens until we come across a token which can unambiguously end this statement, this could
		// be another semi-colon `;` or a keyword which starts a new statement.
		let mut ending_semi_span = None;
		loop {
			let (current, current_span) = match walker.peek() {
				Some(t) => t,
				None => break,
			};

			if *current == Token::Semi {
				nodes.push(Node {
					ty: NodeTy::Punctuation,
					span: *current_span,
				});
				ending_semi_span = Some(*current_span);
				walker.advance();
				break;
			} else if current.starts_statement() {
				break;
			} else {
				nodes.push(Node {
					ty: NodeTy::Invalid,
					span: *current_span,
				});
				walker.advance();
				continue;
			}
		}

		Some((nodes, ending_semi_span, errors))
	}
}

/// Parse a statement beginning at the current position.
///
/// [`Ok`] is returned in the following cases:
/// - a fully valid statement was found (in which case there will be no syntax errors),
/// - a partially valid statement was found and recovered (in which case there will be some syntax errors),
/// - a partially valid statement was found but could not recover a meaningful CST node (in which case there will
///   be some syntax errors).
///
/// [`Err`] is returned if the following:
/// - the end of the token stream was reached without being able to produce either a fully valid statement or a
///   recovered partially valid statement.
///
/// # Panics
/// This function assumes that there is a current `Token` to peek.
fn parse_stmt(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	syntax_errors: &mut Vec<SyntaxErr>,
) {
	// Panics: This is guaranteed to unwrap without panic because of the while-loop precondition.
	let (current, current_span) = walker
		.peek()
		.expect("[parser::parse_stmt] Found no current token.");

	// If we immediately encounter an opening `{` brace, that means we have an new inner scope. We need to
	// perform this check before the `expr_parser()` call because that would treat the `{` as the beginning of
	// an initializer list.
	if *current == Token::LBrace {
		let l_brace_span = *current_span;
		walker.advance();

		let (inner_scope, mut inner_errs) =
			parse_scope(walker, BRACE_DELIMITER, l_brace_span);
		syntax_errors.append(&mut inner_errs);

		nodes.push(Node {
			span: Span::new(l_brace_span.start, inner_scope.span.end),
			ty: NodeTy::Scope(inner_scope),
		});
		return;
	}

	// TODO: Deal with comments?

	// First, we look for any qualifiers because they are always located first in a statement.
	let qualifiers = try_parse_qualifier_list(walker, syntax_errors);

	// Next, we try to parse a statement that doesn't begin with a keyword, such as a variable declaration.
	match try_parse_stmt_not_beginning_with_keyword(
		walker,
		&qualifiers,
		&[Token::Semi],
	) {
		Some((mut inner, _, mut err)) => {
			syntax_errors.append(&mut err);
			nodes.append(&mut inner);
			return;
		}
		None => {}
	}

	// We failed to parse anything, which means that this must be a statement beginning with a keyword. We check
	// for qualifiers since those cannot annotate a keyword statement.

	let qualifier_span_end = if !qualifiers.is_empty() {
		// Panics: There is at least one element so `last()` will return `Some`.
		Some(qualifiers.last().unwrap().span.end_zero_width())
	} else {
		None
	};
	let (token, token_span) = match walker.peek() {
		Some(t) => (&t.0, t.1),
		None => {
			// We potentially parsed some qualifiers and have reached the EOF.
			if let Some(span) = qualifier_span_end {
				syntax_errors
					.push(SyntaxErr::ExpectedDefDeclAfterQualifiers(span));
			}
			return;
		}
	};

	match token {
		Token::Struct => {}
		_ => {
			// We cannot have qualifiers before any other keywords.
			if !qualifiers.is_empty() {
				qualifiers.into_iter().for_each(|q| {
					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: q.span,
					})
				});
				syntax_errors.push(SyntaxErr::ExpectedDefDeclAfterQualifiers(
					// Panics: This is assigned `Some` if `qualifiers` is not empty, and we currently have just
					// checked for that condition.
					qualifier_span_end.unwrap(),
				));
				return;
			}
		}
	}

	match token {
		Token::Semi => {
			walker.advance();
			nodes.push(Node {
				ty: NodeTy::EmptyStmt,
				span: token_span,
			});
		}
		Token::If => {
			let kw_span = token_span;
			walker.advance();

			// Parse the first `if ...` branch.
			let mut branches = Vec::new();
			let (first, mut errs) =
				parse_if_header_body(walker, IfTy::If(kw_span), true);
			syntax_errors.append(&mut errs);
			branches.push(first);

			'branches: loop {
				let (token, token_span) = match walker.peek() {
					Some(t) => (&t.0, t.1),
					None => {
						nodes.push(Node {
							ty: NodeTy::If { branches },
							span: Span::new(
								token_span.start,
								walker.get_last_span().end,
							),
						});
						return;
					}
				};

				match token {
					Token::Else => {
						let else_span = token_span;
						walker.advance();

						let (current, current_span) = match walker.peek() {
							Some(t) => (&t.0, t.1),
							None => {
								syntax_errors.push(
									SyntaxErr::ExpectedIfOrBodyAfterElseKw(
										walker
											.get_last_span()
											.next_single_width(),
									),
								);
								return;
							}
						};

						if *current == Token::If {
							let if_span = current_span;
							// We have `else if`.
							walker.advance();

							let (branch, mut errs) = parse_if_header_body(
								walker,
								IfTy::ElseIf(else_span, if_span),
								true,
							);
							syntax_errors.append(&mut errs);
							branches.push(branch);
						} else {
							// We just have `else`.

							let (branch, mut errs) = parse_if_header_body(
								walker,
								IfTy::Else(else_span),
								false,
							);
							syntax_errors.append(&mut errs);
							branches.push(branch);
						}
					}
					_ => break 'branches,
				}
			}

			nodes.push(Node {
				ty: NodeTy::If { branches },
				span: Span::new(
					token_span.start,
					walker.get_previous_span().end,
				),
			});
		}
		Token::Switch => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(SyntaxErr::ExpectedParenAfterSwitchKw(
						token_span.next_single_width(),
					));

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: kw_span,
					});
					return;
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				let l_brace_span = current_span;
				walker.advance();

				// We are completely missing the condition expression, but we treat this as "valid" for
				// better recovery.
				syntax_errors.push(SyntaxErr::MissingSwitchHeader(
					Span::new_between(token_span, current_span),
				));

				// Consume the body, including the closing `}` brace.
				let (cases, mut errs, r_brace) =
					parse_switch_body(walker, current_span);
				syntax_errors.append(&mut errs);

				nodes.push(Node {
					ty: NodeTy::Switch {
						kw: kw_span,
						l_paren: None,
						expr: None,
						r_paren: None,
						l_brace: Some(l_brace_span),
						cases,
						r_brace,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				});
				return;
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				syntax_errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
					token_span.next_single_width(),
				));
				None
			};

			// Consume the conditional expression.
			let mut expr_nodes =
				match expr_parser(walker, Mode::Default, &[Token::RParen]) {
					(Some(e), mut errs) => {
						syntax_errors.append(&mut errs);
						Some(Nodes::new_with(Node {
							span: e.span,
							ty: NodeTy::Expression(e),
						}))
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either a `)` or a `{`.
						let mut invalid_expr_nodes = Nodes::new();
						'expr_4: loop {
							let (current, current_span) = match walker.peek() {
								Some(t) => (&t.0, t.1),
								None => {
									syntax_errors.push(
										SyntaxErr::ExpectedExprInSwitchHeader(
											walker
												.get_last_span()
												.next_single_width(),
										),
									);

									nodes.push(Node {
										ty: NodeTy::Keyword,
										span: kw_span,
									});
									if let Some(l_paren_span) = l_paren_span {
										nodes.push(Node {
											ty: NodeTy::Punctuation,
											span: l_paren_span,
										});
									}
									nodes.append(&mut invalid_expr_nodes.inner);
									return;
								}
							};

							match current {
								Token::RParen | Token::RBrace => {
									if let Some(l_paren_span) = l_paren_span {
										syntax_errors.push(
											SyntaxErr::ExpectedExprInSwitchHeader(
												Span::new_between(l_paren_span, current_span)
											),
										);
									} else {
										syntax_errors.push(
											SyntaxErr::ExpectedExprInSwitchHeader(
												current_span.previous_single_width()
											),
										);
									}
									break 'expr_4;
								}
								_ => {
									invalid_expr_nodes.push(Node {
										ty: NodeTy::Invalid,
										span: current_span,
									});
									walker.advance();
									continue 'expr_4;
								}
							}
						}
						if invalid_expr_nodes.is_empty() {
							None
						} else {
							Some(invalid_expr_nodes)
						}
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterSwitchHeader(
								l_paren_span,
								walker.get_last_span().next_single_width(),
							),
						);

						nodes.push(Node {
							ty: NodeTy::Keyword,
							span: kw_span,
						});
						if let Some(l_paren_span) = l_paren_span {
							nodes.push(Node {
								ty: NodeTy::Punctuation,
								span: l_paren_span,
							});
						}
						if let Some(mut expr_nodes) = expr_nodes {
							nodes.append(&mut expr_nodes.inner);
						}
						return;
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterSwitchHeader(
								l_paren_span,
								current_span.previous_single_width(),
							),
						);
						break 'r_paren_3 current_span.previous_single_width();
					}
					_ => {
						if let Some(ref mut expr_nodes) = expr_nodes {
							expr_nodes.push(Node {
								ty: NodeTy::Invalid,
								span: *current_span,
							});
						} else {
							expr_nodes = Some(Nodes::new_with(Node {
								ty: NodeTy::Invalid,
								span: *current_span,
							}));
						}
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
					syntax_errors.push(
						SyntaxErr::ExpectedBraceAfterSwitchHeader(
							walker.get_last_span().next_single_width(),
						),
					);

					nodes.push(Node {
						ty: NodeTy::Switch {
							kw: kw_span,
							l_paren: l_paren_span,
							expr: expr_nodes,
							r_paren: r_paren_span,
							l_brace: None,
							cases: vec![],
							r_brace: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_last_span().end,
						),
					});
					return;
				}
			};
			let l_brace_span = if *current == Token::LBrace {
				walker.advance();
				current_span
			} else {
				syntax_errors.push(SyntaxErr::ExpectedBraceAfterSwitchHeader(
					span_after_header.next_single_width(),
				));

				nodes.push(Node {
					ty: NodeTy::Switch {
						kw: kw_span,
						l_paren: l_paren_span,
						expr: expr_nodes,
						r_paren: r_paren_span,
						l_brace: None,
						cases: vec![],
						r_brace: None,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				});
				return;
			};

			// Consume the body, including the closing `}` brace.
			let (cases, mut errs, r_brace_span) =
				parse_switch_body(walker, current_span);
			syntax_errors.append(&mut errs);

			nodes.push(Node {
				ty: NodeTy::Switch {
					kw: kw_span,
					l_paren: l_paren_span,
					expr: expr_nodes,
					r_paren: r_paren_span,
					l_brace: Some(l_brace_span),
					cases,
					r_brace: r_brace_span,
				},
				span: Span::new(
					token_span.start,
					walker.get_previous_span().end,
				),
			});
		}
		Token::For => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(SyntaxErr::ExpectedParenAfterForKw(
						kw_span.next_single_width(),
					));

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: kw_span,
					});
					return;
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				walker.advance();

				// We are completely missing the header, but we treat this as "valid" for better
				// recovery.
				syntax_errors.push(SyntaxErr::MissingForHeader(
					Span::new_between(kw_span, current_span),
				));

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				syntax_errors.append(&mut errs);

				nodes.push(Node {
					span: Span::new(kw_span.start, body.span.end),
					ty: NodeTy::For {
						kw: kw_span,
						l_paren: None,
						nodes: None,
						r_paren: None,
						body: Some(body),
					},
				});
				return;
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				syntax_errors.push(SyntaxErr::ExpectedParenAfterForKw(
					kw_span.next_single_width(),
				));
				None
			};

			let mut args = List::new();
			let mut r_paren_span = None;
			'for_args: loop {
				let (current, current_span) = match walker.peek() {
					Some((t, s)) => (t, *s),
					None => {
						// We haven't found the closing `)` parenthesis yet, but we've reached the end of the
						// token stream.

						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterForHeader(
								l_paren_span,
								walker.get_last_span().next_single_width(),
							),
						);

						nodes.push(Node {
							ty: NodeTy::Keyword,
							span: kw_span,
						});
						if let Some(l_paren_span) = l_paren_span {
							nodes.push(Node {
								ty: NodeTy::Punctuation,
								span: l_paren_span,
							});
						}
						// TODO:
						return;
					}
				};

				match current {
					Token::Semi => {
						args.push_separator(current_span);
						walker.advance();
						continue 'for_args;
					}
					Token::RParen => {
						walker.advance();
						r_paren_span = Some(current_span);
						break 'for_args;
					}
					Token::LBrace => {
						break 'for_args;
					}
					_ => {}
				}

				if let Some((nodes, semi, mut err)) =
					try_parse_stmt_not_beginning_with_keyword(
						walker,
						&Vec::<Qualifier>::new(),
						&[Token::RParen],
					) {
					syntax_errors.append(&mut err);

					args.push_item(Nodes::from_vec(nodes));
					if let Some(semi) = semi {
						args.push_separator(semi);
					}

					continue 'for_args;
				} else {
					let mut invalid_nodes = Nodes::new();
					'invalid_param: loop {
						let (current, current_span) = match walker.peek() {
							Some(t) => t,
							None => {
								return;
							}
						};

						match current {
							Token::Semi | Token::RParen | Token::LBrace => {
								break 'invalid_param
							}
							_ => {
								invalid_nodes.push(Node {
									span: *current_span,
									ty: NodeTy::Invalid,
								});
								walker.advance();
							}
						}
					}
					args.push_item(invalid_nodes);
					continue 'for_args;
				}
			}

			// TODO: Analyze list for syntax errors.

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Even though for loops without a body are illegal, we treat this as "valid" for
					// better error recovery.
					syntax_errors.push(SyntaxErr::ExpectedBraceAfterForHeader(
						walker.get_last_span().next_single_width(),
					));

					nodes.push(Node {
						ty: NodeTy::For {
							kw: kw_span,
							l_paren: l_paren_span,
							nodes: args.wrap_in_option(),
							r_paren: r_paren_span,
							body: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_last_span().end,
						),
					});
					return;
				}
			};
			if *current == Token::LBrace {
				walker.advance();
			} else {
				// Even though for loops without a body are illegal, we treat this as "valid" for
				// better error recovery.
				/* errors.push(SyntaxErr::ExpectedBraceAfterForHeader(
					span_after_header.next_single_width(),
				)); */

				nodes.push(Node {
					ty: NodeTy::For {
						kw: kw_span,
						l_paren: l_paren_span,
						nodes: args.wrap_in_option(),
						r_paren: r_paren_span,
						body: None,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				});
				return;
			}

			// Consume the body, including the closing `}` brace.
			let (body, mut errs) =
				parse_scope(walker, BRACE_DELIMITER, current_span);
			syntax_errors.append(&mut errs);

			nodes.push(Node {
				span: Span::new(token_span.start, body.span.end),
				ty: NodeTy::For {
					kw: kw_span,
					l_paren: l_paren_span,
					nodes: args.wrap_in_option(),
					r_paren: r_paren_span,
					body: Some(body),
				},
			});
		}
		Token::While => {
			let kw_span = token_span;
			walker.advance();

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
						kw_span.next_single_width(),
					));

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: kw_span,
					});
					return;
				}
			};
			let l_paren_span = if *current == Token::LParen {
				walker.advance();
				Some(current_span)
			} else if *current == Token::LBrace {
				walker.advance();

				// We are completely missing the condition expression, but we treat this as "valid" for
				// better recovery.
				syntax_errors.push(SyntaxErr::ExpectedCondExprAfterWhile(
					Span::new_between(kw_span, current_span),
				));

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				syntax_errors.append(&mut errs);

				nodes.push(Node {
					span: Span::new(kw_span.start, body.span.end),
					ty: NodeTy::While {
						kw: kw_span,
						l_paren: None,
						cond: None,
						r_paren: None,
						body: Some(body),
					},
				});
				return;
			} else {
				// Even though we are missing the token, we will still try to parse this syntax at
				// least until we expect the body scope.
				syntax_errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
					kw_span.next_single_width(),
				));
				None
			};

			// Consume the conditional expression.
			let mut cond_nodes =
				match expr_parser(walker, Mode::Default, &[Token::RParen]) {
					(Some(e), mut errs) => {
						syntax_errors.append(&mut errs);
						Nodes::new_with(Node {
							span: e.span,
							ty: NodeTy::Expression(e),
						})
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either a `)` or a `{`.
						let mut invalid_cond_nodes = Nodes::new();
						'expr: loop {
							let (current, current_span) = match walker.peek() {
								Some(t) => (&t.0, t.1),
								None => {
									syntax_errors.push(
										SyntaxErr::ExpectedCondExprAfterWhile(
											walker
												.get_last_span()
												.next_single_width(),
										),
									);

									nodes.push(Node {
										ty: NodeTy::Keyword,
										span: kw_span,
									});
									if let Some(l_paren_span) = l_paren_span {
										nodes.push(Node {
											ty: NodeTy::Punctuation,
											span: l_paren_span,
										});
									}
									nodes.append(&mut invalid_cond_nodes.inner);
									return;
								}
							};

							match current {
								Token::RParen | Token::LBrace => {
									if let Some(l_paren_span) = l_paren_span {
										syntax_errors.push(
											SyntaxErr::ExpectedCondExprAfterWhile(
												Span::new_between(l_paren_span, current_span)
											),
										);
									} else {
										syntax_errors.push(
											SyntaxErr::ExpectedCondExprAfterWhile(
												current_span.previous_single_width()
											),
										);
									}
									break 'expr;
								}
								_ => {
									invalid_cond_nodes.push(Node {
										ty: NodeTy::Invalid,
										span: current_span,
									});
									walker.advance();
									continue 'expr;
								}
							}
						}

						invalid_cond_nodes
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterWhileCond(
								l_paren_span,
								walker.get_last_span().next_single_width(),
							),
						);

						nodes.push(Node {
							ty: NodeTy::Keyword,
							span: kw_span,
						});
						if let Some(l_paren) = l_paren_span {
							nodes.push(Node {
								ty: NodeTy::Punctuation,
								span: l_paren,
							});
						}
						nodes.append(&mut cond_nodes.inner);
						return;
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterWhileCond(
								l_paren_span,
								current_span.previous_single_width(),
							),
						);
						break 'r_paren current_span.start_zero_width();
					}
					_ => {
						cond_nodes.push(Node {
							ty: NodeTy::Invalid,
							span: *current_span,
						});
						walker.advance();
						continue 'r_paren;
					}
				}
			};

			let cond_nodes = if !cond_nodes.is_empty() {
				Some(cond_nodes)
			} else {
				None
			};

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Even though while loops without a body are illegal, we treat this as "valid" for
					// better recovery.
					syntax_errors.push(
						SyntaxErr::ExpectedScopeAfterControlFlowExpr(
							walker.get_last_span().next_single_width(),
						),
					);

					nodes.push(Node {
						ty: NodeTy::While {
							kw: token_span,
							l_paren: l_paren_span,
							cond: cond_nodes,
							r_paren: r_paren_span,
							body: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_last_span().end,
						),
					});
					return;
				}
			};
			if *current == Token::LBrace {
				walker.advance();
			} else {
				syntax_errors.push(
					SyntaxErr::ExpectedScopeAfterControlFlowExpr(
						span_before_body.next_single_width(),
					),
				);

				nodes.push(Node {
					ty: NodeTy::While {
						kw: token_span,
						l_paren: l_paren_span,
						cond: cond_nodes,
						r_paren: r_paren_span,
						body: None,
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				});
				return;
			}

			// Consume the body, including the closing `}` brace.
			let (body, mut errs) =
				parse_scope(walker, BRACE_DELIMITER, current_span);
			syntax_errors.append(&mut errs);

			nodes.push(Node {
				ty: NodeTy::While {
					kw: token_span,
					l_paren: l_paren_span,
					cond: cond_nodes,
					r_paren: r_paren_span,
					body: Some(body),
				},
				span: Span::new(
					token_span.start,
					walker.get_previous_span().end,
				),
			});
		}
		Token::Do => {
			let do_kw_span = token_span;
			walker.advance();

			// Consume the opening `{` scope brace.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(SyntaxErr::ExpectedBraceAfterDoKw(
						token_span.next_single_width(),
					));

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: do_kw_span,
					});
					return;
				}
			};
			let (body, span_after_body) = if *current == Token::LBrace {
				walker.advance();

				// Consume the body, including the closing `}` brace.
				let (body, mut errs) =
					parse_scope(walker, BRACE_DELIMITER, current_span);
				syntax_errors.append(&mut errs);

				(Some(body.clone()), body.span.end_zero_width())
			} else if *current == Token::While {
				// We are completely missing the body, but we treat this as "valid" for better error
				// recovery; we still try to parse the condition. We do nothing because the next check
				// deals with the `while` keyword.
				syntax_errors.push(SyntaxErr::ExpectedScopeAfterDoKw(
					token_span.next_single_width(),
				));
				(None, do_kw_span.end_zero_width())
			} else {
				syntax_errors.push(SyntaxErr::ExpectedBraceAfterDoKw(
					token_span.next_single_width(),
				));

				nodes.push(Node {
					ty: NodeTy::Keyword,
					span: do_kw_span,
				});
				return;
			};

			// Consume the `while` keyword.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						walker.get_last_span(),
					));

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: do_kw_span,
					});
					if let Some(body) = body {
						nodes.push(Node {
							span: body.span,
							ty: NodeTy::DelimitedScope(body),
						})
					}
					return;
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
					syntax_errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						span_after_body.next_single_width(),
					));
				}
				None
			} else {
				// Since the position of a missing body and a missing `while` keyword can potentially
				// overlap if both are missing, we avoid this error if we already have the first.
				if let Some(_) = body {
					syntax_errors.push(SyntaxErr::ExpectedWhileKwAfterDoBody(
						span_after_body.next_single_width(),
					));
				}

				nodes.push(Node {
					ty: NodeTy::Keyword,
					span: do_kw_span,
				});
				if let Some(body) = body {
					nodes.push(Node {
						span: body.span,
						ty: NodeTy::DelimitedScope(body),
					})
				}
				return;
			};

			// Consume the opening `(` parenthesis.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					// Since the position of a missing `while` keyword and a missing `(` token can
					// potentially overlap if both are missing, we avoid this error if we already have
					// the first error.
					if let Some(while_kw_span) = while_kw_span {
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterWhileKw(
								while_kw_span.next_single_width(),
							),
						);
					}

					nodes.push(Node {
						ty: NodeTy::Keyword,
						span: do_kw_span,
					});
					if let Some(body) = body {
						nodes.push(Node {
							span: body.span,
							ty: NodeTy::DelimitedScope(body),
						})
					}
					if let Some(while_kw_span) = while_kw_span {
						nodes.push(Node {
							ty: NodeTy::Keyword,
							span: while_kw_span,
						});
					}
					return;
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
					syntax_errors.push(SyntaxErr::ExpectedCondExprAfterWhile(
						Span::new_between(while_kw_span, current_span),
					));
				}

				nodes.push(Node {
					ty: NodeTy::DoWhile {
						do_kw: do_kw_span,
						body,
						while_kw: while_kw_span,
						l_paren: None,
						cond: None,
						r_paren: None,
						semi: Some(current_span),
					},
					span: Span::new(
						token_span.start,
						walker.get_previous_span().end,
					),
				});
				return;
			} else {
				// Since the position of a missing `while` keyword and a missing `(` token can
				// potentially overlap if both are missing, we avoid this error if we already have the
				// first error.
				if let Some(while_kw_span) = while_kw_span {
					syntax_errors.push(SyntaxErr::ExpectedParenAfterWhileKw(
						while_kw_span.next_single_width(),
					));
				}
				None
			};

			// Consume the conditional expression.
			let mut cond_nodes = match expr_parser(
				walker,
				Mode::Default,
				&[Token::RParen, Token::Semi],
			) {
				(Some(e), mut errs) => {
					syntax_errors.append(&mut errs);
					Nodes::new_with(Node {
						span: e.span,
						ty: NodeTy::Expression(e),
					})
				}
				(None, _) => {
					// We found tokens which cannot even start an expression. We loop until we come
					// across either a `)` or a `;`.
					let mut invalid_cond_nodes = Nodes::new();
					'expr_2: loop {
						let (current, current_span) = match walker.peek() {
							Some(t) => (&t.0, t.1),
							None => {
								syntax_errors.push(
									SyntaxErr::ExpectedCondExprAfterWhile(
										walker
											.get_last_span()
											.next_single_width(),
									),
								);

								nodes.push(Node {
									ty: NodeTy::Keyword,
									span: do_kw_span,
								});
								if let Some(body) = body {
									nodes.push(Node {
										span: body.span,
										ty: NodeTy::DelimitedScope(body),
									})
								}
								if let Some(while_kw_span) = while_kw_span {
									nodes.push(Node {
										ty: NodeTy::Keyword,
										span: while_kw_span,
									});
								}
								if let Some(l_paren) = l_paren_span {
									nodes.push(Node {
										ty: NodeTy::Punctuation,
										span: l_paren,
									});
								}
								nodes.append(&mut invalid_cond_nodes.inner);
								return;
							}
						};

						match current {
							Token::RParen => {
								if let Some(l_paren_span) = l_paren_span {
									syntax_errors.push(
										SyntaxErr::ExpectedCondExprAfterWhile(
											Span::new_between(
												l_paren_span,
												current_span,
											),
										),
									);
								} else {
									syntax_errors.push(
										SyntaxErr::ExpectedCondExprAfterWhile(
											current_span
												.previous_single_width(),
										),
									);
								}
								break 'expr_2;
							}
							Token::Semi => {
								if let Some(l_paren_span) = l_paren_span {
									syntax_errors.push(
										SyntaxErr::ExpectedCondExprAfterWhile(
											l_paren_span.next_single_width(),
										),
									);
								} else {
									// We do nothing since the next check deals with the `;` and
									// produces an error for it.
								}
								break 'expr_2;
							}
							_ => {
								invalid_cond_nodes.push(Node {
									ty: NodeTy::Invalid,
									span: current_span,
								});
								walker.advance();
								continue 'expr_2;
							}
						}
					}

					invalid_cond_nodes
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterWhileCond(
								l_paren_span,
								walker.get_last_span().next_single_width(),
							),
						);

						nodes.push(Node {
							ty: NodeTy::DoWhile {
								do_kw: do_kw_span,
								body,
								while_kw: while_kw_span,
								l_paren: l_paren_span,
								cond: if !cond_nodes.is_empty() {
									Some(cond_nodes)
								} else {
									None
								},
								r_paren: None,
								semi: None,
							},
							span: Span::new(
								token_span.start,
								walker.get_previous_span().end,
							),
						});
						return;
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
						syntax_errors.push(
							SyntaxErr::ExpectedParenAfterWhileCond(
								l_paren_span,
								current_span.previous_single_width(),
							),
						);
						break 'r_paren_2 current_span.previous_single_width();
					}
					_ => {
						cond_nodes.push(Node {
							ty: NodeTy::Invalid,
							span: *current_span,
						});
						walker.advance();
						continue 'r_paren_2;
					}
				}
			};

			let cond_nodes = if !cond_nodes.is_empty() {
				Some(cond_nodes)
			} else {
				None
			};

			// Consume the statement-ending `;` semicolon.
			let (current, current_span) = match walker.peek() {
				Some(t) => (&t.0, t.1),
				None => {
					syntax_errors.push(
						SyntaxErr::ExpectedSemiAfterDoWhileStmt(
							walker.get_last_span(),
						),
					);

					nodes.push(Node {
						ty: NodeTy::DoWhile {
							do_kw: do_kw_span,
							body,
							while_kw: while_kw_span,
							l_paren: l_paren_span,
							cond: cond_nodes,
							r_paren: r_paren_span,
							semi: None,
						},
						span: Span::new(
							token_span.start,
							walker.get_previous_span().end,
						),
					});
					return;
				}
			};
			let semi_span = if *current == Token::Semi {
				walker.advance();
				Some(current_span)
			} else {
				// Even though we are missing a necessary token, it still makes sense to just treat
				// this as a "valid" loop for analysis. We do produce an error about the missing token.
				syntax_errors.push(SyntaxErr::ExpectedSemiAfterDoWhileStmt(
					span_after_while_header.next_single_width(),
				));
				None
			};

			nodes.push(Node {
				ty: NodeTy::DoWhile {
					do_kw: do_kw_span,
					body,
					while_kw: while_kw_span,
					l_paren: l_paren_span,
					cond: cond_nodes,
					r_paren: r_paren_span,
					semi: semi_span,
				},
				span: Span::new(
					token_span.start,
					walker.get_previous_span().end,
				),
			});
		}
		Token::Return => {
			let kw_span = token_span;
			walker.advance();

			// Look for the optional return value expression.
			let (return_expr, mut errs) =
				expr_parser(walker, Mode::Default, &[Token::Semi]);
			syntax_errors.append(&mut errs);

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, current_span)) => {
					if *current == Token::Semi {
						let semi_span = *current_span;
						walker.advance();
						Some(semi_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				syntax_errors.push(SyntaxErr::ExpectedSemiAfterReturnKw(
					walker.get_previous_span().next_single_width(),
					return_expr.is_some(),
				));
			}

			nodes.push(Node {
				span: Span::new(
					kw_span.start,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else if let Some(ref return_expr) = return_expr {
						return_expr.span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::Return {
					kw: kw_span,
					value: return_expr,
					semi: semi_span,
				},
			});
		}
		Token::Break => {
			let kw_span = token_span;
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, current_span)) => {
					if *current == Token::Semi {
						let semi_span = *current_span;
						walker.advance();
						Some(semi_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				syntax_errors.push(SyntaxErr::ExpectedSemiAfterBreakKw(
					kw_span.next_single_width(),
				));
			}

			nodes.push(Node {
				span: Span::new(
					kw_span.start,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::Break {
					kw: kw_span,
					semi: semi_span,
				},
			});
		}
		Token::Continue => {
			let kw_span = token_span;
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, current_span)) => {
					if *current == Token::Semi {
						let semi_span = *current_span;
						walker.advance();
						Some(semi_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				syntax_errors.push(SyntaxErr::ExpectedSemiAfterContinueKw(
					kw_span.next_single_width(),
				));
			}

			nodes.push(Node {
				span: Span::new(
					token_span.start,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::Continue {
					kw: kw_span,
					semi: semi_span,
				},
			});
		}
		Token::Discard => {
			let kw_span = token_span;
			walker.advance();

			// Consume the `;` to end the statement.
			let semi_span = match walker.peek() {
				Some((current, current_span)) => {
					if *current == Token::Semi {
						let semi_span = *current_span;
						walker.advance();
						Some(semi_span)
					} else {
						None
					}
				}
				None => None,
			};
			if semi_span.is_none() {
				syntax_errors.push(SyntaxErr::ExpectedSemiAfterDiscardKw(
					kw_span.next_single_width(),
				));
			}

			nodes.push(Node {
				span: Span::new(
					token_span.start,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::Discard {
					kw: kw_span,
					semi: semi_span,
				},
			});
		}
		Token::Directive(_) => {
			walker.advance();
			syntax_errors.push(SyntaxErr::DirectivesNotSupported(token_span));
			// TODO: Implement preprocessor stuff.
			nodes.push(Node {
				ty: NodeTy::Directive,
				span: token_span,
			});
		}
		Token::Struct => {
			walker.advance();

			let (node, mut errs) = parse_struct(walker, qualifiers, token_span);
			syntax_errors.append(&mut errs);

			if let Some(node) = node {
				nodes.push(node);
			}
		}
		Token::Reserved(_) => {
			walker.advance();
			syntax_errors.push(SyntaxErr::FoundIllegalReservedKw(token_span));
			nodes.push(Node {
				ty: NodeTy::Keyword,
				span: token_span,
			});
		}
		Token::Invalid(c) => {
			syntax_errors.push(SyntaxErr::FoundIllegalChar(token_span, *c));
			walker.advance();
			nodes.push(Node {
				ty: NodeTy::Invalid,
				span: token_span,
			});
		}
		Token::RBrace => {
			walker.advance();
			syntax_errors.push(SyntaxErr::FoundLonelyRBrace(token_span));
			nodes.push(Node {
				ty: NodeTy::Punctuation,
				span: token_span,
			});
		}
		_ => {
			if token.is_punctuation_for_stmt() {
				syntax_errors
					.push(SyntaxErr::PunctuationCannotStartStmt(token_span));
				nodes.push(Node {
					ty: NodeTy::Punctuation,
					span: token_span,
				});
			} else {
				// FIXME: Is this branch `unreachable!()`?
				nodes.push(Node {
					ty: NodeTy::Invalid,
					span: token_span,
				});
			}
			walker.advance();
		}
	}

	return;
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
		Some((t, s)) => (t, *s),
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
		Token::RBrace => Some(current_span),
		Token::Case | Token::Default => Some(current_span),
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
	let mut inner_nodes = Vec::new();
	let mut errors = Vec::new();

	let mut ending_span = walker.get_last_span().end_zero_width();
	let mut closing_delim = None;

	'stmts: while let Some(_) = walker.peek() {
		// If we have reached a closing delimiter, break out of the loop and return the parsed statements.
		if let Some(span) = exit_condition(walker, &mut errors, opening_delim) {
			if !span.is_zero_width() {
				closing_delim = Some(span)
			}
			ending_span = span;
			break 'stmts;
		}

		parse_stmt(walker, &mut inner_nodes, &mut errors);
	}

	(
		Scope {
			opening: Some(opening_delim),
			inner: inner_nodes,
			closing: closing_delim,
			span: Span::new(opening_delim.start, ending_span.end),
		},
		errors,
	)
}

/// Parse an if-statement header and body beginning at the current position (the `if`/`else` keyword should already
/// be consumed).
///
/// - `kw_span` - the span of the last keyword; this would be `else` in `else...`, or `if` in `else if...`,
/// - `expects_condition` - whether we are expecting a condition inside of parenthesis; this is set to `false` only
///   when parsing an *else*.
///
/// The `Ok` return value means we were able to parse something (with potential error recovery), and represents the
/// following:
///
/// `(left paren, condition, right paren, body, syntax errors)`.
///
/// The `Err` return value means we encountered an unrecoverable syntax error.
fn parse_if_header_body(
	walker: &mut Walker,
	ty: IfTy,
	expects_condition: bool,
) -> (IfBranch, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	let (l_paren_span, cond_node, r_paren_span) = if expects_condition {
		// Consume the opening `(` parenthesis.
		let (current, current_span) = match walker.peek() {
			Some(t) => (&t.0, t.1),
			None => {
				errors.push(SyntaxErr::ExpectedParenAfterIfKw(
					ty.span().next_single_width(),
				));
				return (
					IfBranch {
						ty,
						l_paren: None,
						cond: None,
						r_paren: None,
						body: None,
						span: ty.span(),
					},
					errors,
				);
			}
		};
		let l_paren_span = if *current == Token::LParen {
			walker.advance();
			Some(current_span)
		} else {
			errors.push(SyntaxErr::ExpectedParenAfterIfKw(
				ty.span().next_single_width(),
			));
			None
		};

		// Consume the conditional expression.
		let cond_node =
			match expr_parser(walker, Mode::Default, &[Token::RParen]) {
				(Some(e), mut errs) => {
					errors.append(&mut errs);
					Some(Node {
						span: e.span,
						ty: NodeTy::Expression(e),
					})
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
									if let Some(l_paren_span) = l_paren_span {
										l_paren_span
									} else {
										ty.span()
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

					None
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
				return (
					IfBranch {
						span: Span::new(
							ty.span().start,
							if let Some(cond_node) = &cond_node {
								cond_node.span.end
							} else if let Some(l_paren) = &l_paren_span {
								l_paren.end
							} else {
								ty.span().end
							},
						),
						ty,
						l_paren: l_paren_span,
						cond: cond_node,
						r_paren: None,
						body: None,
					},
					errors,
				);
			}
		};
		let branch = if *current == Token::RParen {
			walker.advance();
			(l_paren_span, cond_node, Some(current_span))
		} else if *current == Token::LBrace {
			// We don't do anything apart from creating a syntax error since the next check deals
			// with the optional `{`.
			errors.push(SyntaxErr::ExpectedParenAfterIfHeader(
				l_paren_span,
				current_span.previous_single_width(),
			));
			(l_paren_span, cond_node, None)
		} else {
			errors.push(SyntaxErr::ExpectedParenAfterIfHeader(
				l_paren_span,
				Span::new_between(walker.get_previous_span(), current_span),
			));
			return (
				IfBranch {
					span: Span::new(
						ty.span().start,
						if let Some(cond_node) = &cond_node {
							cond_node.span.end
						} else if let Some(l_paren) = &l_paren_span {
							l_paren.end
						} else {
							ty.span().end
						},
					),
					ty,
					l_paren: l_paren_span,
					cond: cond_node,
					r_paren: None,
					body: None,
				},
				errors,
			);
		};

		branch
	} else {
		(None, None, None)
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
			return (
				IfBranch {
					span: Span::new(
						ty.span().start,
						if let Some(r_paren) = &r_paren_span {
							r_paren.end
						} else if let Some(cond_node) = &cond_node {
							cond_node.span.end
						} else if let Some(l_paren) = &l_paren_span {
							l_paren.end
						} else {
							ty.span().end
						},
					),
					ty,
					l_paren: l_paren_span,
					cond: cond_node,
					r_paren: r_paren_span,
					body: None,
				},
				errors,
			);
		}
	};
	let body = if *current == Token::LBrace {
		let l_brace_span = current_span;
		walker.advance();

		// Consume the body, including the closing `}` brace.
		let (body, mut errs) =
			parse_scope(walker, BRACE_DELIMITER, current_span);
		errors.append(&mut errs);

		Some(body)
	} else {
		// Since we are missing a `{`, we are expecting a single statement.
		let mut nodes = Vec::new();
		parse_stmt(walker, &mut nodes, &mut errors);

		if !nodes.is_empty() {
			// Panics: `nodes` is not empty, so `first()` and `last()` will return `Some`.
			let span = Span::new(
				nodes.first().unwrap().span.start,
				nodes.last().unwrap().span.end,
			);
			Some(Scope {
				span,
				opening: None,
				inner: nodes,
				closing: None,
			})
		} else {
			errors.push(SyntaxErr::ExpectedStmtAfterIfHeader(
				// Panics: `r_paren_span` will be `None` if a `{` was encountered, but in that
				// case, the branch above will be chosen instead, and if we didn't encounter a
				// `)`, we will have already quit this parse, so this is always guaranteed to
				// be `Some` if we are in this branch.
				walker.get_previous_span().next_single_width(),
			));
			None
		}
	};

	(
		IfBranch {
			span: Span::new(
				ty.span().start,
				if let Some(body) = &body {
					body.span.end
				} else if let Some(r_paren) = &r_paren_span {
					r_paren.end
				} else if let Some(cond_node) = &cond_node {
					cond_node.span.end
				} else if let Some(l_paren) = &l_paren_span {
					l_paren.end
				} else {
					ty.span().end
				},
			),
			ty,
			l_paren: l_paren_span,
			cond: cond_node,
			r_paren: r_paren_span,
			body,
		},
		errors,
	)
}

/// Parse a switch-statement body beginning at the current position (the `switch (...)` should already be
/// consumed).
///
/// - `l_brace_span` - the span of the opening brace of the body scope.
///
/// The return value represents the following:
///
/// `((case expression, colon, body), syntax errors, closing brace span)`.
///
/// If `case expression` is `None`, that means it is a `default` case.
fn parse_switch_body(
	walker: &mut Walker,
	l_brace_span: Span,
) -> (Vec<SwitchBranch>, Vec<SyntaxErr>, Option<Span>) {
	let mut errors = Vec::new();

	// Check if the body is empty.
	match walker.peek() {
		Some((token, token_span)) => match token {
			Token::RBrace => {
				errors.push(SyntaxErr::FoundEmptySwitchBody(
					Span::new_between(l_brace_span, *token_span),
				));
				return (vec![], errors, Some(*token_span));
			}
			_ => {}
		},
		None => {
			errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
				Some(l_brace_span),
				walker.get_last_span().next_single_width(),
			));
			return (vec![], errors, None);
		}
	}

	// Consume cases until we reach the end of the body.
	let mut cases: Vec<SwitchBranch> = Vec::new();
	let mut r_brace_span = None;
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
				let kw_span = current_span;
				walker.advance();

				// Consume the expression.
				let expr_nodes = match expr_parser(
					walker,
					Mode::Default,
					&[Token::Colon, Token::Case, Token::Default, Token::RBrace],
				) {
					(Some(e), mut errs) => {
						errors.append(&mut errs);
						Some(Nodes::new_with(Node {
							span: e.span,
							ty: NodeTy::Expression(e),
						}))
					}
					(None, _) => {
						// We found tokens which cannot even start an expression. We loop until we come
						// across either `case`, `default` or a `}`.
						errors.push(SyntaxErr::ExpectedExprAfterCaseKw(
							kw_span.next_single_width(),
						));
						let mut invalid_expr_nodes = Nodes::new();
						'expr: loop {
							let (current, current_span) = match walker.peek() {
								Some(t) => t,
								None => {
									errors.push(SyntaxErr::MissingSwitchBodyClosingBrace(
										Some(l_brace_span),
										walker.get_last_span().next_single_width()
									));
									break 'cases;
								}
							};

							match current {
								Token::Colon => {
									// We don't do anything since the next check deals with the `:`.
									break 'expr;
								}
								Token::Case | Token::Default => {
									errors.push(
										SyntaxErr::ExpectedExprAfterCaseKw(
											kw_span.next_single_width(),
										),
									);
									cases.push(SwitchBranch {
										span: Span::new(
											kw_span.start,
											if let Some(node) =
												invalid_expr_nodes.last()
											{
												node.span.end
											} else {
												kw_span.end
											},
										),
										kw: kw_span,
										is_default: false,
										expr: Some(invalid_expr_nodes),
										colon: None,
										body: None,
									});
									continue 'cases;
								}
								Token::RBrace => {
									errors.push(
										SyntaxErr::ExpectedExprAfterCaseKw(
											kw_span.next_single_width(),
										),
									);
									cases.push(SwitchBranch {
										span: Span::new(
											kw_span.start,
											if let Some(node) =
												invalid_expr_nodes.last()
											{
												node.span.end
											} else {
												kw_span.end
											},
										),
										kw: kw_span,
										is_default: false,
										expr: Some(invalid_expr_nodes),
										colon: None,
										body: None,
									});
									r_brace_span = Some(*current_span);
									walker.advance();
									break 'cases;
								}
								_ => {
									invalid_expr_nodes.push(Node {
										ty: NodeTy::Invalid,
										span: *current_span,
									});
									walker.advance();
									continue 'expr;
								}
							}
						}

						Some(invalid_expr_nodes)
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
						if let Some(expr_nodes) = &expr_nodes {
							if let Some(last) = expr_nodes.last() {
								last.span.next_single_width()
							} else {
								kw_span.next_single_width()
							}
						} else {
							kw_span.next_single_width()
						},
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

				cases.push(SwitchBranch {
					span: Span::new(kw_span.start, body.span.end),
					kw: kw_span,
					is_default: false,
					expr: expr_nodes,
					colon: colon_span,
					body: Some(body),
				});
			}
			Token::Default => {
				let kw_span = current_span;
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
						kw_span.next_single_width(),
					));
					kw_span.end_zero_width()
				};

				// Consume the body of the case. This does not consume a `case` or `default` keyword or `}`.
				let (body, mut errs) = parse_scope(
					walker,
					SWITCH_CASE_DELIMITER,
					scope_begin_span,
				);
				errors.append(&mut errs);

				cases.push(SwitchBranch {
					span: Span::new(kw_span.start, body.span.end),
					kw: kw_span,
					is_default: true,
					expr: None,
					colon: colon_span,
					body: Some(body),
				});
			}
			Token::RBrace => {
				r_brace_span = Some(current_span);
				walker.advance();
				break 'cases;
			}
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

	(cases, errors, r_brace_span)
}

/// Continue parsing a function definition or declaration beginning at the current position; (the return type
/// expression, the identifier expression and the opening `(` parenthesis should already be consumed).
///
/// - `return_type` - the function return type,
/// - `ident` - the function identifier,
/// - `qualifiers` - any already parsed qualifiers,
/// - `l_paren_span` - the span of the opening parenthesis of the parameter list which follows the identifier.
fn parse_fn(
	walker: &mut Walker,
	return_type: Expr,
	ident: Ident,
	qualifiers: &Vec<Qualifier>,
	l_paren_span: Span,
) -> (Node, Vec<SyntaxErr>) {
	let mut errors = Vec::new();

	let mut params = List::new();
	let mut r_paren_span = None;

	// If this is set to `true`, that means we have just started parsing the contents after the opening `(`.
	let mut just_started = true;
	// If this is set to `true`, that means we are expecting either a `,` or a `)`.
	let mut just_finished_param = false;

	// Consume tokens until we've reached the closing `)` parenthesis.
	'params: loop {
		let (current, current_span) = match walker.peek() {
			Some((t, s)) => (t, *s),
			None => {
				// Since we are still in this loop, that means we haven't found the closing `)` parenthesis yet,
				// but we've now reached the end of the token stream.

				// Error recovery: we are missing the closing parenthesis.
				let node_end_span = walker.get_last_span();
				errors.push(SyntaxErr::ExpectedParenAtEndOfParamList(
					l_paren_span,
					node_end_span.next_single_width(),
				));
				return (
					Node {
						span: Span::new(
							return_type.span.start,
							node_end_span.end,
						),
						ty: NodeTy::FnDef {
							qualifiers: qualifiers.to_vec(),
							return_type,
							ident,
							l_paren: l_paren_span,
							params,
							r_paren: None,
							semi: None,
						},
					},
					errors,
				);
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
				params.push_separator(current_span);
				walker.advance();
				continue 'params;
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
				r_paren_span = Some(current_span);
				walker.advance();
				break 'params;
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
					Node {
						span: Span::new(
							return_type.span.start,
							current_span.end,
						),
						ty: NodeTy::FnDef {
							qualifiers: qualifiers.to_vec(),
							return_type,
							ident,
							l_paren: l_paren_span,
							params,
							r_paren: None,
							semi: Some(current_span),
						},
					},
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
				break 'params;
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
		let qualifiers = try_parse_qualifier_list(walker, &mut errors);

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

				match Type::parse(&e) {
					Some(_) => e,
					None => {
						errors.push(SyntaxErr::ExpectedType(e.span));
						just_finished_param = true;
						continue 'params;
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
							Token::Comma => continue 'params,
							Token::RParen => {
								// Since we are here, that means we have at least one parameter separated by a
								// comma and we've now come across the closing `)` parenthesis, i.e. `int,)`.
								errors.push(SyntaxErr::MissingTypeInParamList(
									current_span.start_zero_width(),
								));
								r_paren_span = Some(*current_span);
								walker.advance();
								break 'params;
							}
							Token::Semi | Token::LBrace => {
								errors.push(SyntaxErr::MissingTypeInParamList(
									current_span.start_zero_width(),
								));
								continue 'params;
							}
							_ => {
								// We have something like a keyword which is illegal.
								errors.push(SyntaxErr::ExpectedType(
									*current_span,
								));
								walker.advance();
								continue 'params;
							}
						}
					}
					// The first check in the 'param loop deals with reaching the end-of-file.
					None => continue 'params,
				};
			}
		};

		let param_span_start = if let Some(qualifier) = qualifiers.last() {
			qualifier.span.start
		} else {
			type_.span.start
		};

		// Look for an identifier.
		let ident_expr = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			&[Token::LBrace, Token::Semi],
		) {
			(Some(e), mut errs) => {
				errors.append(&mut errs);
				e
			}
			// Identifiers are optional, so if we haven't found one, we move onto the next parameter.
			(None, _) => {
				just_finished_param = true;
				// Note: We need to `peek()` again because we may have found qualifiers.
				match walker.peek() {
					Some((current, current_span)) => {
						params.push_item(Param {
							span: Span::new(param_span_start, type_.span.end),
							qualifiers,
							type_,
							ident: None,
						});

						match current {
							Token::Comma => continue 'params,
							Token::RParen => {
								r_paren_span = Some(*current_span);
								walker.advance();
								break 'params;
							}
							Token::Semi | Token::LBrace => {
								continue 'params;
							}
							_ => {
								// We have something like a keyword which is illegal.
								errors.push(SyntaxErr::ExpectedIdent(
									*current_span,
								));
								walker.advance();
								continue 'params;
							}
						}
					}
					// The first check in the 'param loop deals with reaching the end-of-file.
					None => continue 'params,
				}
			}
		};

		params.push_item(Param {
			span: Span::new(param_span_start, ident_expr.span.end),
			qualifiers,
			type_,
			ident: Some(ident_expr),
		});
		just_finished_param = true;
	}

	// TODO: Analyze list for syntax errors.

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
				Node {
					span: Span::new(
						return_type.span.start,
						walker.get_last_span().end,
					),
					ty: NodeTy::FnDef {
						qualifiers: qualifiers.to_vec(),
						return_type,
						ident,
						l_paren: l_paren_span,
						params,
						r_paren: r_paren_span,
						semi: None,
					},
				},
				errors,
			);
		}
	};
	if *current == Token::Semi {
		walker.advance();
		(
			Node {
				span: Span::new(return_type.span.start, current_span.end),
				ty: NodeTy::FnDef {
					qualifiers: qualifiers.to_vec(),
					return_type,
					ident,
					l_paren: l_paren_span,
					params,
					r_paren: r_paren_span,
					semi: Some(current_span),
				},
			},
			errors,
		)
	} else if *current == Token::LBrace {
		walker.advance();

		// Parse the function body, including the closing `}` brace.
		let (body, mut errs) =
			parse_scope(walker, BRACE_DELIMITER, current_span);
		errors.append(&mut errs);

		(
			Node {
				span: Span::new(return_type.span.start, body.span.end),
				ty: NodeTy::FnDecl {
					qualifiers: qualifiers.to_vec(),
					return_type,
					ident,
					l_paren: l_paren_span,
					params,
					r_paren: r_paren_span,
					body,
				},
			},
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
			Node {
				span: Span::new(
					return_type.span.start,
					walker.get_previous_span().end,
				),
				ty: NodeTy::FnDef {
					qualifiers: qualifiers.to_vec(),
					return_type,
					ident,
					l_paren: l_paren_span,
					params,
					r_paren: r_paren_span,
					semi: None,
				},
			},
			errors,
		)
	}
}

/// Parse a struct definition or declaration beginning at the current position (the `struct` keyword should already
/// be consumed).
///
/// - `qualifiers` - any already parsed qualifiers,
/// - `kw_span` - the span of the `struct` keyword.
fn parse_struct(
	walker: &mut Walker,
	qualifiers: Vec<Qualifier>,
	kw_span: Span,
) -> (Option<Node>, Vec<SyntaxErr>) {
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
			Some(Node {
				ty: NodeTy::StructDef {
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
			Some(Node {
				span: Span::new(kw_span.start, body.span.end),
				ty: NodeTy::StructDecl {
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
	body.inner.iter().for_each(|stmt| match stmt.ty {
		NodeTy::VarDef { .. } | NodeTy::VarDefs { .. } => count += 1,
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
					Some(Node {
						ty: NodeTy::StructDecl {
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
				Some(Node {
					ty: NodeTy::StructDecl {
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
			Some(Node {
				ty: NodeTy::StructDecl {
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
			Some(Node {
				ty: NodeTy::StructDecl {
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

/// Prints the concrete syntax tree.
///
/// This function produces a formatted `String` which contains all of the information of the CST.
#[allow(unused_must_use)]
pub fn print_tree(cst: &Cst) -> String {
	use std::fmt::Write;

	let mut buffer = String::with_capacity(10_000);

	if let Some(last) = cst.last() {
		write!(&mut buffer, "SOURCE_FILE@0..{}", last.span.end);
		for node in cst {
			printing::print_tree_node(node, 1, &mut buffer);
		}
	} else {
		write!(&mut buffer, "SOURCE_FILE@0..0");
	}

	buffer
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
