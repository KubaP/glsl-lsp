//! Parsing functions for GLSL language constructs.

use super::{
	ast,
	ast::*,
	expression::{
		parse_expr, try_parse_new_name, try_parse_new_var_specifiers,
		try_parse_subroutine_type_specifier, try_parse_type_specifier, Mode,
	},
	Ctx, Macro, TokenStreamProvider, Walker,
};
use crate::{
	diag::{
		DiagCtx, ExpectedGrammar, ExprDiag, ForRemoval, ForRemoval2, Found,
		MissingPunct, PreprocDefineDiag, PreprocExtDiag, PreprocLineDiag,
		PreprocVersionDiag, Semantic, StmtDiag, Syntax, Syntax2,
	},
	lexer::{
		preprocessor::{
			ExtensionToken, LineToken, TokenStream as PreprocStream,
			VersionToken,
		},
		OpTy, Token,
	},
	syntax::{SyntaxModifiers, SyntaxToken, SyntaxType},
	Either, Either3, NonEmpty, Span, Spanned,
};

/// Consumes tokens until a beginning of a new statement is reached.
///
/// This function consumes tokens until a keyword which can begin a statement is found, or until a semi-colon is
/// reached (which is consumed). This is used for some instances of error recovery, where no more specific
/// strategies can be employed.
fn seek_next_stmt<'a, P: TokenStreamProvider<'a>>(walker: &mut Walker<'a, P>) {
	loop {
		match walker.peek() {
			Some((token, span)) => {
				if token.can_start_statement() {
					return;
				} else if *token == Token::Semi {
					walker.push_colour(span, SyntaxType::Punctuation);
					walker.advance();
					return;
				} else {
					walker.push_colour(span, SyntaxType::Invalid);
					walker.advance();
					continue;
				}
			}
			None => return,
		}
	}
}

/// Consumes tokens until a beginning of a new statement is reached.
///
/// This function consumes tokens until a keyword which can begin a statement is found, or until a semi-colon is
/// reached (which is consumed). This is used for some instances of error recovery, where no more specific
/// strategies can be employed.
fn seek_next_stmt2<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
) {
	loop {
		match walker.peek() {
			Some((token, span)) => {
				if token.can_start_statement() {
					return;
				} else if *token == Token::Semi {
					walker.push_colour(span, SyntaxType::Punctuation);
					walker.advance();
					return;
				} else {
					match try_parse_type_specifier(
						walker,
						ctx,
						[Token::Semi],
						false,
					) {
						Ok(type_) => {
							walker.tmp_buf = Either3::B(type_);
							return;
						}
						Err(Some(expr)) => {
							walker.tmp_buf = Either3::C(expr);
							return;
						}
						Err(None) => {
							walker.push_colour(span, SyntaxType::Invalid);
							walker.advance();
						}
					}
					continue;
				}
			}
			None => return,
		}
	}
}

/// Invalidates a set of qualifiers.
///
/// This function is used to emit a diagnostic about the use of qualifiers before a statement which doesn't support
/// qualifiers.
fn invalidate_qualifiers<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	qualifiers: Vec<Qualifier>,
) {
	if let Some(q) = qualifiers.last() {
		walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
			item: ExpectedGrammar::AfterQualifiers,
			span: q.span,
		});
	}
}

/// Parses an individual statement at the current position.
pub(super) fn parse_stmt<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
) {
	// Check whether we have recovered from an error and come across a type specifier/expression in the meantime.
	match std::mem::replace(&mut walker.tmp_buf, Either3::A(())) {
		Either3::A(_) => {}
		Either3::B(type_) => {
			parse_type_stmt(walker, ctx, Vec::new(), type_);
			return;
		}
		Either3::C(expr) => {
			parse_expr_stmt(walker, ctx, Vec::new(), expr);
			return;
		}
	}

	let qualifiers = try_parse_qualifiers(walker, ctx);

	let Some((token, token_span)) = walker.get() else {
		return;
	};

	match token {
		Token::LBrace => {
			let l_brace_span = token_span;
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(l_brace_span, SyntaxType::Punctuation);
			walker.advance();
			let scope_handle = ctx.new_temp_scope(l_brace_span, None);
			parse_scope(walker, ctx, brace_scope, l_brace_span);
			let scope = ctx.take_temp_scope(scope_handle);
			ctx.push_node(Node {
				span: l_brace_span,
				ty: NodeTy::Block(scope),
			});
		}
		Token::Semi => {
			let semi_span = token_span;
			walker.push_colour(semi_span, SyntaxType::Punctuation);
			walker.advance();
			match NonEmpty::from_vec(qualifiers) {
				Some(qualifiers) => ctx.push_node(Node {
					span: Span::new(
						qualifiers.first().span.start,
						qualifiers.last().span.end,
					),
					ty: NodeTy::Qualifiers(qualifiers),
				}),
				None => ctx.push_node(Node {
					span: semi_span,
					ty: NodeTy::Empty,
				}),
			};
		}
		Token::Struct => parse_struct(walker, ctx, qualifiers, token_span),
		Token::Directive(stream) => {
			invalidate_qualifiers(walker, qualifiers);
			parse_directive(walker, ctx, stream, token_span);
			walker.advance();
		}
		Token::If => parse_if(walker, ctx, token_span),
		Token::Switch => parse_switch(walker, ctx, token_span),
		Token::For => parse_for_loop(walker, ctx, token_span),
		Token::While => parse_while_loop(walker, ctx, token_span),
		Token::Do => parse_do_while_loop(walker, ctx, token_span),
		Token::Break => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				ctx,
				token_span,
				|| NodeTy::Break,
				|| DiagCtx::BreakStmt,
			)
		}
		Token::Continue => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				ctx,
				token_span,
				|| NodeTy::Continue,
				|| DiagCtx::ContinueStmt,
			);
		}
		Token::Discard => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				ctx,
				token_span,
				|| NodeTy::Discard,
				|| DiagCtx::DiscardStmt,
			);
		}
		Token::Return => {
			invalidate_qualifiers(walker, qualifiers);
			parse_return(walker, ctx, token_span);
		}
		Token::RBrace => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Punctuation);
			walker.push_syntax_diag(Syntax::FoundUnmatchedRBrace(token_span));
			walker.advance();
		}
		Token::Else => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyElseKw(token_span));
			walker.advance();
		}
		Token::Case => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyCaseKw(token_span));
			walker.advance();
		}
		Token::Default => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyDefaultKw(token_span));
			walker.advance();
		}
		Token::Subroutine => {
			parse_subroutine(walker, ctx, token_span, qualifiers);
		}
		Token::Reserved(str) => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Invalid);
			walker.push_syntax_diag(Syntax::FoundReservedKw(token_span, str));
			walker.advance();
		}
		Token::Invalid(c) => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxType::Invalid);
			walker.push_syntax_diag(Syntax::FoundIllegalChar(token_span, c));
			walker.advance();
		}
		_ => {
			// We attempt to parse a type specifier at the current position, and if that fails an expression.
			match try_parse_type_specifier(walker, ctx, [Token::Semi], false) {
				Ok(type_) => {
					parse_type_stmt(walker, ctx, qualifiers, type_);
				}
				Err(Some(expr)) => {
					// We have an expression. If the expression is just a single identifier and we have a `{`
					// next then the closest match is an interface block, otherwise the closest match is an
					// expression statement.
					match (&expr.ty, walker.peek()) {
						(
							ExprTy::Local { name: ident, .. },
							Some((token, token_span)),
						) => {
							match token {
								Token::LBrace => {
									// Since we were attempting to parse a type specifier but found an expression
									// expression consisting of a single ident instead, we know that the last
									// syntax token to be added is for that ident. We also know that, assuming no
									// variable with such a name exists yet, the last unresolved semantic
									// diagnostic would be for this single-ident expression.
									walker
										.highlighting_tokens
										.last_mut()
										.unwrap()
										.ty = SyntaxType::InterfaceBlock;
									let mut remove = false;
									if let Some((diag, _)) =
										ctx.unresolved_diags.last()
									{
										match diag {
											Semantic::UnresolvedVariable {
												var: (var_name, _),
												..
											} => {
												if var_name == &ident.name {
													remove = true;
												}
											}
											_ => {}
										}
									}
									if remove {
										ctx.unresolved_diags.pop();
									}

									let l_brace_span = token_span;
									walker.push_colour(
										l_brace_span,
										SyntaxType::Punctuation,
									);
									walker.advance();
									parse_interface_block(
										walker,
										ctx,
										qualifiers,
										ident.clone(),
										l_brace_span,
									);
									return;
								}
								_ => {}
							}
						}
						(_, _) => {}
					}

					// We have an expression.
					parse_expr_stmt(walker, ctx, qualifiers, expr)
				}
				Err(None) => {
					// We couldn't parse a type specifier nor even an expression, so this cannot be a valid
					// statement.
					invalidate_qualifiers(walker, qualifiers);
					seek_next_stmt2(walker, ctx);
				}
			}
		}
	}
}

/// Parses a scope of statements.
///
/// This function assumes that the opening delimiter is already consumed.
fn parse_scope<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	exit_condition: ScopeEnd<'a, P>,
	opening_span: Span,
) {
	loop {
		// Check if we have reached the closing delimiter.
		if let Some(span) = exit_condition(walker, opening_span) {
			ctx.set_scope_end(span);
			return;
		}
		parse_stmt(walker, ctx);
	}
}

/// A function, which given the `walker`, determines whether to end parsing the current scope of statements and
/// return back to the caller. If this returns `Some`, we have reached the end of the scope. If the span returned
/// is zero-width, that means we have no closing delimiter.
///
/// This also takes a span of the opening delimiter which allows for the creation of a syntax error if the function
/// never encounters the desired ending delimiter.
type ScopeEnd<'a, P> = fn(&mut Walker<'a, P>, Span) -> Option<Span>;

fn brace_scope<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	l_brace_span: Span,
) -> Option<Span> {
	match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RBrace {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => {
			walker.push_nsyntax_diag(Syntax2::MissingPunct {
				char: '}',
				pos: walker.get_last_span().end,
				ctx: DiagCtx::BraceScope,
			});
			Some(walker.get_last_span().end_zero_width())
		}
	}
}
fn switch_case_scope<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	_start_span: Span,
) -> Option<Span> {
	match walker.peek() {
		Some((token, span)) => match token {
			Token::Case | Token::Default | Token::RBrace => Some(span),
			_ => None,
		},
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SwitchExpectedRBrace(
					walker.get_last_span().next_single_width(),
				),
			));
			Some(walker.get_last_span().end_zero_width())
		}
	}
}

/// Tries to parse one or more qualifiers.
///
/// This function makes no assumptions as to what the current token is.
fn try_parse_qualifiers<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
) -> Vec<Qualifier> {
	let mut qualifiers = Vec::new();
	'outer: loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => break,
		};

		match token {
			Token::Const => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Const,
				});
			}
			Token::In => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::In,
				});
			}
			Token::Out => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Out,
				});
			}
			Token::InOut => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::InOut,
				});
			}
			Token::Attribute => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Attribute,
				});
			}
			Token::Uniform => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Uniform,
				});
			}
			Token::Varying => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Varying,
				});
			}
			Token::Buffer => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Buffer,
				});
			}
			Token::Shared => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Shared,
				});
			}
			Token::Centroid => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Centroid,
				});
			}
			Token::Sample => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Sample,
				});
			}
			Token::Patch => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Patch,
				});
			}
			Token::Flat => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Flat,
				});
			}
			Token::Smooth => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Smooth,
				});
			}
			Token::NoPerspective => {
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::NoPerspective,
				});
			}
			Token::HighP => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::HighP,
				});
			}
			Token::MediumP => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::MediumP,
				});
			}
			Token::LowP => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::LowP,
				});
			}
			Token::Invariant => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Invariant,
				});
			}
			Token::Precise => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Precise,
				});
			}
			Token::Coherent => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Coherent,
				});
			}
			Token::Volatile => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Volatile,
				});
			}
			Token::Restrict => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Restrict,
				});
			}
			Token::Readonly => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Readonly,
				});
			}
			Token::Writeonly => {
				walker.push_colour(token_span, SyntaxType::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Writeonly,
				});
			}
			Token::Layout => {
				let kw_span = token_span;
				walker.push_colour(kw_span, SyntaxType::Keyword);
				walker.advance();

				// Consume the `(`.
				let (token, token_span) = match walker.peek() {
					Some(t) => t,
					None => {
						// We don't have any layout contents yet.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedLParenAfterKw(
								kw_span.next_single_width(),
							),
						));
						qualifiers.push(Qualifier {
							span: kw_span,
							ty: QualifierTy::Layout(vec![]),
						});
						break;
					}
				};
				let l_paren_span = if *token == Token::LParen {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();
					token_span
				} else {
					// We don't have any layout contents yet.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::LayoutExpectedLParenAfterKw(
							kw_span.next_single_width(),
						),
					));
					qualifiers.push(Qualifier {
						span: kw_span,
						ty: QualifierTy::Layout(vec![]),
					});
					break;
				};

				// Look for any layouts until we hit a closing `)` parenthesis.
				#[derive(PartialEq)]
				enum Prev {
					None,
					Layout,
					Comma,
					Invalid,
				}
				let mut prev = Prev::None;
				let mut prev_span = l_paren_span;
				let mut layouts = Vec::new();
				let r_paren_span = loop {
					let (token, token_span) = match walker.get() {
						Some(t) => t,
						None => {
							// We have not yet finished parsing the layout list, but we treat this as a valid
							// layout qualifier.
							let span = Span::new(
								kw_span.start,
								walker.get_last_span().end,
							);
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutMissingRParen(
									span.next_single_width(),
								),
							));
							qualifiers.push(Qualifier {
								span,
								ty: QualifierTy::Layout(layouts),
							});
							break 'outer;
						}
					};

					match token {
						Token::Comma => {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							if prev == Prev::Comma {
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::LayoutExpectedLayoutAfterComma(
										Span::new(
											prev_span.start,
											token_span.end,
										),
									),
								));
							} else if prev == Prev::None {
								walker.push_syntax_diag(Syntax::Stmt(StmtDiag::LayoutExpectedLayoutBetweenParenComma(
									Span::new(prev_span.start, token_span.end)
								)));
							}
							prev = Prev::Comma;
							prev_span = token_span;
							continue;
						}
						Token::RParen => {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							break token_span;
						}
						_ => {}
					}

					if prev == Prev::Layout {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedCommaAfterLayout(
								prev_span.next_single_width(),
							),
						));
					}
					let layout_span_start = token_span.start;

					// Consume the layout identifier. This creates a constructor either for a layout which only
					// consists of an identifier, or for a layout which expects an expression.
					let constructor: Either<
						LayoutTy,
						fn(Option<Expr>) -> LayoutTy,
					> = if let Token::Ident(str) = token {
						match str.as_ref() {
							"packed" => Either::Left(LayoutTy::Packed),
							"std140" => Either::Left(LayoutTy::Std140),
							"std430" => Either::Left(LayoutTy::Std430),
							"row_major" => Either::Left(LayoutTy::RowMajor),
							"column_major" => {
								Either::Left(LayoutTy::ColumnMajor)
							}
							"binding" => Either::Right(LayoutTy::Binding),
							"offset" => Either::Right(LayoutTy::Offset),
							"align" => Either::Right(LayoutTy::Align),
							"location" => Either::Right(LayoutTy::Location),
							"component" => Either::Right(LayoutTy::Component),
							"index" => Either::Right(LayoutTy::Index),
							"points" => Either::Left(LayoutTy::Points),
							"lines" => Either::Left(LayoutTy::Lines),
							"isolines" => Either::Left(LayoutTy::Isolines),
							"triangles" => Either::Left(LayoutTy::Triangles),
							"quads" => Either::Left(LayoutTy::Quads),
							"equal_spacing" => {
								Either::Left(LayoutTy::EqualSpacing)
							}
							"fractional_even_spacing" => {
								Either::Left(LayoutTy::FractionalEvenSpacing)
							}
							"fractional_odd_spacing" => {
								Either::Left(LayoutTy::FractionalOddSpacing)
							}
							"cw" => Either::Left(LayoutTy::Clockwise),
							"ccw" => Either::Left(LayoutTy::CounterClockwise),
							"point_mode" => Either::Left(LayoutTy::PointMode),
							"line_adjacency" => {
								Either::Left(LayoutTy::LineAdjacency)
							}
							"triangle_adjacency" => {
								Either::Left(LayoutTy::TriangleAdjacency)
							}
							"invocations" => {
								Either::Right(LayoutTy::Invocations)
							}
							"origin_upper_left" => {
								Either::Left(LayoutTy::OriginUpperLeft)
							}
							"pixel_center_integer" => {
								Either::Left(LayoutTy::PixelCenterInteger)
							}
							"early_fragment_tests" => {
								Either::Left(LayoutTy::EarlyFragmentTests)
							}
							"local_size_x" => {
								Either::Right(LayoutTy::LocalSizeX)
							}
							"local_size_y" => {
								Either::Right(LayoutTy::LocalSizeY)
							}
							"local_size_z" => {
								Either::Right(LayoutTy::LocalSizeZ)
							}
							"xfb_buffer" => Either::Right(LayoutTy::XfbBuffer),
							"xfb_stride" => Either::Right(LayoutTy::XfbStride),
							"xfb_offset" => Either::Right(LayoutTy::XfbOffset),
							"vertices" => Either::Right(LayoutTy::Vertices),
							"line_strip" => Either::Left(LayoutTy::LineStrip),
							"triangle_strip" => {
								Either::Left(LayoutTy::TriangleStrip)
							}
							"max_vertices" => {
								Either::Right(LayoutTy::MaxVertices)
							}
							"stream" => Either::Right(LayoutTy::Stream),
							"depth_any" => Either::Left(LayoutTy::DepthAny),
							"depth_greater" => {
								Either::Left(LayoutTy::DepthGreater)
							}
							"depth_less" => Either::Left(LayoutTy::DepthLess),
							"depth_unchanged" => {
								Either::Left(LayoutTy::DepthUnchanged)
							}
							_ => {
								// We have an identifier that is not a valid layout. We ignore it and continue
								// for the next layout.
								walker.push_colour(
									token_span,
									SyntaxType::UnresolvedIdent,
								);
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::LayoutInvalidIdent(token_span),
								));
								walker.advance();
								prev = Prev::Invalid;
								prev_span = token_span;
								continue;
							}
						}
					} else if let Token::Shared = token {
						Either::Left(LayoutTy::Shared)
					} else {
						// We have a token that is not a valid layout. We ignore it and continue for the next
						// layout.
						walker.push_colour(token_span, SyntaxType::Invalid);
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutInvalidIdent(token_span),
						));
						walker.advance();
						prev = Prev::Invalid;
						prev_span = token_span;
						continue;
					};

					let (constructor, ident_span) = match constructor {
						Either::Left(ty) => {
							walker.push_colour(
								token_span,
								SyntaxType::LayoutQualifier,
							);
							walker.advance();
							layouts.push(Layout {
								span: token_span,
								ty,
							});
							prev = Prev::Layout;
							prev_span = token_span;
							continue;
						}
						Either::Right(constructor) => {
							walker.push_colour(
								token_span,
								SyntaxType::LayoutQualifier,
							);
							walker.advance();
							(constructor, token_span)
						}
					};

					// We have a layout identifier which expects an expression.

					// Consume the `=`.
					let (token, token_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// We are missing the equals sign and we don't know what comes after. We ignore this
							// layout.
							let span = Span::new(
								kw_span.start,
								walker.get_last_span().end,
							);
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutExpectedEqAfterIdent(
									span.next_single_width(),
								),
							));
							qualifiers.push(Qualifier {
								span,
								ty: QualifierTy::Layout(layouts),
							});
							break 'outer;
						}
					};
					let eq_span = if let Token::Op(OpTy::Eq) = token {
						walker.push_colour(token_span, SyntaxType::Operator);
						walker.advance();
						token_span
					} else {
						// We are missing the equals sign and we don't know what comes after. We ignore this
						// layout.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedEqAfterIdent(
								ident_span.next_single_width(),
							),
						));
						prev = Prev::Layout;
						prev_span = ident_span;
						continue;
					};

					// Consume the expression.
					let value_expr = match parse_expr(
						walker,
						ctx,
						Mode::DisallowTopLevelList,
						[Token::RParen],
					) {
						Some(e) => e,
						None => {
							// We are missing the expression.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutExpectedExprAfterEq(
									eq_span.next_single_width(),
								),
							));
							layouts.push(Layout {
								span: Span::new(layout_span_start, eq_span.end),
								ty: constructor(None),
							});
							prev = Prev::Layout;
							prev_span = eq_span;
							continue;
						}
					};

					prev = Prev::Layout;
					prev_span = value_expr.span;
					layouts.push(Layout {
						span: Span::new(layout_span_start, value_expr.span.end),
						ty: constructor(Some(value_expr)),
					});
				};

				qualifiers.push(Qualifier {
					span: Span::new(kw_span.start, r_paren_span.end),
					ty: QualifierTy::Layout(layouts),
				});
				continue;
			}
			_ => break,
		}
		walker.advance();
	}

	qualifiers
}

/// Tries to parse a statement that begins with a type specifier.
///
/// This function takes the type specifier and assumes that nothing afterwards has been consumed.
fn parse_type_stmt<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	qualifiers: Vec<Qualifier>,
	mut type_: Type,
) {
	type_.qualifiers = NonEmpty::from_vec(qualifiers).into();

	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// We expect something after the type specifier.
			walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
				item: ExpectedGrammar::AfterType,
				span: walker.get_last_span(),
			});
			return;
		}
	};

	// Check whether we have a function declaration/definition.
	match token {
		Token::Ident(i) => match walker.lookahead_1() {
			Some(next) => match next.0 {
				Token::LParen => {
					// We have a function declaration/definition.
					let l_paren_span = next.1;
					let ident = Ident {
						name: i.clone(),
						span: token_span,
					};
					walker.push_colour(token_span, SyntaxType::Function);
					walker.advance();
					walker.push_colour(next.1, SyntaxType::Punctuation);
					walker.advance();
					parse_function(walker, ctx, type_, ident, l_paren_span);
					return;
				}
				_ => {}
			},
			None => {}
		},
		_ => {}
	}

	// We don't have a function declaration/definition, so this must be a variable definition.

	let var_specifiers = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		SyntaxType::Variable,
		false,
	) {
		Ok(v) => v,
		Err(e) => match e {
			Either3::A(next_type) => {
				// We have a type specifier, followed by a second type specifier. The best error recovery strategy
				// is to treat the type specifier as a standalone type specifier, and the second type specifier as
				// a future statement.
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::AfterType,
					span: type_.ty_specifier_span,
				});
				ctx.push_node(Node {
					span: Span::new(
						if let Omittable::Some(qualifiers) = &type_.qualifiers {
							qualifiers.first().span.start
						} else {
							type_.ty_specifier_span.start
						},
						type_.ty_specifier_span.end,
					),
					ty: NodeTy::TypeSpecifier(type_),
				});
				walker.tmp_buf = Either3::B(next_type);
				return;
			}
			Either3::B(expr) => {
				// We have a type specifier, followed by a second expression but the second expression
				// isn't one or more new variable specifiers. The best error recovery strategy is to treat
				// the type specifier as a standalone type specifier, and the second expression as an
				// expression statement on its own.
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::AfterType,
					span: type_.ty_specifier_span,
				});
				ctx.push_node(Node {
					span: Span::new(
						if let Omittable::Some(qualifiers) = &type_.qualifiers {
							qualifiers.first().span.start
						} else {
							type_.ty_specifier_span.start
						},
						type_.ty_specifier_span.end,
					),
					ty: NodeTy::TypeSpecifier(type_),
				});
				walker.tmp_buf = Either3::C(expr);
				return;
			}
			Either3::C(_) => {
				seek_next_stmt2(walker, ctx);
				return;
			}
		},
	};

	let last_var_spec_span = var_specifiers.last().span;

	// We expect a `;` after the new variable specifier(s);
	let semi_span = match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::Semi {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				Some(token_span)
			} else {
				None
			}
		}
		None => None,
	};
	ctx.push_new_variables(
		walker,
		type_,
		var_specifiers,
		semi_span.map(|s| s.end).unwrap_or(last_var_spec_span.end),
		(SyntaxType::Variable, SyntaxModifiers::empty()),
	);
	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: last_var_spec_span.end,
			ctx: DiagCtx::VarDef,
		});
		seek_next_stmt2(walker, ctx);
	}
}

/// Creates an expression statement.
///
/// This function takes the expression and assumes that nothing afterwards has been consumed.
fn parse_expr_stmt<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	qualifiers: Vec<Qualifier>,
	expr: Expr,
) {
	// We have an expression potentially preceeded by qualifiers. The best error recovery strategy is to treat the
	// qualifiers as invalid and the expression as an expression statement.
	if !qualifiers.is_empty() {
		walker.push_nsyntax_diag(Syntax2::ForRemoval {
			item: ForRemoval::Qualifiers,
			span: Span::new(
				qualifiers.first().unwrap().span.start,
				qualifiers.last().unwrap().span.end,
			),
			ctx: DiagCtx::ExprStmt,
		});
	}

	// We expect a `;` after an expression to make it into a statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};

	let expr_end = expr.span.end;
	ctx.push_node(Node {
		span: if let Some(semi_span) = semi_span {
			Span::new(expr.span.start, semi_span.end)
		} else {
			expr.span
		},
		ty: NodeTy::Expr(expr),
	});
	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: expr_end,
			ctx: DiagCtx::ExprStmt,
		});
		seek_next_stmt2(walker, ctx);
	}
}

/// Parses a function declaration/definition.
///
/// This function assumes that the return type, ident, and opening parenthesis have been consumed.
fn parse_function<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	return_type: Type,
	ident: Ident,
	l_paren_span: Span,
) {
	// Look for any parameters until we hit a closing `)` parenthesis, or other error recovery exit condition.
	#[derive(PartialEq)]
	enum Prev {
		None,
		Param,
		Comma,
		Invalid,
	}
	let mut prev = Prev::None;
	let mut prev_span = l_paren_span;
	let mut params = Vec::new();
	let mut prev_type: Option<Type> = None;
	let params_end_pos = loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We expect a `)` to finish the parameter list. Since we know there's nothing else left, the best
				// error recovery strategy is to treat this as a function declaration. (We are also technically
				// missing the `;` but two overlapping errors should be avoided).
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ')',
					pos: prev_span.end,
					ctx: DiagCtx::ParamList,
				});
				ctx.push_new_function_decl(
					walker,
					return_type,
					ident,
					params,
					walker.get_last_span().end,
				);
				return;
			}
		};

		if prev_type.is_none() {
			match token {
				Token::Comma => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();
					if prev == Prev::Comma {
						walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
							item: ExpectedGrammar::Parameter,
							span: prev_span,
						});
					} else if prev == Prev::None {
						walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
							item: ExpectedGrammar::Parameter,
							span: l_paren_span,
						});
					}
					prev = Prev::Comma;
					prev_span = token_span;
					continue;
				}
				Token::RParen => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();
					if prev == Prev::Comma {
						walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
							item: ExpectedGrammar::Parameter,
							span: prev_span,
						});
					}
					break token_span.end;
				}
				Token::Semi => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();

					// Although we expect a `)` to close the parameter list, since we've encountered a `;` the best
					// error recovery strategy is to allow a function declaration anyway.
					walker.push_nsyntax_diag(Syntax2::MissingPunct {
						char: ')',
						pos: prev_span.end,
						ctx: DiagCtx::ParamList,
					});
					ctx.push_new_function_decl(
						walker,
						return_type,
						ident,
						params,
						token_span.end,
					);
					return;
				}
				Token::LBrace => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					// We don't advance because the next check after this loop checks for a `{`.

					// Although we expect a `)` to close the parameter list, since we've encountered a `{` the best
					// error recovery strategy is to continue on anyway (to a function definition).
					walker.push_nsyntax_diag(Syntax2::MissingPunct {
						char: ')',
						pos: prev_span.end,
						ctx: DiagCtx::ParamList,
					});
					break token_span.end;
				}
				_ => {}
			}
		}

		if prev == Prev::Param {
			// We have a parameter after a parameter, though we expect a separating `,` between.
			walker.push_nsyntax_diag(Syntax2::MissingPunct {
				char: ',',
				pos: prev_span.end,
				ctx: DiagCtx::ParamList,
			});
		}
		let param_span_start = if let Some(prev_type) = &prev_type {
			prev_type.span_start()
		} else {
			token_span.start
		};

		let qualifiers = if prev_type.is_none() {
			try_parse_qualifiers(walker, ctx)
		} else {
			Vec::new()
		};

		// We expect a type specifier.
		let mut type_ = if let Some(t) = prev_type.take() {
			t
		} else {
			match try_parse_type_specifier(
				walker,
				ctx,
				[Token::Semi, Token::LBrace],
				true,
			) {
				Ok(type_) => type_,
				Err(Some(expr)) => {
					// We couldn't parse a type specifier. The best error recovery strategy is to ignore this and
					// continue looking for the next parameter.
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::ParamList,
					});
					prev = Prev::Invalid;
					prev_span = Span::new(param_span_start, expr.span.end);
					continue;
				}
				Err(None) => {
					// We immediately have a token that is not an expression. The best error recovery strategy is
					// to ignore this and loop until we hit something recognizable.
					let end_pos = loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::Comma
									|| *token == Token::RParen || *token
									== Token::Semi || *token == Token::LBrace
								{
									break span.start;
								} else {
									walker.advance();
									continue;
								}
							}
							None => break walker.get_last_span().end,
						}
					};
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Something,
						span: Span::new(param_span_start, end_pos),
						ctx: DiagCtx::ParamList,
					});
					prev = Prev::Invalid;
					prev_span = token_span;
					continue;
				}
			}
		};

		// We may have an optional new variable specifier.
		let mut vars = match try_parse_new_var_specifiers(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
			SyntaxType::Parameter,
			true,
		) {
			Ok(v) => v,
			Err(e) => match e {
				Either3::A(next_type) => {
					// We have a type specifier followed by a type specifier. The best error recovery strategy is
					// to treat the first type specifier as an anonymous parameter, and the second as the beginning
					// of a new parameter.
					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					prev_type = Some(next_type);
					continue;
				}
				Either3::B(expr) => {
					// We have an expression after the type specifier, but the expression can't be parsed as a new
					// variable specifier. The best error recovery strategy is to treat the type specifier as an
					// anonymous parameter, and the second expression as invalid.
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::ParamList,
					});

					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					params.push(Param {
						span: Span::new(
							param_span_start,
							type_.ty_specifier_span.end,
						),
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
				Either3::C(_) => {
					// We have a type specifier followed by something that can't even be parsed into an expression.
					// The best error recovery strategy is to treat the type specifier as an anonymous parameter,
					// and continue looking. It's possible that we hit a `,` or `)`, in which case it would be
					// erreneous to produce a diagnostic.
					let start_pos = walker.get().unwrap().1.start;
					let end_pos = loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::Comma
									|| *token == Token::RParen || *token
									== Token::Semi || *token == Token::LBrace
								{
									break span.start;
								} else {
									walker.advance();
									continue;
								}
							}
							None => break walker.get_last_span().end,
						}
					};
					if start_pos != end_pos {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::Something,
							span: Span::new(start_pos, end_pos),
							ctx: DiagCtx::ParamList,
						});
					}

					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
			},
		}; // FIXME: Copy changes from this into `subroutine_function` parser

		// Panic: `vars` has a length of exactly 1
		let super::NewVarSpecifier {
			ident,
			arr,
			eq_span,
			init_expr,
			span: var_span,
		} = vars.destruct();

		// New variable specifiers inside parameter lists cannot have an initialization expression.
		match (eq_span, init_expr) {
			(Some(span), None) => {
				walker.push_nsyntax_diag(Syntax2::ForRemoval {
					item: ForRemoval::VarInitialization,
					span,
					ctx: DiagCtx::ParamList,
				})
			}
			(Some(begin), Some(end)) => {
				walker.push_nsyntax_diag(Syntax2::ForRemoval {
					item: ForRemoval::VarInitialization,
					span: Span::new(begin.start, end.span.end),
					ctx: DiagCtx::ParamList,
				})
			}
			_ => {}
		}

		type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
		let type_ = combine_type_with_arr(type_, arr);
		let param_span = Span::new(param_span_start, var_span.end);
		params.push(Param {
			span: param_span,
			type_,
			ident: Omittable::Some(ident),
		});
		prev = Prev::Param;
		prev_span = param_span;
		prev_type = None;
	};

	// We expect a `;` for a declaration, or a `{` for a definition.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => match token {
			Token::Semi => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				Some(token_span)
			}
			Token::LBrace => {
				// We have a function definition.
				let l_brace_span = token_span;
				walker.push_colour(l_brace_span, SyntaxType::Punctuation);
				walker.advance();

				// Parse the contents of the body.
				let scope_handle =
					ctx.new_temp_scope(l_brace_span, Some(&params));
				parse_scope(walker, ctx, brace_scope, l_brace_span);
				let body = ctx.replace_temp_scope(scope_handle);

				let end_pos = body.span.end;
				ctx.push_new_function_def(
					walker,
					scope_handle,
					return_type,
					ident,
					params,
					body,
					end_pos,
				);
				return;
			}
			_ => None,
		},
		None => None,
	};

	// We have a function declaration.

	let end_pos = if let Some(span) = semi_span {
		span.end
	} else {
		params_end_pos
	};

	ctx.push_new_function_decl(walker, return_type, ident, params, end_pos);

	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: params_end_pos,
			ctx: DiagCtx::FnDecl,
		});
		seek_next_stmt2(walker, ctx);
	}
}

/// Parses a subroutine type declaration, subroutine associated function definition, or a subroutine uniform
/// definition.
///
/// This function assumes that the `subroutine` keyword is not yet consumed.
fn parse_subroutine<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	subroutine_kw_span: Span,
	mut qualifiers: Vec<Qualifier>,
) {
	let start_pos = if let Some(q) = qualifiers.first() {
		q.span.start
	} else {
		subroutine_kw_span.start
	};
	walker.push_colour(subroutine_kw_span, SyntaxType::Keyword);
	walker.advance();

	let is_uniform_before_subroutine = qualifiers
		.iter()
		.find(|q| q.ty == QualifierTy::Uniform)
		.is_some();

	// An association list, if present, will come immediately after the `subroutine` keyword.
	let association_list = match walker.peek() {
		Some((token, token_span)) => match token {
			Token::LParen => {
				let l_paren_span = token_span;
				walker.push_colour(l_paren_span, SyntaxType::Punctuation);
				walker.advance();

				// Look for any subroutine identifiers until we hit a closing `)` parenthesis.
				#[derive(PartialEq)]
				enum Prev {
					None,
					Ident,
					Comma,
					Invalid,
				}
				let mut prev = Prev::None;
				let mut prev_span = l_paren_span;
				let mut associations = Vec::new();
				let r_paren_span = loop {
					let (token, token_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// We expect a `)` to finish the association list. There is no error recovery strategy
							// because there are multiple options possible after this.
							walker.push_nsyntax_diag(Syntax2::MissingPunct {
								char: ')',
								pos: prev_span.end,
								ctx: DiagCtx::AssociationList,
							});
							return;
						}
					};

					match token {
						Token::Comma => {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							if prev == Prev::Comma {
								walker.push_nsyntax_diag(
									Syntax2::ExpectedGrammar {
										item:
											ExpectedGrammar::SubroutineTypename,
										span: prev_span,
									},
								);
							} else if prev == Prev::None {
								walker.push_nsyntax_diag(
									Syntax2::ExpectedGrammar {
										item:
											ExpectedGrammar::SubroutineTypename,
										span: l_paren_span,
									},
								);
							}
							prev = Prev::Comma;
							prev_span = token_span;
							continue;
						}
						Token::RParen => {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							if prev == Prev::Comma {
								walker.push_nsyntax_diag(
									Syntax2::ExpectedGrammar {
										item: ExpectedGrammar::Parameter,
										span: prev_span,
									},
								);
							}
							break token_span;
						}
						Token::Ident(str) => {
							let subroutine_type_handle = ctx
								.resolve_subroutine_type(&Ident {
									name: str.clone(),
									span: token_span,
								});
							associations.push((
								subroutine_type_handle,
								Ident {
									name: str.to_owned(),
									span: token_span,
								},
							));
							walker.push_colour(
								token_span,
								if subroutine_type_handle.is_resolved() {
									SyntaxType::SubroutineType
								} else {
									SyntaxType::UnresolvedIdent
								},
							);
							walker.advance();
							if prev == Prev::Ident {
								walker.push_nsyntax_diag(
									Syntax2::MissingPunct {
										char: ',',
										pos: prev_span.end,
										ctx: DiagCtx::AssociationList,
									},
								);
							}
							prev = Prev::Ident;
							prev_span = token_span;
							continue;
						}
						Token::Semi => {
							// We expect a `)` to finish the parameter list, (and stuff afterwards), but since we
							// hit a `;` we just abort creating anything and return out. There is no error recovery
							// strategy because there are multiple options possible after this.
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							walker.push_nsyntax_diag(Syntax2::MissingPunct {
								char: ')',
								pos: prev_span.end,
								ctx: DiagCtx::AssociationList,
							});
							return;
						}
						_ => {
							// We immediately have a token that is not an identifier. The best error recovery
							// strategy is to ignore this and loop until we hit something recognizable.
							let end_span = loop {
								match walker.peek() {
									Some((token, span)) => {
										if *token == Token::Comma
											|| *token == Token::RParen || *token
											== Token::Semi || *token
											== Token::LBrace
										{
											break span;
										} else {
											walker.advance();
											continue;
										}
									}
									None => break walker.get_last_span(),
								}
							};
							walker.push_nsyntax_diag(Syntax2::ForRemoval {
								item: ForRemoval::Something,
								span: Span::new(
									l_paren_span.start,
									end_span.end,
								),
								ctx: DiagCtx::AssociationList,
							});
							walker.push_colour(token_span, SyntaxType::Invalid);
							walker.advance();
							prev = Prev::Invalid;
							prev_span = token_span;
							continue;
						}
					}
				};

				Some((associations, l_paren_span, r_paren_span))
			}
			_ => None,
		},
		None => {
			// Even if we don't have an association list, we still expect something after the subroutine/qualifiers
			// to make a valid statement.
			walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
				item: ExpectedGrammar::AfterSubroutineQualifiers,
				span: subroutine_kw_span,
			});
			return;
		}
	};

	// We can have qualifiers after the `subroutine` keyword, though only for subroutine uniform definitions.
	let qualifiers_end_pos = if let Some(q) = qualifiers.last() {
		q.span.end
	} else {
		subroutine_kw_span.end
	};
	let mut next_qualifiers = try_parse_qualifiers(walker, ctx);
	let qualifiers_end_pos = if let Some(q) = next_qualifiers.last() {
		q.span.end
	} else {
		qualifiers_end_pos
	};
	qualifiers.append(&mut next_qualifiers);
	let uniform_kw_span = qualifiers
		.iter()
		.find(|q| q.ty == QualifierTy::Uniform)
		.map(|q| q.span);

	parse_non_kw_stmt_for_subroutine(
		walker,
		ctx,
		qualifiers,
		association_list,
		start_pos,
		uniform_kw_span,
		subroutine_kw_span,
		is_uniform_before_subroutine,
		qualifiers_end_pos,
	);
}

/// Parses an interface block.
///
/// This function assumes that the qualifiers, identifier, and opening brace have been consumed.
///
/// # Invariants
/// `qualifiers` is not empty.
fn parse_interface_block<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	qualifiers: Vec<Qualifier>,
	name: Ident,
	l_brace_span: Span,
) {
	let (start_pos, qualifiers) = if let Some(q) = qualifiers.first() {
		(q.span.start, Some(NonEmpty::from_vec(qualifiers).unwrap()))
	} else {
		// We expect certain qualifiers before an interface block.
		walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
			item: ExpectedGrammar::QualifierBeforeInterfaceBlock,
			span: name.span,
		});
		(name.span.start, None)
	};

	// For perf optimization, see end of function.
	let syntax_vec_len = walker.highlighting_tokens.len();

	// We expect field definitions inside the body.
	let mut fields = Vec::new();
	let mut prev_type = None;
	let r_brace_span = loop {
		match walker.get() {
			Some((token, token_span)) => match token {
				Token::RBrace => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();
					break token_span;
				}
				_ => {}
			},
			None => {
				// We expect a `}` to finish the interface body. Since we know there's nothing else left, the best
				// error recovery strategy is to treat this as a valid interface definition (with no instances).
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: '}',
					pos: walker.get_last_span().end,
					ctx: DiagCtx::InterfaceBlockDef,
				});
				ctx.push_new_interface(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					walker.get_last_span().end,
				);
				return;
			}
		}

		match try_parse_var_def(walker, ctx, SyntaxType::Field, prev_type) {
			Ok((type_, mut var_specifiers, semi_span)) => {
				// There can only be one variable specifier per field.
				let super::NewVarSpecifier {
					ident,
					arr,
					eq_span,
					init_expr,
					span,
				} = if var_specifiers.len().get() == 1 {
					var_specifiers.destruct()
				} else {
					let first = var_specifiers.remove(0).unwrap();
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::MultipleVarSpecifiers,
						span: Span::new(
							// We want to include the comma after the first specifier:
							// int i, j;
							//      ~~~
							first.span.end,
							var_specifiers.last().span.end,
						),
						ctx: DiagCtx::InterfaceField,
					});
					first
				};

				match (eq_span, init_expr) {
					(Some(start), Some(end)) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::VarInitialization,
							span: Span::new(start.start, end.span.end),
							ctx: DiagCtx::InterfaceField,
						})
					}
					(Some(span), _) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::VarInitialization,
							span,
							ctx: DiagCtx::InterfaceField,
						})
					}
					_ => {}
				}

				fields.push((combine_type_with_arr(type_, arr), Some(ident)));

				if semi_span.is_none() {
					if eq_span.is_none() {
						// Prevent multiple overlapping errors.
						walker.push_nsyntax_diag(Syntax2::MissingPunct {
							char: ';',
							pos: span.end,
							ctx: DiagCtx::InterfaceField,
						});
					}
					// Loop until we hit something recognizable.
					loop {
						match walker.get() {
							Some((token, token_span)) => match token {
								Token::Semi => {
									walker.push_colour(
										token_span,
										SyntaxType::Punctuation,
									);
									walker.advance();
									break;
								}
								_ => {
									walker.push_colour(
										token_span,
										SyntaxType::Invalid,
									);
									walker.advance();
								}
							},
							None => break,
						}
					}
				}
			}
			Err(Either::Left((qualifiers, expr))) => {
				// We potentially have qualifiers, potentially followed by an expression.
				if !qualifiers.is_empty() {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::AfterQualifiers,
						span: qualifiers.last().unwrap().span,
					});
				}
				if let Some(expr) = expr {
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::InterfaceField,
					});
				}
				// Loop until we hit something recognizable.
				loop {
					match walker.get() {
						Some((token, token_span)) => match token {
							Token::Semi => {
								walker.push_colour(
									token_span,
									SyntaxType::Punctuation,
								);
								walker.advance();
								break;
							}
							_ => {
								walker.push_colour(
									token_span,
									SyntaxType::Invalid,
								);
								walker.advance();
							}
						},
						None => break,
					}
				}
			}
			Err(Either::Right((qualifiers, type_, e))) => {
				// We potentially have qualifiers, followed by a type specifier, then potentially folowed by
				// another type specifier or an expression.
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::AfterType,
					span: type_.ty_specifier_span,
				});
				match e {
					Either3::A(next_type) => {
						prev_type = Some(next_type);
						continue;
					}
					Either3::B(expr) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::Expr,
							span: expr.span,
							ctx: DiagCtx::InterfaceField,
						});
					}
					Either3::C(_) => {}
				}
				// Loop until we hit something recognizable.
				loop {
					match walker.get() {
						Some((token, token_span)) => match token {
							Token::Semi => {
								walker.push_colour(
									token_span,
									SyntaxType::Punctuation,
								);
								walker.advance();
								break;
							}
							_ => {
								walker.push_colour(
									token_span,
									SyntaxType::Invalid,
								);
								walker.advance();
							}
						},
						None => break,
					}
				}
			}
		}

		prev_type = None;
	};

	if fields.is_empty() {
		// We expect fields inside the body.
		walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
			item: ExpectedGrammar::AtLeastOneInterfaceField,
			span: l_brace_span,
		});
	}

	// We may have optional instance variable specifiers.
	let instances = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		SyntaxType::Variable,
		false,
	) {
		Ok(vars) => vars.into_vec(),
		Err(e) => match e {
			Either3::A(type_) => {
				// We have an interface body followed by a type specifier. The best error recovery strategy is to
				// treat the current state as an interface block definition, and the type specifier as a new
				// statement.
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ';',
					pos: r_brace_span.end,
					ctx: DiagCtx::InterfaceBlockDef,
				});
				ctx.push_new_interface(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					r_brace_span.end,
				);
				walker.tmp_buf = Either3::B(type_);
				return;
			}
			Either3::B(expr) => {
				// We have an interface body followed by an expression, but the expression isn't one or more new
				// variable specifiers. The best error recovery strategy is to treat the current state as an
				// interface block definition, and the second expression as an expression statement on its own.
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ';',
					pos: r_brace_span.end,
					ctx: DiagCtx::InterfaceBlockDef,
				});
				ctx.push_new_interface(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					r_brace_span.end,
				);
				walker.tmp_buf = Either3::C(expr);
				return;
			}
			Either3::C(_) => Vec::new(),
		},
	};

	// We expect a `;` at the end.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};

	let end_pos = if let Some(semi_span) = semi_span {
		semi_span.end
	} else {
		if let Some(var) = instances.last() {
			var.span.end
		} else {
			r_brace_span.end
		}
	};

	// If we have one or more instances, the interface block effectively acts as a struct and all the fields are
	// namespaced within the instances. However, if we don't have any instances, then the "fields" are actually
	// individual global variables. If so, we need to modify the syntax highlighting information because by default
	// the fields are highlighting like struct fields.
	let end_pos = if !instances.is_empty() {
		let mut i = 0;
		// Panic: We record the length of the vector before parsing the body and optional instance new variable
		// specifiers. It is impossible for the length to have shrunk in the meantime.
		for token in walker.highlighting_tokens[syntax_vec_len..].iter_mut() {
			if token.span == instances[i].ident.span {
				token.ty = SyntaxType::Variable;
				i += 1;
				if instances.len() == i {
					break;
				}
			}
		}
		instances.last().unwrap().span.end
	} else {
		r_brace_span.end
	};

	ctx.push_new_interface(
		walker, start_pos, qualifiers, name, fields, instances, end_pos,
	);

	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: end_pos,
			ctx: DiagCtx::InterfaceBlockDef,
		});
		seek_next_stmt(walker);
	}
}

/// Parses a struct declaration/definition.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_struct<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	qualifiers: Vec<Qualifier>,
	kw_span: Span,
) {
	let (start_pos, qualifiers) = if let Some(q) = qualifiers.first() {
		(
			q.span.start,
			Omittable::Some(NonEmpty::from_vec(qualifiers).unwrap()),
		)
	} else {
		(kw_span.start, Omittable::None)
	};
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// We expect a name.
	let name = match try_parse_new_name(
		walker,
		ctx,
		[Token::LBrace, Token::Semi],
		SyntaxType::Struct,
	) {
		Ok(name) => name,
		Err(expr) => {
			// We expect a name. In the current state, there is no sensible recovery strategy, so we abort.
			walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
				item: ExpectedGrammar::AfterStructKw,
				span: kw_span,
			});
			if let Some(expr) = expr {
				walker.tmp_buf = Either3::C(expr);
			}
			return;
		}
	};

	// We expect a `{` to open the body.
	let l_brace_span = match walker.peek() {
		Some((token, token_span)) => match token {
			Token::LBrace => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				token_span
			}
			Token::Semi => {
				// We have a struct declaration. This is not legal, but for better error recovery we allow this.
				walker.push_nsyntax_diag(Syntax2::ForRemoval {
					item: ForRemoval::StructDecl,
					span: Span::new(start_pos, token_span.end),
					ctx: DiagCtx::StructDef,
				});
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				// We don't create a symbol because a struct declaration is not legal.
				ctx.push_node(Node {
					span: Span::new(start_pos, token_span.end),
					ty: NodeTy::StructDecl { qualifiers, name },
				});
				return;
			}
			_ => {
				// We could treat this as a struct declaration for error recovery, but since a struct declaration
				// is not a valid statement in the first place, it would create more confusion, so the best choice
				// is to abort.
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::StructBody,
					span: name.span,
				});
				return;
			}
		},
		None => {
			// We could treat this as a struct declaration for error recovery, but since a struct declaration is
			// not a valid statement in the first place, it would create more confusion, so the best choice is to
			// abort.
			walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
				item: ExpectedGrammar::StructBody,
				span: name.span,
			});
			return;
		}
	};

	// We expect field definitions inside the body.
	let mut fields = Vec::new();
	let mut prev_type = None;
	let r_brace_span = loop {
		match walker.get() {
			Some((token, token_span)) => match token {
				Token::RBrace => {
					walker.push_colour(token_span, SyntaxType::Punctuation);
					walker.advance();
					break token_span;
				}
				_ => {}
			},
			None => {
				// We expect a `}` to finish the struct body. Since we know there's nothing else left, the best
				// error recovery strategy is to treat this as a valid struct definition (with no instances).
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: '}',
					pos: walker.get_last_span().end,
					ctx: DiagCtx::StructDef,
				});
				ctx.push_new_struct(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					walker.get_last_span().end,
				);
				return;
			}
		}

		match try_parse_var_def(walker, ctx, SyntaxType::Field, prev_type) {
			Ok((type_, mut var_specifiers, semi_span)) => {
				// There can only be one variable specifier per field.
				let super::NewVarSpecifier {
					ident,
					arr,
					eq_span,
					init_expr,
					span,
				} = if var_specifiers.len().get() == 1 {
					var_specifiers.destruct()
				} else {
					let first = var_specifiers.remove(0).unwrap();
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::MultipleVarSpecifiers,
						span: Span::new(
							// We want to include the comma after the first specifier:
							// int i, j;
							//      ~~~
							first.span.end,
							var_specifiers.last().span.end,
						),
						ctx: DiagCtx::StructField,
					});
					first
				};

				match (eq_span, init_expr) {
					(Some(start), Some(end)) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::VarInitialization,
							span: Span::new(start.start, end.span.end),
							ctx: DiagCtx::StructField,
						})
					}
					(Some(span), _) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::VarInitialization,
							span,
							ctx: DiagCtx::StructField,
						})
					}
					_ => {}
				}

				fields.push((combine_type_with_arr(type_, arr), Some(ident)));

				if semi_span.is_none() {
					if eq_span.is_none() {
						// Prevent multiple overlapping errors.
						walker.push_nsyntax_diag(Syntax2::MissingPunct {
							char: ';',
							pos: span.end,
							ctx: DiagCtx::StructField,
						});
					}
					// Loop until we hit something recognizable.
					loop {
						match walker.get() {
							Some((token, token_span)) => match token {
								Token::Semi => {
									walker.push_colour(
										token_span,
										SyntaxType::Punctuation,
									);
									walker.advance();
									break;
								}
								_ => {
									walker.push_colour(
										token_span,
										SyntaxType::Invalid,
									);
									walker.advance();
								}
							},
							None => break,
						}
					}
				}
			}
			Err(Either::Left((qualifiers, expr))) => {
				// We potentially have qualifiers, potentially followed by an expression.
				if !qualifiers.is_empty() {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::AfterQualifiers,
						span: qualifiers.last().unwrap().span,
					});
				}
				if let Some(expr) = expr {
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::StructField,
					});
				}
				// Loop until we hit something recognizable.
				loop {
					match walker.get() {
						Some((token, token_span)) => match token {
							Token::Semi => {
								walker.push_colour(
									token_span,
									SyntaxType::Punctuation,
								);
								walker.advance();
								break;
							}
							_ => {
								walker.push_colour(
									token_span,
									SyntaxType::Invalid,
								);
								walker.advance();
							}
						},
						None => break,
					}
				}
			}
			Err(Either::Right((qualifiers, type_, e))) => {
				// We potentially have qualifiers, followed by a type specifier, then potentially folowed by
				// another type specifier or an expression.
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::AfterType,
					span: type_.ty_specifier_span,
				});
				match e {
					Either3::A(next_type) => {
						prev_type = Some(next_type);
						continue;
					}
					Either3::B(expr) => {
						walker.push_nsyntax_diag(Syntax2::ForRemoval {
							item: ForRemoval::Expr,
							span: expr.span,
							ctx: DiagCtx::StructField,
						});
					}
					Either3::C(_) => {}
				}
				// Loop until we hit something recognizable.
				loop {
					match walker.get() {
						Some((token, token_span)) => match token {
							Token::Semi => {
								walker.push_colour(
									token_span,
									SyntaxType::Punctuation,
								);
								walker.advance();
								break;
							}
							_ => {
								walker.push_colour(
									token_span,
									SyntaxType::Invalid,
								);
								walker.advance();
							}
						},
						None => break,
					}
				}
			}
		}

		prev_type = None;
	};

	if fields.is_empty() {
		// We expect fields inside the body.
		walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
			item: ExpectedGrammar::AtLeastOneStructField,
			span: l_brace_span,
		});
	}

	// We may have optional instance variable specifiers.
	let instances = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		SyntaxType::Variable,
		false,
	) {
		Ok(vars) => vars.into_vec(),
		Err(e) => match e {
			Either3::A(type_) => {
				// We have a struct body followed by a type specifier. The best error recovery strategy is to treat
				// the current state as a struct definition, and the type specifier as a new statement.
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ';',
					pos: r_brace_span.end,
					ctx: DiagCtx::StructDef,
				});
				ctx.push_new_struct(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					r_brace_span.end,
				);
				walker.tmp_buf = Either3::B(type_);
				return;
			}
			Either3::B(expr) => {
				// We have a struct body followed by an expression, but the expression isn't one or more new
				// variable specifiers. The best error recovery strategy is to treat the current state as a struct
				// definition, and the second expression as an expression statement on its own.
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ';',
					pos: r_brace_span.end,
					ctx: DiagCtx::StructDef,
				});
				ctx.push_new_struct(
					walker,
					start_pos,
					qualifiers,
					name,
					fields,
					Vec::new(),
					r_brace_span.end,
				);
				walker.tmp_buf = Either3::C(expr);
				return;
			}
			Either3::C(_) => Vec::new(),
		},
	};

	// We expect a `;` at the end.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};

	let end_pos = if let Some(semi_span) = semi_span {
		semi_span.end
	} else {
		if let Some(var) = instances.last() {
			var.span.end
		} else {
			r_brace_span.end
		}
	};

	ctx.push_new_struct(
		walker, start_pos, qualifiers, name, fields, instances, end_pos,
	);

	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: end_pos,
			ctx: DiagCtx::StructDef,
		});
		seek_next_stmt(walker);
	}
}

/// Parses an if statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_if<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	let mut branches = Vec::new();
	let mut first_iter = true;
	// On the first iteration of this loop, the current token is guaranteed to be `Token::If`.
	loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				ctx.push_node(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::If(branches),
				});
				return;
			}
		};

		let else_kw_span = if *token != Token::Else && !first_iter {
			// We've found a token that is not `else`, which means we've finished the current if statement.
			ctx.push_node(Node {
				span: Span::new(
					kw_span.start,
					if let Some(branch) = branches.last() {
						branch.span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::If(branches),
			});
			return;
		} else if *token == Token::If && first_iter {
			// In the first iteration this variable is ignored. This is just to prevent divergence of branches
			// which would require a different overall parsing algorithm.
			token_span
		} else {
			// Consume the `else` keyword.
			walker.push_colour(token_span, SyntaxType::Keyword);
			walker.advance();
			token_span
		};

		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have an else keyword followed by nothing.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::IfExpectedIfOrLBraceOrStmtAfterElseKw(
						walker.get_last_span().next_single_width(),
					),
				));
				ctx.push_node(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::If(branches),
				});
				return;
			}
		};

		if *token == Token::If {
			let if_kw_span = token_span;
			walker.push_colour(if_kw_span, SyntaxType::Keyword);
			walker.advance();

			// Consume the `(`.
			let l_paren_span = match walker.peek() {
				Some((token, span)) => {
					if *token == Token::LParen {
						walker.push_colour(span, SyntaxType::Punctuation);
						walker.advance();
						Some(span)
					} else {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedLParenAfterKw(
								if_kw_span.next_single_width(),
							),
						));
						None
					}
				}
				None => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLParenAfterKw(
							if_kw_span.next_single_width(),
						),
					));
					branches.push(IfBranch {
						span: if first_iter {
							if_kw_span
						} else {
							Span::new(else_kw_span.start, if_kw_span.end)
						},
						condition: if first_iter {
							(IfCondition::If(None), if_kw_span)
						} else {
							(
								IfCondition::ElseIf(None),
								Span::new(else_kw_span.start, if_kw_span.end),
							)
						},
						body: None,
					});
					ctx.push_node(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			};

			// Consume the condition expression.
			let cond_expr = match parse_expr(
				walker,
				ctx,
				Mode::Default,
				[Token::RParen, Token::LBrace],
			) {
				Some(e) => Some(e),
				None => {
					if let Some(l_paren_span) = l_paren_span {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedExprAfterLParen(
								l_paren_span.next_single_width(),
							),
						));
					}
					None
				}
			};

			// Consume the `)`.
			let r_paren_span = match walker.peek() {
				Some((token, span)) => {
					if *token == Token::RParen {
						walker.push_colour(span, SyntaxType::Punctuation);
						walker.advance();
						Some(span)
					} else {
						if let Some(ref cond_expr) = cond_expr {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::IfExpectedRParenAfterExpr(
									cond_expr.span.next_single_width(),
								),
							));
						}
						None
					}
				}
				None => {
					if let Some(ref cond_expr) = cond_expr {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedRParenAfterExpr(
								cond_expr.span.next_single_width(),
							),
						));
					}
					let span = Span::new(
						if first_iter {
							if_kw_span.start
						} else {
							else_kw_span.start
						},
						if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							if_kw_span.end
						},
					);
					branches.push(IfBranch {
						span,
						condition: (
							if first_iter {
								IfCondition::If(cond_expr)
							} else {
								IfCondition::ElseIf(None)
							},
							span,
						),
						body: None,
					});
					ctx.push_node(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			};

			// Consume either the `{` for a multi-line if body or a statement for a single-statement if body.
			match walker.peek() {
				Some((token, token_span)) => {
					if *token == Token::LBrace {
						// We have a multi-line body.
						walker.push_colour(token_span, SyntaxType::Punctuation);
						walker.advance();
						let scope_handle = ctx.new_temp_scope(token_span, None);
						parse_scope(walker, ctx, brace_scope, token_span);
						let body = ctx.take_temp_scope(scope_handle);

						let span = Span::new(
							if first_iter {
								if_kw_span.start
							} else {
								else_kw_span.start
							},
							if let Some(r_paren_span) = r_paren_span {
								r_paren_span.end
							} else if let Some(ref cond_expr) = cond_expr {
								cond_expr.span.end
							} else if let Some(l_paren_span) = l_paren_span {
								l_paren_span.end
							} else {
								if_kw_span.end
							},
						);
						branches.push(IfBranch {
							span: Span::new(if_kw_span.start, body.span.end),
							condition: (
								if first_iter {
									IfCondition::If(cond_expr)
								} else {
									IfCondition::ElseIf(cond_expr)
								},
								span,
							),
							body: Some(body),
						});
					} else {
						// We don't have a multi-line body, so we attempt to parse a single statement.
						let scope_handle = ctx.new_temp_scope(token_span, None);
						parse_stmt(walker, ctx);
						let body = ctx.take_temp_scope(scope_handle);

						let span = Span::new(
							if first_iter {
								if_kw_span.start
							} else {
								else_kw_span.start
							},
							if let Some(r_paren_span) = r_paren_span {
								r_paren_span.end
							} else if let Some(ref cond_expr) = cond_expr {
								cond_expr.span.end
							} else if let Some(l_paren_span) = l_paren_span {
								l_paren_span.end
							} else {
								if_kw_span.end
							},
						);
						branches.push(IfBranch {
							span: Span::new(if_kw_span.start, body.span.end),
							condition: (
								if first_iter {
									IfCondition::If(cond_expr)
								} else {
									IfCondition::ElseIf(cond_expr)
								},
								span,
							),
							body: Some(body),
						});
					}
				}
				None => {
					// We have a if-header but no associated body but we've reached the EOF.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLBraceOrStmtAfterRParen(
							walker.get_last_span().next_single_width(),
						),
					));
					let span = Span::new(
						if first_iter {
							if_kw_span.start
						} else {
							else_kw_span.start
						},
						if let Some(r_paren_span) = r_paren_span {
							r_paren_span.end
						} else if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							if_kw_span.end
						},
					);
					branches.push(IfBranch {
						span,
						condition: (
							if first_iter {
								IfCondition::If(cond_expr)
							} else {
								IfCondition::ElseIf(cond_expr)
							},
							span,
						),
						body: None,
					});
					ctx.push_node(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			}
		} else {
			// Consume either the `{` for a multi-line if body or a statement for a single-statement if body.
			match walker.peek() {
				Some((token, token_span)) => {
					if *token == Token::LBrace {
						// We have a multi-line body.
						walker.push_colour(token_span, SyntaxType::Punctuation);
						walker.advance();
						let scope_handle = ctx.new_temp_scope(token_span, None);
						parse_scope(walker, ctx, brace_scope, token_span);
						let body = ctx.take_temp_scope(scope_handle);
						branches.push(IfBranch {
							span: Span::new(else_kw_span.start, body.span.end),
							condition: (IfCondition::Else, else_kw_span),
							body: Some(body),
						});
					} else {
						// We don't have a multi-line body, so we attempt to parse a single statement.
					}
				}
				None => {
					// We have one else-header but no associated body.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLBraceOrStmtAfterRParen(
							walker.get_last_span().next_single_width(),
						),
					));
					branches.push(IfBranch {
						span: else_kw_span,
						condition: (IfCondition::Else, else_kw_span),
						body: None,
					});
					ctx.push_node(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			}
		}

		first_iter = false;
	}
}

/// Parses a switch statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_switch<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SwitchExpectedLParenAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match parse_expr(
		walker,
		ctx,
		Mode::Default,
		[Token::RParen, Token::LBrace],
	) {
		Some(e) => Some(e),
		None => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SwitchExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				span
			} else {
				if let Some(r_paren_span) = r_paren_span {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SwitchExpectedLBraceAfterCond(
							r_paren_span.next_single_width(),
						),
					));
				}
				ctx.push_node(Node {
					span: Span::new(
						kw_span.start,
						if let Some(r_paren_span) = r_paren_span {
							r_paren_span.end
						} else if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							kw_span.end
						},
					),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases: vec![],
					},
				});
				return;
			}
		}
		None => {
			if let Some(r_paren_span) = r_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedLBraceAfterCond(
						r_paren_span.next_single_width(),
					),
				));
			}
			ctx.push_node(Node {
				span: Span::new(kw_span.start, walker.get_last_span().end),
				ty: NodeTy::Switch {
					cond: cond_expr,
					cases: vec![],
				},
			});
			return;
		}
	};

	// Check if the body is empty.
	match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::RBrace {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchFoundEmptyBody(Span::new(
						l_brace_span.start,
						token_span.end,
					)),
				));
				ctx.push_node(Node {
					span: Span::new(kw_span.start, token_span.end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases: vec![],
					},
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ScopeMissingRBrace(
					l_brace_span,
					walker.get_last_span().next_single_width(),
				),
			));
			ctx.push_node(Node {
				span: Span::new(kw_span.start, walker.get_last_span().end),
				ty: NodeTy::Switch {
					cond: cond_expr,
					cases: vec![],
				},
			});
			return;
		}
	}

	// Consume cases until we reach the end of the body.
	let mut cases = Vec::new();
	loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ScopeMissingRBrace(
						l_brace_span,
						walker.get_last_span().next_single_width(),
					),
				));
				ctx.push_node(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases,
					},
				});
				return;
			}
		};

		match token {
			Token::Case => {
				let case_kw_span = token_span;
				walker.push_colour(case_kw_span, SyntaxType::Keyword);
				walker.advance();

				// Consume the expression.
				let expr = match parse_expr(
					walker,
					ctx,
					Mode::Default,
					[Token::Colon],
				) {
					Some(e) => Some(e),
					None => {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SwitchExpectedExprAfterCaseKw(
								case_kw_span.next_single_width(),
							),
						));
						None
					}
				};

				// Consume the `:`.
				let colon_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Colon {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							Some(token_span)
						} else {
							if let Some(ref expr) = expr {
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::SwitchExpectedColonAfterCaseExpr(
										expr.span.next_single_width(),
									),
								));
							}
							None
						}
					}
					None => {
						// We don't have a complete case but we've reached the EOF.
						if let Some(ref expr) = expr {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedColonAfterCaseExpr(
									expr.span.next_single_width(),
								),
							));
						}
						cases.push(SwitchCase {
							span: Span::new(
								case_kw_span.start,
								walker.get_last_span().end,
							),
							expr: Either::Left(expr),
							body: None,
						});
						ctx.push_node(Node {
							span: Span::new(
								kw_span.start,
								walker.get_last_span().end,
							),
							ty: NodeTy::Switch {
								cond: cond_expr,
								cases,
							},
						});
						return;
					}
				};

				// Consume the body of the case.
				let scope_handle = ctx.new_temp_scope(
					colon_span.unwrap_or(if let Some(ref expr) = expr {
						expr.span
					} else {
						case_kw_span
					}),
					None,
				);
				parse_scope(
					walker,
					ctx,
					switch_case_scope,
					colon_span.unwrap_or(if let Some(ref expr) = expr {
						expr.span
					} else {
						case_kw_span
					}),
				);
				let body = ctx.take_temp_scope(scope_handle);
				cases.push(SwitchCase {
					span: Span::new(case_kw_span.start, body.span.end),
					expr: Either::Left(expr),
					body: Some(body),
				});
			}
			Token::Default => {
				let default_kw_span = token_span;
				walker.push_colour(default_kw_span, SyntaxType::Keyword);
				walker.advance();

				// Consume the `:`.
				let colon_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Colon {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							Some(token_span)
						} else {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedColonAfterDefaultKw(
									default_kw_span.next_single_width(),
								),
							));
							None
						}
					}
					None => {
						// We don't have a complete case but we've reached the EOF.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SwitchExpectedColonAfterDefaultKw(
								default_kw_span.next_single_width(),
							),
						));
						cases.push(SwitchCase {
							span: default_kw_span,
							expr: Either::Right(()),
							body: None,
						});
						ctx.push_node(Node {
							span: Span::new(
								kw_span.start,
								walker.get_last_span().end,
							),
							ty: NodeTy::Switch {
								cond: cond_expr,
								cases,
							},
						});
						return;
					}
				};

				// Consume the body of the case.
				let scope_handle = ctx.new_temp_scope(
					colon_span.unwrap_or(default_kw_span.end_zero_width()),
					None,
				);
				parse_scope(
					walker,
					ctx,
					switch_case_scope,
					colon_span.unwrap_or(default_kw_span.end_zero_width()),
				);
				let body = ctx.take_temp_scope(scope_handle);
				cases.push(SwitchCase {
					span: Span::new(default_kw_span.start, body.span.end),
					expr: Either::Right(()),
					body: Some(body),
				});
			}
			Token::RBrace => {
				// If this branch is triggered, this `}` is closing the entire body of the switch statement. In the
				// following example:
				//
				// switch (true) {
				//     default: {
				//         /*...*/
				//     }
				// }
				//
				// the first `}` will be consumed by the `parse_scope()` function of the default case body, whilst
				// the second will be consumed by this branch. In the following example:
				//
				// switch (true) {
				//     default:
				//         /*...*/
				// }
				//
				// The `}` will close the body of the default case but it won't be consumed, and hence it will be
				// consumed by this branch.
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				ctx.push_node(Node {
					span: Span::new(kw_span.start, token_span.end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases,
					},
				});
				return;
			}
			_ => {
				// We have a token which cannot begin a case, nor can finish the switch body. We consume tokens
				// until we hit something recognizable.
				let invalid_span_start = token_span.start;
				let mut invalid_span_end = token_span.end;
				loop {
					match walker.peek() {
						Some((token, token_span)) => {
							if *token == Token::Case
								|| *token == Token::Default || *token
								== Token::RBrace
							{
								// We don't consume the token because the next iteration of the main loop will deal
								// with it appropriately.
								walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SwitchExpectedCaseOrDefaultKwOrEnd(
									Span::new(invalid_span_start, invalid_span_end)
								)));
								break;
							} else {
								invalid_span_end = token_span.end;
								walker.push_colour(
									token_span,
									token.non_semantic_colour(),
								);
								walker.advance();
							}
						}
						None => {
							// We haven't yet hit anything recognizable but we've reached the EOF.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedCaseOrDefaultKwOrEnd(
									Span::new(
										invalid_span_start,
										walker.get_last_span().end,
									),
								),
							));
							ctx.push_node(Node {
								span: Span::new(
									kw_span.start,
									walker.get_last_span().end,
								),
								ty: NodeTy::Switch {
									cond: cond_expr,
									cases,
								},
							});
							return;
						}
					}
				}
			}
		}
	}
}

/// Parses a for loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_for_loop<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ForExpectedLParenAfterKw(kw_span.next_single_width()),
			));
			return;
		}
	};

	// Consume the "expressions" (actually expression/declaration statements).
	let mut init: Omittable<
		Either<ast::Expr, Vec<(Type, Ident, Omittable<Span>, Omittable<Expr>)>>,
	> = Omittable::None;
	let mut cond: Omittable<ast::Expr> = Omittable::None;
	let mut inc: Omittable<ast::Expr> = Omittable::None;
	let mut counter = 0;
	let mut body_handle = None;
	let r_paren_span = 'outer: loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not encountered a `)` yet.
				let span = Span::new(
					kw_span.start,
					if let Omittable::Some(ref inc) = inc {
						inc.span.end
					} else if let Omittable::Some(ref cond) = cond {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedIncStmt(
								cond.span.next_single_width(),
							),
						));
						cond.span.end
					} else if let Omittable::Some(ref init) = init {
						let span = match init {
							Either::Left(expr) => expr.span,
							Either::Right(v) => Span::new(
								v.first().unwrap().0.span_start(),
								v.last().unwrap().0.ty_specifier_span.end,
							),
						};
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedCondStmt(
								span.next_single_width(),
							),
						));
						span.end
					} else if let Some(l_paren_span) = l_paren_span {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedInitStmt(
								l_paren_span.next_single_width(),
							),
						));
						l_paren_span.end
					} else {
						kw_span.end
					},
				);
				ctx.push_node(Node {
					span,
					ty: NodeTy::For {
						init,
						cond,
						inc,
						body: None,
					},
				});
				return;
			}
		};

		match token {
			Token::RParen => {
				if counter < 3 {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpected3Stmts(
							token_span.previous_single_width(),
						),
					));
				}
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				break token_span;
			}
			_ => {
				if counter == 3 {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpectedRParenAfterStmts(
							inc.as_ref().unwrap().span.next_single_width(),
						),
					));

					walker.push_colour(token_span, SyntaxType::Invalid);
					walker.advance();

					loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::RParen {
									walker.push_colour(
										span,
										SyntaxType::Punctuation,
									);
									walker.advance();
									break 'outer span;
								} else {
									walker
										.push_colour(span, SyntaxType::Invalid);
									walker.advance();
								}
							}
							None => break,
						}
					}
					let span_end = inc.as_ref().unwrap().span.end;
					ctx.push_node(Node {
						span: Span::new(kw_span.start, span_end),
						ty: NodeTy::For {
							init,
							cond,
							inc,
							body: None,
						},
					});
					return;
				}
			}
		}

		if counter == 0 {
			match try_parse_var_def(walker, ctx, SyntaxType::Variable, None) {
				Ok((type_, var_specifiers, semi_span)) => {
					let end_pos = if let Some(span) = semi_span {
						span.end
					} else {
						var_specifiers.last().span.end
					};

					let mut vars =
						Vec::with_capacity(var_specifiers.len().get());
					for var in var_specifiers.iter() {
						vars.push((
							combine_type_with_arr(
								type_.clone(),
								var.arr.clone(),
							),
							var.ident.clone(),
							var.eq_span.into(),
							var.init_expr.clone().into(),
						))
					}

					init = Omittable::Some(Either::Right(vars));

					body_handle = Some(ctx.new_temp_scope(
						l_paren_span.unwrap_or(kw_span.end_zero_width()),
						None,
					));
				}
				Err(Either::Left((qualifiers, expr))) => {
					invalidate_qualifiers(walker, qualifiers);
					if let Some(expr) = expr {
						init = Omittable::Some(Either::Left(expr));
					}
					body_handle = Some(ctx.new_temp_scope(
						l_paren_span.unwrap_or(kw_span.end_zero_width()),
						None,
					));
				}
				Err(Either::Right((qualifiers, _, _))) => {
					invalidate_qualifiers(walker, qualifiers);
					body_handle = Some(ctx.new_temp_scope(
						l_paren_span.unwrap_or(kw_span.end_zero_width()),
						None,
					));
				}
			}
		} else if counter == 1 || counter == 2 {
			let expr = parse_expr(
				walker,
				ctx,
				Mode::Default,
				[Token::Semi, Token::RParen],
			);
			if counter == 1 {
				cond = expr.into();
			} else {
				inc = expr.into();
			}
		}
		counter += 1;
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedLBraceAfterHeader(
						r_paren_span.next_single_width(),
					),
				));
				ctx.push_node(Node {
					span: Span::new(kw_span.start, r_paren_span.end),
					ty: NodeTy::For {
						init,
						cond,
						inc,
						body: None,
					},
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ForExpectedLBraceAfterHeader(
					r_paren_span.next_single_width(),
				),
			));
			ctx.push_node(Node {
				span: Span::new(kw_span.start, r_paren_span.end),
				ty: NodeTy::For {
					init,
					cond,
					inc,
					body: None,
				},
			});
			return;
		}
	};

	// Consume the body.
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	let body = ctx.take_temp_scope(body_handle.unwrap());
	ctx.push_node(Node {
		span: Span::new(kw_span.start, body.span.end),
		ty: NodeTy::For {
			init,
			cond,
			inc,
			body: Some(body),
		},
	});
}

/// Parses a while loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_while_loop<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::WhileExpectedLParenAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match parse_expr(
		walker,
		ctx,
		Mode::Default,
		[Token::RParen, Token::Semi],
	) {
		Some(e) => Some(e),
		None => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				span
			} else {
				if let Some(r_paren_span) = r_paren_span {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedLBraceAfterCond(
							r_paren_span.next_single_width(),
						),
					));
				}
				return;
			}
		}
		None => {
			if let Some(r_paren_span) = r_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLBraceAfterCond(
						r_paren_span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Parse the body.
	let scope_handle = ctx.new_temp_scope(l_brace_span, None);
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	let body = ctx.take_temp_scope(scope_handle);
	ctx.push_node(Node {
		span: Span::new(kw_span.start, body.span.end),
		ty: NodeTy::While {
			cond: cond_expr,
			body,
		},
	});
}

/// Parses a do-while loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_do_while_loop<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedLBraceAfterKw(
						kw_span.next_single_width(),
					),
				));
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedLBraceAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Parse the body.
	let scope_handle = ctx.new_temp_scope(l_brace_span, None);
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	let body = ctx.take_temp_scope(scope_handle);

	// Consume the `while` keyword.
	let while_kw_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::While {
				walker.push_colour(span, SyntaxType::Keyword);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedWhileAfterBody(
						body.span.next_single_width(),
					),
				));
				ctx.push_node(Node {
					span: Span::new(kw_span.start, body.span.end),
					ty: NodeTy::DoWhile { body, cond: None },
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedWhileAfterBody(
					body.span.next_single_width(),
				),
			));
			ctx.push_node(Node {
				span: Span::new(kw_span.start, body.span.end),
				ty: NodeTy::DoWhile { body, cond: None },
			});
			return;
		}
	};

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLParenAfterKw(
						while_kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::WhileExpectedLParenAfterKw(
					while_kw_span.next_single_width(),
				),
			));
			ctx.push_node(Node {
				span: Span::new(kw_span.start, while_kw_span.end),
				ty: NodeTy::DoWhile { body, cond: None },
			});
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match parse_expr(
		walker,
		ctx,
		Mode::Default,
		[Token::RParen, Token::Semi],
	) {
		Some(e) => Some(e),
		None => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			ctx.push_node(Node {
				span: Span::new(kw_span.start, while_kw_span.end),
				ty: NodeTy::DoWhile {
					body,
					cond: cond_expr,
				},
			});
			return;
		}
	};

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				span
			} else {
				let span = if let Some(r_paren_span) = r_paren_span {
					r_paren_span
				} else if let Some(ref expr) = cond_expr {
					expr.span
				} else if let Some(l_paren_span) = l_paren_span {
					l_paren_span
				} else {
					while_kw_span
				};
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedSemiAfterRParen(
						span.next_single_width(),
					),
				));
				ctx.push_node(Node {
					span,
					ty: NodeTy::DoWhile {
						body,
						cond: cond_expr,
					},
				});
				return;
			}
		}
		None => {
			let span = if let Some(r_paren_span) = r_paren_span {
				r_paren_span
			} else if let Some(ref expr) = cond_expr {
				expr.span
			} else if let Some(l_paren_span) = l_paren_span {
				l_paren_span
			} else {
				while_kw_span
			};
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedSemiAfterRParen(
					span.next_single_width(),
				),
			));
			ctx.push_node(Node {
				span,
				ty: NodeTy::DoWhile {
					body,
					cond: cond_expr,
				},
			});
			return;
		}
	};

	ctx.push_node(Node {
		span: Span::new(kw_span.start, semi_span.end),
		ty: NodeTy::DoWhile {
			cond: cond_expr,
			body,
		},
	});
}

/// Parses a break/continue/discard statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_break_continue_discard<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
	ty: impl FnOnce() -> NodeTy,
	get_ctx: impl FnOnce() -> DiagCtx,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// We consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};

	ctx.push_node(Node {
		span: Span::new(
			kw_span.start,
			if let Some(span) = semi_span {
				span.end
			} else {
				kw_span.end
			},
		),
		ty: ty(),
	});

	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: kw_span.end,
			ctx: get_ctx(),
		});
		seek_next_stmt2(walker, ctx);
	}
}

/// Parses a return statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_return<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// We look for the optional return value expression.
	let return_expr =
		match parse_expr(walker, ctx, Mode::Default, [Token::Semi]) {
			Some(e) => Some(e),
			None => None,
		};

	// We expect a `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};

	let end_pos = if let Some(span) = semi_span {
		span.end
	} else if let Some(expr) = &return_expr {
		expr.span.end
	} else {
		kw_span.end
	};

	ctx.push_node(Node {
		span: Span::new(kw_span.start, end_pos),
		ty: NodeTy::Return {
			value: return_expr.into(),
		},
	});

	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: end_pos,
			ctx: DiagCtx::ReturnStmt,
		});
		seek_next_stmt2(walker, ctx);
	}
}

// region: preprocessor grammar
/// Parses a preprocessor directive.
///
/// This function assumes that the directive has not yet been consumed.
fn parse_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	stream: PreprocStream,
	dir_span: Span,
) {
	use crate::lexer::preprocessor::{self, DefineToken, UndefToken};

	match stream {
		PreprocStream::Empty => {
			walker.push_colour(dir_span, SyntaxType::DirectiveHash);
			walker.push_semantic_diag(Semantic::UnnecessaryDirective(dir_span));
			ctx.push_node(Node {
				span: dir_span,
				ty: NodeTy::EmptyDirective,
			});
		}
		PreprocStream::Custom { kw, content } => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(kw.1, SyntaxType::DirectiveName);
			if let Some((_, span)) = content {
				walker.push_colour(span, SyntaxType::Directive);
			}
			walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
				item: ForRemoval2::InvalidDirective,
				span: dir_span,
			});
		}
		PreprocStream::Invalid { content } => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(content.1, SyntaxType::Directive);
			walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
				item: ForRemoval2::InvalidDirective,
				span: dir_span,
			});
		}
		PreprocStream::Version { kw, tokens } => {
			parse_version_directive(walker, ctx, dir_span, kw, tokens)
		}
		PreprocStream::Extension { kw, tokens } => {
			parse_extension_directive(walker, ctx, dir_span, kw, tokens)
		}
		PreprocStream::Line { kw, tokens } => {
			parse_line_directive(walker, ctx, dir_span, kw, tokens)
		}
		PreprocStream::Define {
			kw: kw_span,
			mut ident_tokens,
			body_tokens,
		} => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(kw_span, SyntaxType::DirectiveName);

			if ident_tokens.is_empty() && body_tokens.is_empty() {
				// We have a macro that's missing a name.

				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::NothingExpectedMacroName,
					span: kw_span.next_single_width(),
				});
			} else if ident_tokens.is_empty() && !body_tokens.is_empty() {
				// We have a macro that's missing a name.

				let (_, first) = body_tokens.first().unwrap();
				let (_, last) = body_tokens.last().unwrap();
				walker.push_colour_with_modifiers(
					Span::new(first.start, last.end),
					SyntaxType::Invalid,
					SyntaxModifiers::MACRO_BODY,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedMacroName,
					span: Span::new(first.start, last.end),
				});
			} else if ident_tokens.len() == 1 {
				// We have an object-like macro.

				let (name, name_span) = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::ObjectMacro,
							SyntaxModifiers::MACRO_SIGNATURE,
						);
						(s, span)
					}
					// Panic: `ident_tokens` must always start with a `DefineToken::Ident`.
					_ => unreachable!(),
				};

				// Since object-like macros don't have parameters, we can perform the concatenation right here
				// since we know the contents of the macro body will never change.
				let (body_tokens, mut syntax, mut semantic) =
					preprocessor::concat_macro_body(
						body_tokens,
						walker.span_encoding,
					);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				body_tokens.iter().for_each(|(t, s)| {
					walker.push_colour_with_modifiers(
						*s,
						t.non_semantic_colour(),
						SyntaxModifiers::MACRO_BODY,
					)
				});

				walker.register_macro(
					name.clone(),
					name_span,
					Macro::Object(body_tokens.clone()),
				);
				ctx.push_node(Node {
					span: dir_span,
					ty: NodeTy::DefineDirective {
						macro_: ast::Macro::Object {
							ident: Ident {
								span: name_span,
								name,
							},
						},
						replacement_tokens: body_tokens,
					},
				});
			} else {
				// We have a function-like macro.

				let (name, name_span) = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::FunctionMacro,
							SyntaxModifiers::MACRO_SIGNATURE,
						);
						(s, span)
					}
					// Panic: `ident_tokens` must always start with a `DefineToken::Ident`.
					_ => unreachable!(),
				};

				// Consume the `(`.
				let l_paren_span = match ident_tokens.remove(0) {
					(DefineToken::LParen, span) => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::Punctuation,
							SyntaxModifiers::MACRO_SIGNATURE,
						);
						span
					}
					// Panic: `ident_tokens` must always have a `DefineToken::LParen` afterwards.
					_ => unreachable!(),
				};

				// Look for any parameters until we hit a closing `)` parenthesis.
				#[derive(PartialEq)]
				enum Prev {
					None,
					Param,
					Comma,
					Invalid,
				}
				let mut prev = Prev::None;
				let mut prev_span = l_paren_span;
				let mut params = Vec::new();
				let r_paren_span = loop {
					let (token, token_span) = if !ident_tokens.is_empty() {
						ident_tokens.remove(0)
					} else {
						walker.push_nsyntax_diag(Syntax2::MissingPunct2 {
							missing: MissingPunct::EndOfParamList,
							span: prev_span.next_single_width(),
						});
						ctx.push_node(Node {
							span: dir_span,
							ty: NodeTy::DefineDirective {
								macro_: ast::Macro::Function {
									ident: Ident {
										span: name_span,
										name,
									},
									params,
								},
								replacement_tokens: body_tokens,
							},
						});
						return;
					};

					match token {
						DefineToken::Comma => {
							walker.push_colour_with_modifiers(
								token_span,
								SyntaxType::Punctuation,
								SyntaxModifiers::MACRO_SIGNATURE,
							);
							if prev == Prev::Comma {
								walker.push_nsyntax_diag(
									Syntax2::FoundUnexpected {
										ty: Found::NothingExpectedParam,
										span: Span::new_between(
											prev_span, token_span,
										),
									},
								);
							} else if prev == Prev::None {
								walker.push_nsyntax_diag(
									Syntax2::FoundUnexpected {
										ty: Found::NothingExpectedParam,
										span: Span::new_between(
											prev_span, token_span,
										),
									},
								);
							}
							prev = Prev::Comma;
							prev_span = token_span;
						}
						DefineToken::Ident(str) => {
							walker.push_colour_with_modifiers(
								token_span,
								SyntaxType::Parameter,
								SyntaxModifiers::MACRO_SIGNATURE,
							);
							params.push(Ident {
								name: str,
								span: token_span,
							});
							if prev == Prev::Param {
								walker.push_nsyntax_diag(
									Syntax2::MissingPunct2 {
										missing: MissingPunct::CommaInParamList,
										span: Span::new_between(
											prev_span, token_span,
										),
									},
								);
							}
							prev = Prev::Param;
							prev_span = token_span;
						}
						DefineToken::RParen => {
							walker.push_colour_with_modifiers(
								token_span,
								SyntaxType::Punctuation,
								SyntaxModifiers::MACRO_SIGNATURE,
							);
							if prev == Prev::Comma {
								walker.push_nsyntax_diag(
									Syntax2::FoundUnexpected {
										ty: Found::NothingExpectedParam,
										span: Span::new_between(
											prev_span, token_span,
										),
									},
								);
							}
							break token_span;
						}
						_ => {
							walker.push_colour_with_modifiers(
								token_span,
								SyntaxType::Invalid,
								SyntaxModifiers::MACRO_SIGNATURE,
							);
							walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
								item: ForRemoval2::SomethingInParamList,
								span: token_span,
							});
							prev = Prev::Invalid;
							prev_span = token_span;
						}
					}
				};

				// We can't perform the token concatenation right here since the contents of the macro body will
				// change depending on the parameters, but we can still concatenate in order to find any
				// syntax/semantic diagnostics.
				let (_, mut syntax, mut semantic) =
					preprocessor::concat_macro_body(
						body_tokens.clone(),
						walker.span_encoding,
					);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);

				// Syntax highlight the body. If any identifier matches a parameter name, we need to correctly
				// highlight that.
				body_tokens.iter().for_each(|(t, s)| match t {
					Token::Ident(str) => {
						if let Some(_) =
							params.iter().find(|ident| &ident.name == str)
						{
							walker.push_colour_with_modifiers(
								*s,
								SyntaxType::Parameter,
								SyntaxModifiers::MACRO_BODY,
							)
						} else {
							walker.push_colour_with_modifiers(
								*s,
								t.non_semantic_colour(),
								SyntaxModifiers::MACRO_BODY,
							)
						}
					}
					_ => walker.push_colour_with_modifiers(
						*s,
						t.non_semantic_colour(),
						SyntaxModifiers::MACRO_BODY,
					),
				});

				walker.register_macro(
					name.clone(),
					Span::new(name_span.start, r_paren_span.end),
					Macro::Function {
						params: params.clone(),
						body: body_tokens.clone(),
					},
				);
				ctx.push_node(Node {
					span: dir_span,
					ty: NodeTy::DefineDirective {
						macro_: ast::Macro::Function {
							ident: Ident {
								span: name_span,
								name,
							},
							params,
						},
						replacement_tokens: body_tokens,
					},
				});
			}
		}
		PreprocStream::Undef {
			kw: kw_span,
			mut tokens,
		} => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(kw_span, SyntaxType::DirectiveName);

			let ident = if tokens.is_empty() {
				walker.push_semantic_diag(Semantic::UnnecessaryDirective(
					dir_span,
				));
				Omittable::None
			} else {
				let (token, token_span) = tokens.remove(0);
				let ident = match token {
					UndefToken::Ident(s) => {
						match walker.unregister_macro(&s) {
							Some(super::Macro::Object(_)) => walker
								.push_colour_with_modifiers(
									token_span,
									SyntaxType::ObjectMacro,
									SyntaxModifiers::UNDEF,
								),
							Some(super::Macro::Function { .. }) => walker
								.push_colour_with_modifiers(
									token_span,
									SyntaxType::FunctionMacro,
									SyntaxModifiers::UNDEF,
								),
							None => {
								walker.push_colour_with_modifiers(
									token_span,
									SyntaxType::Ident,
									SyntaxModifiers::UNDEF,
								);
								walker.push_semantic_diag(
									Semantic::UndefMacroNameUnresolved {
										name: (s.clone(), token_span),
									},
								);
							}
						};

						// We've removed the first token. If there are still tokens, whatever they hold is invalid.
						if !tokens.is_empty() {
							let (_, first) = tokens.first().unwrap();
							let (_, last) = tokens.last().unwrap();
							walker.push_colour_with_modifiers(
								Span::new(first.start, last.end),
								SyntaxType::Invalid,
								SyntaxModifiers::UNDEF,
							);
							walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
								item: ForRemoval2::DirectiveTrailingTokens,
								span: Span::new(first.start, last.end),
							});
						}

						Omittable::Some(Ident {
							name: s,
							span: token_span,
						})
					}
					UndefToken::Invalid(_) => {
						let end = if !tokens.is_empty() {
							tokens.last().unwrap().1.end
						} else {
							token_span.end
						};
						walker.push_colour_with_modifiers(
							Span::new(token_span.start, end),
							SyntaxType::Invalid,
							SyntaxModifiers::UNDEF,
						);
						walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
							item: ForRemoval2::SomethingInUndef,
							span: Span::new(token_span.start, end),
						});
						Omittable::None
					}
				};

				ident
			};

			ctx.push_node(Node {
				span: Span::new(
					dir_span.start,
					if let Omittable::Some(ident) = &ident {
						ident.span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::UndefDirective { name: ident },
			});
		}
		PreprocStream::Error { kw, message } => {
			parse_error_directive(walker, ctx, dir_span, kw, message)
		}
		PreprocStream::Pragma { kw, options } => {
			parse_pragma_directive(walker, ctx, dir_span, kw, options)
		}
		_ => {}
	}
}

/// Parses a `#version` directive.
fn parse_version_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(VersionToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
	walker.push_colour(kw_span, SyntaxType::DirectiveName);

	if tokens.is_empty() {
		walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
			ty: Found::NothingExpectedGlslVersion,
			span: kw_span.next_single_width(),
		});
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (VersionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let (span_start, mut span_end) = match tokens.next() {
			Some((_, token_span)) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::VERSION,
				);
				(token_span.start, token_span.end)
			}
			None => return,
		};
		for (_, token_span) in tokens.into_iter() {
			walker.push_colour_with_modifiers(
				token_span,
				SyntaxType::Invalid,
				SyntaxModifiers::VERSION,
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
				item: ForRemoval2::DirectiveTrailingTokens,
				span: Span::new(span_start, span_end),
			});
		}
	}

	/// Parses the version number.
	fn parse_version<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		number: usize,
		span: Span,
	) -> Option<usize> {
		match number {
			450 => Some(number),
			100 | 110 | 120 | 130 | 140 | 150 | 300 | 310 | 320 | 330 | 400
			| 410 | 420 | 430 | 460 => {
				walker.push_semantic_diag(Semantic::UnsupportedGlslVersion {
					version: number,
					version_span: span,
				});
				Some(number)
			}
			_ => {
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::InvalidGlslVersion { version: number },
					span,
				});
				None
			}
		}
	}

	/// Parses the profile; also pushes a syntax highlighting token.
	fn parse_profile<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		str: &str,
		span: Span,
	) -> Option<ProfileTy> {
		match str {
			"core" => {
				walker.push_colour_with_modifiers(
					span,
					SyntaxType::Ident,
					SyntaxModifiers::VERSION,
				);
				Some(ProfileTy::Core)
			}
			"compatability" => {
				walker.push_colour_with_modifiers(
					span,
					SyntaxType::Ident,
					SyntaxModifiers::VERSION,
				);
				Some(ProfileTy::Compatability)
			}
			"es" => {
				walker.push_colour_with_modifiers(
					span,
					SyntaxType::Ident,
					SyntaxModifiers::VERSION,
				);
				Some(ProfileTy::Es)
			}
			_ => {
				let str = str.to_lowercase();
				match str.as_ref() {
					"core" => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::Ident,
							SyntaxModifiers::VERSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslProfileCasing {
								correct_casing: "core",
							},
							span,
						});
						Some(ProfileTy::Core)
					}
					"compatability" => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::Ident,
							SyntaxModifiers::VERSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslProfileCasing {
								correct_casing: "compatability",
							},
							span,
						});
						Some(ProfileTy::Compatability)
					}
					"es" => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::Ident,
							SyntaxModifiers::VERSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslProfileCasing {
								correct_casing: "es",
							},
							span,
						});
						Some(ProfileTy::Es)
					}
					_ => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::Invalid,
							SyntaxModifiers::VERSION,
						);
						None
					}
				}
			}
		}
	}

	// Consume the version number.
	let version = {
		// Panic: checked vector length earlier.
		let (token, token_span) = tokens.next().unwrap();
		match token {
			VersionToken::Num(n) => {
				match parse_version(walker, n, token_span) {
					Some(n) => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Number,
							SyntaxModifiers::VERSION,
						);
						(n, token_span)
					}
					None => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Invalid,
							SyntaxModifiers::VERSION,
						);
						seek_end(walker, tokens, false);
						return;
					}
				}
			}
			VersionToken::InvalidNum(_) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::VERSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslVersion,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Invalid(_) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::VERSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslVersion,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Word(str) => {
				match parse_profile(walker, &str, token_span) {
					Some(profile) => {
						// We have a profile immediately after the `version` keyword.
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::GlslProfileExpectedVersion,
							span: Span::new_between(kw_span, token_span),
						});
						seek_end(walker, tokens, true);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::VersionDirective {
								version: None,
								profile: Omittable::Some((profile, token_span)),
							},
						});
						return;
					}
					None => {
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::SomethingExpectedGlslVersion,
							span: token_span,
						});
						seek_end(walker, tokens, false);
						return;
					}
				}
			}
		}
	};

	// Look for an optional profile.
	let profile = match tokens.next() {
		Some((token, token_span)) => match token {
			VersionToken::Word(str) => {
				match parse_profile(walker, &str, token_span) {
					Some(p) => Omittable::Some((p, token_span)),
					None => {
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::SomethingExpectedGlslProfile,
							span: token_span,
						});
						seek_end(walker, tokens, false);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, version.1.end),
							ty: NodeTy::VersionDirective {
								version: Some(version),
								profile: Omittable::None,
							},
						});
						return;
					}
				}
			}
			_ => {
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslProfile,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, version.1.end),
					ty: NodeTy::VersionDirective {
						version: Some(version),
						profile: Omittable::None,
					},
				});
				return;
			}
		},
		None => Omittable::None,
	};

	seek_end(walker, tokens, true);
	ctx.push_node(Node {
		span: Span::new(
			dir_span.start,
			if let Omittable::Some(ref profile) = profile {
				profile.1.end
			} else {
				version.1.end
			},
		),
		ty: NodeTy::VersionDirective {
			version: Some(version),
			profile,
		},
	});
}

/// Parses an `#extension` directive.
fn parse_extension_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(ExtensionToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
	walker.push_colour(kw_span, SyntaxType::DirectiveName);

	if tokens.is_empty() {
		walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
			ty: Found::NothingExpectedGlslExtName,
			span: kw_span.next_single_width(),
		});
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (ExtensionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let (span_start, mut span_end) = match tokens.next() {
			Some((_, span)) => {
				walker.push_colour_with_modifiers(
					span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				(span.start, span.end)
			}
			None => return,
		};
		for (_, token_span) in tokens.into_iter() {
			walker.push_colour_with_modifiers(
				token_span,
				SyntaxType::Invalid,
				SyntaxModifiers::EXTENSION,
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
				item: ForRemoval2::DirectiveTrailingTokens,
				span: Span::new(span_start, span_end),
			});
		}
	}

	/// Parses the behaviour.
	fn parse_behaviour(
		str: &str,
		span: Span,
	) -> Option<(BehaviourTy, Option<Syntax2>)> {
		match str {
			"require" => Some((BehaviourTy::Require, None)),
			"enable" => Some((BehaviourTy::Enable, None)),
			"warn" => Some((BehaviourTy::Warn, None)),
			"disable" => Some((BehaviourTy::Disable, None)),
			_ => {
				let str = str.to_lowercase();
				match str.as_ref() {
					"require" => Some((
						BehaviourTy::Require,
						Some(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslExtBehaviourCasing {
								correct_casing: "require",
							},
							span,
						}),
					)),
					"enable" => Some((
						BehaviourTy::Enable,
						Some(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslExtBehaviourCasing {
								correct_casing: "enable",
							},
							span,
						}),
					)),
					"warn" => Some((
						BehaviourTy::Warn,
						Some(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslExtBehaviourCasing {
								correct_casing: "warn",
							},
							span,
						}),
					)),
					"disable" => Some((
						BehaviourTy::Disable,
						Some(Syntax2::FoundUnexpected {
							ty: Found::IncorrectGlslExtBehaviourCasing {
								correct_casing: "disable",
							},
							span,
						}),
					)),
					_ => None,
				}
			}
		}
	}

	// Consume the extension name.
	let name = {
		// Panic: checked vector length earlier.
		let (token, token_span) = tokens.next().unwrap();
		match token {
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Ident,
							SyntaxModifiers::EXTENSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::GlslExtBehaviourExpectedExtName,
							span: Span::new_between(kw_span, token_span),
						});
						seek_end(walker, tokens, false);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::ExtensionDirective {
								name: None,
								behaviour: Some((behaviour, token_span)),
							},
						});
						return;
					}
					None => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Ident,
							SyntaxModifiers::EXTENSION,
						);
						(str, token_span)
					}
				}
			}
			ExtensionToken::Colon => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::ColonExpectedExtName,
					span: Span::new_between(kw_span, token_span),
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, kw_span.end),
					ty: NodeTy::ExtensionDirective {
						name: None,
						behaviour: None,
					},
				});
				return;
			}
			ExtensionToken::Invalid(_) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslExtName,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				return;
			}
		}
	};

	// Consume the colon.
	let colon_span = match tokens.next() {
		Some((token, token_span)) => match token {
			ExtensionToken::Colon => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Punctuation,
					SyntaxModifiers::EXTENSION,
				);
				token_span
			}
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Ident,
							SyntaxModifiers::EXTENSION,
						);
						walker.push_nsyntax_diag(Syntax2::MissingPunct2 {
							missing:
								MissingPunct::ColonBetweenGlslExtNameBehaviour,
							span: Span::new_between(name.1, token_span),
						});
						seek_end(walker, tokens, false);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: Some((behaviour, token_span)),
							},
						});
						return;
					}
					None => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Invalid,
							SyntaxModifiers::EXTENSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::SomethingExpectedGlslExtColon,
							span: token_span,
						});
						seek_end(walker, tokens, false);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, name.1.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: None,
							},
						});
						return;
					}
				}
			}
			ExtensionToken::Invalid(_) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslExtColon,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, name.1.end),
					ty: NodeTy::ExtensionDirective {
						name: Some(name),
						behaviour: None,
					},
				});
				return;
			}
		},
		None => {
			walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
				ty: Found::NothingExpectedGlslExtColon,
				span: name.1.next_single_width(),
			});
			ctx.push_node(Node {
				span: Span::new(dir_span.start, name.1.end),
				ty: NodeTy::ExtensionDirective {
					name: Some(name),
					behaviour: None,
				},
			});
			return;
		}
	};

	// Consume the behaviour.
	let behaviour = match tokens.next() {
		Some((token, token_span)) => match token {
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, diag)) => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Ident,
							SyntaxModifiers::EXTENSION,
						);
						if let Some(diag) = diag {
							walker.push_nsyntax_diag(diag);
						}
						(behaviour, token_span)
					}
					None => {
						walker.push_colour_with_modifiers(
							token_span,
							SyntaxType::Invalid,
							SyntaxModifiers::EXTENSION,
						);
						walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
							ty: Found::SomethingExpectedGlslExtBehaviour,
							span: token_span,
						});
						seek_end(walker, tokens, false);
						ctx.push_node(Node {
							span: Span::new(dir_span.start, colon_span.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: None,
							},
						});
						return;
					}
				}
			}
			ExtensionToken::Colon => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslExtBehaviour,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, colon_span.end),
					ty: NodeTy::ExtensionDirective {
						name: Some(name),
						behaviour: None,
					},
				});
				return;
			}
			ExtensionToken::Invalid(_) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::EXTENSION,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedGlslExtBehaviour,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, colon_span.end),
					ty: NodeTy::ExtensionDirective {
						name: Some(name),
						behaviour: None,
					},
				});
				return;
			}
		},
		None => {
			walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
				ty: Found::NothingExpectedGlslExtBehaviour,
				span: name.1.next_single_width(),
			});
			ctx.push_node(Node {
				span: Span::new(dir_span.start, colon_span.end),
				ty: NodeTy::ExtensionDirective {
					name: Some(name),
					behaviour: None,
				},
			});
			return;
		}
	};

	seek_end(walker, tokens, true);
	ctx.push_node(Node {
		span: Span::new(dir_span.start, behaviour.1.end),
		ty: NodeTy::ExtensionDirective {
			name: Some(name),
			behaviour: Some(behaviour),
		},
	});
}

/// Parses a `#line` directive.
fn parse_line_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(LineToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
	walker.push_colour(kw_span, SyntaxType::DirectiveName);

	if tokens.is_empty() {
		walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
			ty: Found::NothingExpectedLineNumber,
			span: kw_span.next_single_width(),
		});
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (LineToken, Span)>,
		emit_diagnostic: bool,
	) {
		let (span_start, mut span_end) = match tokens.next() {
			Some((_, token_span)) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::LINE,
				);
				(token_span.start, token_span.end)
			}
			None => return,
		};
		for (_, token_span) in tokens.into_iter() {
			walker.push_colour_with_modifiers(
				token_span,
				SyntaxType::Invalid,
				SyntaxModifiers::LINE,
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_nsyntax_diag(Syntax2::ForRemoval2 {
				item: ForRemoval2::DirectiveTrailingTokens,
				span: Span::new(span_start, span_end),
			});
		}
	}

	let line = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			LineToken::Num(n) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Number,
					SyntaxModifiers::LINE,
				);
				(n, token_span)
			}
			_ => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::LINE,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedLineNumber,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, kw_span.end),
					ty: NodeTy::LineDirective {
						line: None,
						src_str_num: Omittable::None,
					},
				});
				return;
			}
		}
	};

	let src_str_num = match tokens.next() {
		Some((token, token_span)) => match token {
			LineToken::Num(n) => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Number,
					SyntaxModifiers::LINE,
				);
				(n, token_span)
			}
			_ => {
				walker.push_colour_with_modifiers(
					token_span,
					SyntaxType::Invalid,
					SyntaxModifiers::LINE,
				);
				walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
					ty: Found::SomethingExpectedSrcStrNumber,
					span: token_span,
				});
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(dir_span.start, kw_span.end),
					ty: NodeTy::LineDirective {
						line: Some(line),
						src_str_num: Omittable::None,
					},
				});
				return;
			}
		},
		None => {
			walker.push_nsyntax_diag(Syntax2::FoundUnexpected {
				ty: Found::NothingExpectedSrcStrNumber,
				span: line.1.next_single_width(),
			});
			seek_end(walker, tokens, false);
			ctx.push_node(Node {
				span: Span::new(dir_span.start, line.1.end),
				ty: NodeTy::LineDirective {
					line: Some(line),
					src_str_num: Omittable::None,
				},
			});
			return;
		}
	};

	seek_end(walker, tokens, true);
	ctx.push_node(Node {
		span: Span::new(dir_span.start, src_str_num.1.end),
		ty: NodeTy::LineDirective {
			line: Some(line),
			src_str_num: Omittable::Some(src_str_num),
		},
	});
}

/// Parses an `#error` directive.
fn parse_error_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	dir_span: Span,
	kw_span: Span,
	message: Option<Spanned<String>>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
	walker.push_colour(kw_span, SyntaxType::DirectiveName);
	if let Some(message) = &message {
		walker.push_colour_with_modifiers(
			message.1,
			SyntaxType::String,
			SyntaxModifiers::ERROR,
		);
	}
	ctx.push_node(Node {
		span: Span::new(
			dir_span.start,
			if let Some(message) = &message {
				message.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::ErrorDirective {
			message: message.into(),
		},
	});
}

/// Parses a `#pragma` directive.
fn parse_pragma_directive<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	dir_span: Span,
	kw_span: Span,
	options: Option<Spanned<String>>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
	walker.push_colour(kw_span, SyntaxType::DirectiveName);
	if let Some(options) = &options {
		walker.push_colour_with_modifiers(
			options.1,
			SyntaxType::String,
			SyntaxModifiers::PRAGMA,
		);
	}
	ctx.push_node(Node {
		span: Span::new(
			dir_span.start,
			if let Some(options) = &options {
				options.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::PragmaDirective {
			options: options.into(),
		},
	});
}
// endregion: preprocessor grammar

fn parse_non_kw_stmt_for_subroutine<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	// Invariant: has a length of at least 1
	qualifiers: Vec<Qualifier>,
	association_list: Option<(
		Vec<(super::SubroutineHandle, Ident)>,
		Span,
		Span,
	)>,
	start_pos: usize,
	uniform_kw_span: Option<Span>,
	subroutine_kw_span: Span,
	is_uniform_before_subroutine: bool,
	qualifiers_end_pos: usize,
) {
	// We attempt to parse a subroutine type specifier at the current position, and if that fails a normal type
	// specifier, and if that fails an expression.
	let e =
		match try_parse_subroutine_type_specifier(walker, ctx, [Token::Semi]) {
			Ok(mut type_) => {
				// This must be a subroutine type declaration, an associated function definition, or a subroutine
				// uniform definition.

				match &mut type_ {
					Either::Left(type_) => {
						type_.qualifiers = NonEmpty::from_vec(qualifiers).into()
					}
					Either::Right(type_) => {
						type_.qualifiers = NonEmpty::from_vec(qualifiers).into()
					}
				}

				let (token, token_span) = match walker.peek() {
					Some(t) => t,
					None => {
						// We expect something after the type specifier.
						walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
							item: ExpectedGrammar::AfterSubroutineType,
							span: Span::new_zero_width(qualifiers_end_pos),
						});
						return;
					}
				};

				// Check whether we have a subroutine type declaration or an associated function definition.
				match token {
					Token::Ident(i) => match walker.lookahead_1() {
						Some(next) => match next.0 {
							Token::LParen => {
								// We have a function declaration/definition.
								let l_paren_span = next.1;
								let ident = Ident {
									name: i.clone(),
									span: token_span,
								};
								walker.push_colour(
									token_span,
									SyntaxType::Subroutine,
								);
								walker.advance();
								walker.push_colour(
									next.1,
									SyntaxType::Punctuation,
								);
								walker.advance();
								parse_subroutine_function(
									walker,
									ctx,
									start_pos,
									uniform_kw_span,
									subroutine_kw_span,
									is_uniform_before_subroutine,
									qualifiers_end_pos,
									association_list,
									type_,
									ident,
									l_paren_span,
								);
								return;
							}
							_ => {}
						},
						None => {}
					},
					_ => {}
				}

				// We don't have a subroutine type declaration nor an associated function definition, so this must
				// be a subroutine uniform definition.

				let var_specifiers = match try_parse_new_var_specifiers(
					walker,
					ctx,
					[Token::Semi],
					SyntaxType::Subroutine,
					false,
				) {
					Ok(v) => v,
					Err(e) => match e {
						Either3::A(next_type) => {
							// We have a (subroutine/normal) type specifier, followed by another type specifier.
							// The best error recovery strategy is to treat the subroutine qualifiers and type
							// specifier as an unfinished subroutine uniform statement, and the second type
							// specifier as a future statement.
							walker.push_nsyntax_diag(
								Syntax2::ExpectedGrammar {
									item: ExpectedGrammar::NewVarSpecifier,
									span: match &type_ {
										Either::Left(t) => t.ty_specifier_span,
										Either::Right(t) => t.ty_specifier_span,
									},
								},
							);
							walker.tmp_buf = Either3::B(next_type);
							return;
						}
						Either3::B(expr) => {
							// We have a (subroutine/normal) type specifier, followed by a second expression but
							// the second expression isn't one or more new variable specifiers. The best error
							// recovery strategy is to treat the subroutine qualifiers and type specifier as an
							// unfinished subroutine uniform statement, and the second expression as an expression
							// statement on its own.
							walker.push_nsyntax_diag(
								Syntax2::ExpectedGrammar {
									item: ExpectedGrammar::NewVarSpecifier,
									span: match &type_ {
										Either::Left(t) => t.ty_specifier_span,
										Either::Right(t) => t.ty_specifier_span,
									},
								},
							);
							walker.tmp_buf = Either3::C(expr);
							return;
						}
						Either3::C(_) => {
							// We have a (subroutine/normal) type specifier followed by something that can't be
							// parsed at all as an expression. The best error recovery strategy is to treat the
							// subroutine qualifiers and type specifier as an unfinished subroutine uniform
							// statement, and seek the next statement.
							walker.push_nsyntax_diag(
								Syntax2::ExpectedGrammar {
									item: ExpectedGrammar::NewVarSpecifier,
									span: match &type_ {
										Either::Left(t) => t.ty_specifier_span,
										Either::Right(t) => t.ty_specifier_span,
									},
								},
							);
							seek_next_stmt2(walker, ctx);
							return;
						}
					},
				};

				let last_var_spec_pos = var_specifiers.last().span.end;

				// We definitely have something which matches a variable(s) definition, irrespective of what comes
				// next. That means the only node that makes sense to produce is a subroutine uniform definition
				// node. For that to be valid, we need a) lack of an association list, b) the `uniform` keyword
				// after the subroutine keyword, c) a subroutine type specifier rather than a normal type
				// specifier. If (a) is present, we can just ignore it. If (b) is missing, we can just assume it's
				// present. If (c) is not met, we can't create the node since the ast node explicitly takes only a
				// subroutine type.

				// Check (a)
				if let Some((_, l_paren, r_paren)) = association_list {
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::AssociationList,
						span: Span::new(l_paren.start, r_paren.end),
						ctx: DiagCtx::SubroutineUniform,
					});
				}

				// Check (b)
				if let Some(uniform_kw_span) = uniform_kw_span {
					if is_uniform_before_subroutine {
						walker.push_nsyntax_diag(Syntax2::IncorrectOrder {
							msg: "`uniform` keyword must be located after the `subroutine` keyword",
							span: uniform_kw_span,
						});
					}
				} else {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::Keyword("uniform"),
						span: Span::new_zero_width(qualifiers_end_pos),
					});
				}

				// Check (c)
				let type_ = match type_ {
					Either::Left(type_) => type_,
					Either::Right(type_) => {
						// Since the subroutine uniform node takes a subroutine type handle, there is really
						// nothing else we can do other than abort creating anything.
						walker.push_semantic_diag(
							Semantic::SubUniformFoundNormalType(
								type_.ty_specifier_span,
							),
						);
						return;
					}
				};

				// We expect a `;` after the new variable specifier(s).
				let semi_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Semi {
							walker.push_colour(
								token_span,
								SyntaxType::Punctuation,
							);
							walker.advance();
							Some(token_span)
						} else {
							None
						}
					}
					None => None,
				};
				ctx.push_new_subroutine_uniforms(
					walker,
					start_pos,
					type_,
					var_specifiers,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else {
						last_var_spec_pos
					},
				);
				if semi_span.is_none() {
					walker.push_nsyntax_diag(Syntax2::MissingPunct {
						char: ';',
						pos: last_var_spec_pos,
						ctx: DiagCtx::SubroutineUniform,
					});
					seek_next_stmt(walker);
				}
				return;
			}
			Err(e) => e,
		};

	let Some(expr) = e else {
		// We couldn't parse a (subroutine/normal) type specifier nor even an expression, so this cannot be a
		// valid statement.
		walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
			item: ExpectedGrammar::AfterSubroutineQualifiers,
			span: Span::new_zero_width(qualifiers_end_pos),
		});
		seek_next_stmt2(walker, ctx);
		return;
	};

	// We have an expression. If the expression is just a single identifier and we have a `{` next then the closest
	// match is an interface block, otherwise the closest match is an expression statement.

	match (&expr.ty, walker.peek()) {
		(ExprTy::Local { name: ident, .. }, Some((token, token_span))) => {
			match token {
				Token::LBrace => {
					// Though this technically isn't a valid interface block because of the presence of the
					// `subroutine` keyword, this is the best error recovery strategy.
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Keyword("subroutine"),
						span: subroutine_kw_span,
						ctx: DiagCtx::InterfaceBlockDef,
					});

					// Since we were attempting to parse a type specifier but found an expression expression
					// consisting of a single ident instead, we know that the last syntax token to be added is for
					// that ident. We also know that, assuming no variable with such a name exists yet, the last
					// unresolved semantic diagnostic would be for this single-ident expression.
					walker.highlighting_tokens.last_mut().unwrap().ty =
						SyntaxType::InterfaceBlock;
					let mut remove = false;
					if let Some((diag, _)) = ctx.unresolved_diags.last() {
						match diag {
							Semantic::UnresolvedVariable {
								var: (var_name, _),
								..
							} => {
								if var_name == &ident.name {
									remove = true;
								}
							}
							_ => {}
						}
					}
					if remove {
						ctx.unresolved_diags.pop();
					}

					let l_brace_span = token_span;
					walker.push_colour(l_brace_span, SyntaxType::Punctuation);
					walker.advance();
					parse_interface_block(
						walker,
						ctx,
						qualifiers,
						ident.clone(),
						l_brace_span,
					);
					return;
				}
				_ => {}
			}
		}
		(_, _) => {}
	}

	// We have an expression preceeded by qualifiers **including** the `subroutine` keyword. The best error
	// recovery strategy is to treat the qualifiers/subroutine as the beginning of a subroutine-related statement
	// that is incomplete, and the expression as an expression statement on its own.
	walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
		item: ExpectedGrammar::AfterSubroutineQualifiers,
		span: Span::new_zero_width(qualifiers_end_pos),
	});

	// We expect a `;` after an expression to make it into a statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxType::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};
	let expr_end = expr.span.end;
	ctx.push_node(Node {
		span: if let Some(semi_span) = semi_span {
			Span::new(expr.span.start, semi_span.end)
		} else {
			expr.span
		},
		ty: NodeTy::Expr(expr),
	});
	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: expr_end,
			ctx: DiagCtx::ExprStmt,
		});
		seek_next_stmt(walker);
	}
}

/// Parses a subroutine type declaration (function declaration grammar) or an associated subroutine function
/// definition.
///
/// This function assumes that the return type, ident, and opening parenthesis have been consumed.
fn parse_subroutine_function<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	start_pos: usize,
	uniform_kw_span: Option<Span>,
	subroutine_kw_span: Span,
	is_uniform_before_subroutine: bool,
	qualifiers_end_pos: usize,
	association_list: Option<(
		Vec<(super::SubroutineHandle, Ident)>,
		Span,
		Span,
	)>,
	return_type: Either<SubroutineType, Type>,
	ident: Ident,
	l_paren_span: Span,
) {
	fn push_type_decl<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		ctx: &mut Ctx,
		return_type: Either<SubroutineType, Type>,
		ident: Ident,
		association_list: Option<(
			Vec<(super::SubroutineHandle, Ident)>,
			Span,
			Span,
		)>,
		uniform_kw_span: Option<Span>,
		params: Vec<Param>,
		end_pos: usize,
	) {
		// A subroutine type declaration a) cannot have an association list, b) cannot have the `uniform` keyword,
		// c) requires a normal type specifier. If (a) is present we can just ignore it. If (b) is present we can
		// just ignore it. However, if (c) is not met, we can't create the node since the ast node explicitly
		// takes only a normal type.
		if let Some((_, l_paren, r_paren)) = association_list {
			walker.push_nsyntax_diag(Syntax2::ForRemoval {
				item: ForRemoval::AssociationList,
				span: Span::new(l_paren.start, r_paren.end),
				ctx: DiagCtx::SubroutineType,
			});
		}
		if let Some(uniform_kw_span) = uniform_kw_span {
			walker.push_nsyntax_diag(Syntax2::ForRemoval {
				item: ForRemoval::Keyword("uniform"),
				span: uniform_kw_span,
				ctx: DiagCtx::SubroutineType,
			});
		}
		let return_type = match return_type {
			Either::Left(type_) => {
				// Since the subroutine type node takes a subroutine type handle, there is really nothing else we
				// can do other than abort creating anything.
				walker.push_semantic_diag(Semantic::SubTypeFoundSubType(
					type_.ty_specifier_span,
				));
				return;
			}
			Either::Right(type_) => type_,
		};

		ctx.push_new_subroutine_type(
			walker,
			return_type,
			ident,
			params,
			end_pos,
		);
	}

	// Look for any parameters until we hit a closing `)` parenthesis, or other error recovery exit condition.
	#[derive(PartialEq)]
	enum Prev {
		None,
		Param,
		Comma,
		Invalid,
	}
	let mut prev = Prev::None;
	let mut prev_span = l_paren_span;
	let mut params = Vec::new();
	let mut prev_type = None;
	let params_end_pos = loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We expect a `)` to finish the parameter list. Since we know there's nothing else left, the best
				// error recovery strategy is to treat this as a subroutine type declaration. (We are also
				// technically missing the `;` but two overlapping errors should be avoided).
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ')',
					pos: prev_span.end,
					ctx: DiagCtx::ParamList,
				});
				push_type_decl(
					walker,
					ctx,
					return_type,
					ident,
					association_list,
					uniform_kw_span,
					params,
					walker.get_last_span().end,
				);
				return;
			}
		};

		match token {
			Token::Comma => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::Parameter,
						span: prev_span,
					});
				} else if prev == Prev::None {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::Parameter,
						span: l_paren_span,
					});
				}
				prev = Prev::Comma;
				prev_span = token_span;
				continue;
			}
			Token::RParen => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
						item: ExpectedGrammar::Parameter,
						span: prev_span,
					});
				}
				break token_span.end;
			}
			Token::Semi => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();

				// Although we expect a `)` to close the parameter list, since we've encountered a `;` the best
				// error recovery strategy is to allow a subroutine type declaration anyway.
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ')',
					pos: prev_span.end,
					ctx: DiagCtx::ParamList,
				});
				push_type_decl(
					walker,
					ctx,
					return_type,
					ident,
					association_list,
					uniform_kw_span,
					params,
					token_span.end,
				);
				return;
			}
			Token::LBrace => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				// We don't advance because the next check after this loop checks for a `{`.

				// Although we expect a `)` to close the parameter list, since we've encountered a `{` the best
				// error recovery strategy is to continue on anyway (to a function definition).
				walker.push_nsyntax_diag(Syntax2::MissingPunct {
					char: ')',
					pos: prev_span.end,
					ctx: DiagCtx::ParamList,
				});
				break token_span.end;
			}
			_ => {}
		}

		if prev == Prev::Param {
			// We have a parameter after a parameter, though we expect a separating `,` between.
			walker.push_nsyntax_diag(Syntax2::MissingPunct {
				char: ',',
				pos: prev_span.end,
				ctx: DiagCtx::ParamList,
			});
		}
		let param_span_start = token_span.start;

		let qualifiers = try_parse_qualifiers(walker, ctx);

		// We expect a type specifier.
		let mut type_ = if let Some(t) = prev_type.take() {
			t
		} else {
			match try_parse_type_specifier(
				walker,
				ctx,
				[Token::Semi, Token::LBrace],
				true,
			) {
				Ok(type_) => type_,
				Err(Some(expr)) => {
					// We couldn't parse a type specifier. The best error recovery strategy is to ignore this and
					// continue looking for the next parameter.
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::ParamList,
					});
					prev = Prev::Invalid;
					prev_span = Span::new(param_span_start, expr.span.end);
					continue;
				}
				Err(None) => {
					// We immediately have a token that is not an expression. The best error recovery strategy is
					// to ignore this and loop until we hit something recognizable.
					let end_pos = loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::Comma
									|| *token == Token::RParen || *token
									== Token::Semi || *token == Token::LBrace
								{
									break span.end;
								} else {
									walker.advance();
									continue;
								}
							}
							None => break walker.get_last_span().end,
						}
					};
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Something,
						span: Span::new(param_span_start, end_pos),
						ctx: DiagCtx::ParamList,
					});
					prev = Prev::Invalid;
					prev_span = token_span;
					continue;
				}
			}
		};

		// We may have an optional new variable specifier.
		let mut vars = match try_parse_new_var_specifiers(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
			SyntaxType::Parameter,
			true,
		) {
			Ok(v) => v,
			Err(e) => match e {
				Either3::A(next_type) => {
					// We have a type specifier followed by a type specifier. The best error recovery strategy is
					// to treat the first type specifier as an anonymous parameter, and the second as the beginning
					// of a new parameter.
					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					prev_type = Some(next_type);
					continue;
				}
				Either3::B(expr) => {
					// We have an expression after the type specifier, but the expression can't be parsed as a new
					// variable specifier. The best error recovery strategy is to treat the type specifier as an
					// anonymous parameter, and the second expression as invalid.
					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					params.push(Param {
						span: Span::new(
							param_span_start,
							type_.ty_specifier_span.end,
						),
						type_,
						ident: Omittable::None,
					});
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Expr,
						span: expr.span,
						ctx: DiagCtx::ParamList,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
				Either3::C(_) => {
					// We have a type specifier followed by something that can't even be parsed into an expression.
					// The best error recovery strategy is to treat the type specifier as an anonymous parameter,
					// and continue looking. It's possible that we hit a `,` or `)`, in which case it would be
					// erreneous to produce a diagnostic.
					type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
					let param_span = Span::new(
						param_span_start,
						type_.ty_specifier_span.end,
					);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
			},
		};

		// Panic: `vars` has a length of exactly 1
		let super::NewVarSpecifier {
			ident,
			arr,
			eq_span,
			init_expr,
			span: var_span,
		} = vars.destruct();

		// New variable specifiers inside parameter lists cannot have an initialization expression.
		match (eq_span, init_expr) {
			(Some(span), None) => {
				walker.push_nsyntax_diag(Syntax2::ForRemoval {
					item: ForRemoval::VarInitialization,
					span,
					ctx: DiagCtx::ParamList,
				})
			}
			(Some(begin), Some(end)) => {
				walker.push_nsyntax_diag(Syntax2::ForRemoval {
					item: ForRemoval::VarInitialization,
					span: Span::new(begin.start, end.span.end),
					ctx: DiagCtx::ParamList,
				})
			}
			_ => {}
		}

		type_.qualifiers = NonEmpty::from_vec(qualifiers).into();
		let type_ = combine_type_with_arr(type_, arr);
		let param_span = Span::new(param_span_start, var_span.end);
		params.push(Param {
			span: param_span,
			type_,
			ident: Omittable::Some(ident),
		});
		prev = Prev::Param;
		prev_span = param_span;
	};

	// We expect a `;` for a declaration, or a `{` for a definition.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => match token {
			Token::Semi => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				Some(token_span)
			}
			Token::LBrace => {
				// We have a subroutine associated-function definition.
				let l_brace_span = token_span;
				walker.push_colour(l_brace_span, SyntaxType::Punctuation);
				walker.advance();

				// Parse the contents of the body.
				let scope_handle =
					ctx.new_temp_scope(l_brace_span, Some(&params));
				parse_scope(walker, ctx, brace_scope, l_brace_span);
				let body = ctx.replace_temp_scope(scope_handle);

				// A subroutine type declaration a) must have an association list, b) cannot have the `uniform`
				// keyword, c) requires a normal type specifier. If (a) is not present we can just assume it's
				// empty. If (b) is present we can just ignore it. However, if (c) is not met, we can't create the
				// node since the ast node explicitly takes only a normal type.
				let association_list =
					if let Some((association_list, _, _)) = association_list {
						association_list
					} else {
						walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
							item: ExpectedGrammar::AssociationList,
							span: subroutine_kw_span,
						});
						Vec::new()
					};
				if let Some(uniform_kw_span) = uniform_kw_span {
					walker.push_nsyntax_diag(Syntax2::ForRemoval {
						item: ForRemoval::Keyword("uniform"),
						span: uniform_kw_span,
						ctx: DiagCtx::SubroutineAssociatedFn,
					});
				}
				let return_type = match return_type {
					Either::Left(type_) => {
						walker.push_semantic_diag(Semantic::SubFnFoundSubType(
							type_.ty_specifier_span,
						));
						return;
					}
					Either::Right(type_) => type_,
				};

				let end_pos = body.span.end;
				ctx.push_new_associated_subroutine_fn_def(
					walker,
					scope_handle,
					start_pos,
					association_list,
					return_type,
					ident,
					params,
					body,
					end_pos,
				);
				return;
			}
			_ => None,
		},
		None => None,
	};

	// We have a subroutine type declaration.

	push_type_decl(
		walker,
		ctx,
		return_type,
		ident,
		association_list,
		uniform_kw_span,
		params,
		semi_span.map(|s| s.end).unwrap_or(params_end_pos),
	);
	if semi_span.is_none() {
		walker.push_nsyntax_diag(Syntax2::MissingPunct {
			char: ';',
			pos: params_end_pos,
			ctx: DiagCtx::SubroutineType,
		});
		seek_next_stmt(walker);
	}
}

/// Tries to parse a variable definition. This **does not** push anything into the context, but just returns the
/// results to be manually processed as appropriate.
fn try_parse_var_def<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	name_highlighting: SyntaxType,
	type_: Option<Type>,
) -> Result<
	(Type, NonEmpty<super::NewVarSpecifier>, Option<Span>),
	Either<
		(Vec<Qualifier>, Option<Expr>),
		(Vec<Qualifier>, Type, Either3<Type, Expr, ()>),
	>,
> {
	let continuing_prev_type = type_.is_some();
	let (qualifiers, mut type_) = if let Some(type_) = type_ {
		(Vec::new(), type_)
	} else {
		let qualifiers = try_parse_qualifiers(walker, ctx);

		// We attempt to parse a type specifier at the current position. If that fails, we return an error.
		let type_ =
			match try_parse_type_specifier(walker, ctx, [Token::Semi], false) {
				Ok(type_) => type_,
				Err(expr) => {
					return Err(Either::Left((qualifiers, expr)));
				}
			};
		(qualifiers, type_)
	};

	// This must be a variable definition, or a function declaration/definition (which we wouldn't want).

	// We expect new variable specifier(s) after the type specifier.
	let var_specifiers = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		name_highlighting,
		false,
	) {
		Ok(v) => v,
		Err(e) => {
			if continuing_prev_type {
				walker.push_nsyntax_diag(Syntax2::ExpectedGrammar {
					item: ExpectedGrammar::AfterType,
					span: type_.ty_specifier_span,
				});
			}
			return Err(Either::Right((qualifiers, type_, e)));
		}
	};

	type_.qualifiers = NonEmpty::from_vec(qualifiers).into();

	let last_var_spec_span = var_specifiers.last().span;

	// We expect a `;` after the new variable specifier(s);
	let semi_span = match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::Semi {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				Some(token_span)
			} else {
				None
			}
		}
		None => None,
	};

	Ok((type_, var_specifiers, semi_span))
}

/// Combines the disjointed type specifier with a type.
pub(super) fn combine_type_with_arr(
	type_: Type,
	arr: Option<Spanned<Vec<ArrSize>>>,
) -> Type {
	let Some((arr, arr_span)) = arr else {
		return type_;
	};

	let mut sizes = arr;
	let Type {
		ty,
		qualifiers,
		ty_specifier_span,
		disjointed_span: _,
	} = type_;
	let handle = match ty {
		TypeTy::Single(h) => h,
		TypeTy::Array(h, i) => {
			sizes.push(i);
			h
		}
		TypeTy::Array2D(h, i, j) => {
			sizes.push(i);
			sizes.push(j);
			h
		}
		TypeTy::ArrayND(h, mut v) => {
			sizes.append(&mut v);
			h
		}
	};

	Type {
		ty_specifier_span,
		disjointed_span: Omittable::Some(arr_span),
		ty: match sizes.len() {
			0 => TypeTy::Single(handle),
			1 => TypeTy::Array(handle, sizes.remove(0)),
			2 => {
				let b = sizes.remove(0);
				let a = sizes.remove(0);
				TypeTy::Array2D(handle, a, b)
			}
			_ => TypeTy::ArrayND(handle, sizes),
		},
		qualifiers,
	}
}

/// Combines the disjointed type specifier with a subroutine type.
pub(super) fn combine_subroutine_type_with_arr(
	type_: SubroutineType,
	arr: Option<Spanned<Vec<ArrSize>>>,
) -> SubroutineType {
	let Some((arr, arr_span)) = arr else {
		return type_;
	};

	let mut sizes = arr;
	let SubroutineType {
		ty,
		qualifiers,
		ident_span,
		ty_specifier_span,
		disjointed_span: _,
	} = type_;
	let handle = match ty {
		SubroutineTypeTy::Single(h) => h,
		SubroutineTypeTy::Array(h, i) => {
			sizes.push(i);
			h
		}
		SubroutineTypeTy::Array2D(h, i, j) => {
			sizes.push(i);
			sizes.push(j);
			h
		}
		SubroutineTypeTy::ArrayND(h, mut v) => {
			sizes.append(&mut v);
			h
		}
	};

	SubroutineType {
		ident_span,
		ty_specifier_span,
		disjointed_span: Omittable::Some(arr_span),
		ty: match sizes.len() {
			0 => SubroutineTypeTy::Single(handle),
			1 => SubroutineTypeTy::Array(handle, sizes.remove(0)),
			2 => {
				let b = sizes.remove(0);
				let a = sizes.remove(0);
				SubroutineTypeTy::Array2D(handle, a, b)
			}
			_ => SubroutineTypeTy::ArrayND(handle, sizes),
		},
		qualifiers,
	}
}
