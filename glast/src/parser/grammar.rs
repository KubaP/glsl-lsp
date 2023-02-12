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
		ExprDiag, PreprocDefineDiag, PreprocExtDiag, PreprocLineDiag,
		PreprocVersionDiag, Semantic, StmtDiag, Syntax,
	},
	lexer::{
		preprocessor::{
			ExtensionToken, LineToken, TokenStream as PreprocStream,
			VersionToken,
		},
		OpTy, Token,
	},
	syntax::{SyntaxModifiers, SyntaxToken, SyntaxType},
	Either, Span, Spanned,
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

/// Invalidates a set of qualifiers.
///
/// This function is used to emit a diagnostic about the use of qualifiers before a statement which doesn't support
/// qualifiers.
fn invalidate_qualifiers<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	qualifiers: Vec<Qualifier>,
) {
	if let Some(q) = qualifiers.last() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::FoundQualifiersBeforeStmt(Span::new(
				qualifiers.first().unwrap().span.start,
				q.span.end,
			)),
		));
	}
}

/// Parses an individual statement at the current position.
pub(super) fn parse_stmt<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
) {
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
			if !qualifiers.is_empty() {
				ctx.push_node(Node {
					span: Span::new(
						qualifiers.first().unwrap().span.start,
						qualifiers.last().unwrap().span.end,
					),
					ty: NodeTy::Qualifiers(qualifiers),
				});
			} else {
				ctx.push_node(Node {
					span: semi_span,
					ty: NodeTy::Empty,
				});
			}
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
				|span| Syntax::Stmt(StmtDiag::BreakExpectedSemiAfterKw(span)),
			)
		}
		Token::Continue => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				ctx,
				token_span,
				|| NodeTy::Continue,
				|span| {
					Syntax::Stmt(StmtDiag::ContinueExpectedSemiAfterKw(span))
				},
			);
		}
		Token::Discard => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				ctx,
				token_span,
				|| NodeTy::Discard,
				|span| Syntax::Stmt(StmtDiag::DiscardExpectedSemiAfterKw(span)),
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
		_ => {} /* _ => try_parse_definition_declaration_expr(
					walker, ctx, qualifiers, false,
				), */
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
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ScopeMissingRBrace(
					l_brace_span,
					walker.get_last_span().next_single_width(),
				),
			));
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
						(Some(e), mut syntax, mut semantic, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut syntax);
							walker.append_semantic_diags(&mut semantic);
							e
						}
						(None, _, _, _) => {
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
/*
/// Tries to parse a variable definition or a function declaration/definition, an expression statement, or an
/// interface block.
///
/// This function attempts to look for a statement at the current position. If this fails, error recovery till the
/// next clear statement delineation occurs.
///
/// - `parsing_last_for_stmt` - Set to `true` if this function is attempting to parse the increment statement in a
///   for loop header.
fn try_parse_definition_declaration_expr<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	qualifiers: Vec<Qualifier>,
	parsing_last_for_stmt: bool,
) {
	// We attempt to parse a type specifier at the current position.
	let e = match try_parse_type_specifier(walker, ctx, [Token::Semi]) {
		Ok((mut type_, mut syntax, mut semantic, mut colours)) => {
			// This must be a variable definition or function declaration/definition.
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);

			let (token, token_span) = match walker.peek() {
				Some(t) => t,
				None => {
					// We are lacking an identifier after the type.
					invalidate_qualifiers(walker, qualifiers);
					if parsing_last_for_stmt {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedRParenAfterStmts(
								type_.span.next_single_width(),
							),
						))
					} else {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::TypeExpectedIdentsAfterType(
								type_.span.next_single_width(),
							),
						));
					}
					return;
				}
			};

			// Check whether we have a function declaration/definition.
			match token {
				Token::Ident(i) => match walker.lookahead_1() {
					Some(next) => match next.0 {
						Token::LParen => {
							// We have a function declaration/definition.
							type_.qualifiers = qualifiers;
							let l_paren_span = next.1;
							let ident = Ident {
								name: i.clone(),
								span: token_span,
							};
							walker
								.push_colour(token_span, SyntaxType::Function);
							walker.advance();
							walker.push_colour(next.1, SyntaxType::Punctuation);
							walker.advance();
							parse_function(
								walker,
								ctx,
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
				Token::RParen if parsing_last_for_stmt => {
					// We are lacking an identifier.
					invalidate_qualifiers(walker, qualifiers);
					if parsing_last_for_stmt {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedRParenAfterStmts(
								type_.span.next_single_width(),
							),
						))
					} else {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::TypeExpectedIdentsAfterType(
								type_.span.next_single_width(),
							),
						));
					}
					return;
				}
				_ => {}
			}

			// We don't have a function declaration/definition, so this must be a variable definition.

			let ident_info = match try_parse_new_decl_def_idents_with_type_info(
				walker,
				ctx,
				[Token::Semi],
				false,
				if walker.parsing_struct {
					SyntaxType::Field
				} else {
					SyntaxType::Variable
				},
			) {
				Ok((i, mut syntax, mut semantic, mut colours)) => {
					walker.append_colours(&mut colours);
					walker.append_syntax_diags(&mut syntax);
					walker.append_semantic_diags(&mut semantic);
					i
				}
				Err((expr, mut syntax, mut semantic, mut colours)) => {
					walker.append_colours(&mut colours);
					walker.append_syntax_diags(&mut syntax);
					walker.append_semantic_diags(&mut semantic);

					if let Some(expr) = expr {
						// We have a type specifier, followed by a second expression but the second expression
						// isn't one or more identifiers suitable for a variable definition. We treat the first
						// expression as an incomplete type grammar and the second expression as a standalone
						// expression.
						invalidate_qualifiers(walker, qualifiers);
						if parsing_last_for_stmt {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::ForExpectedRParenAfterStmts(
									expr.span.next_single_width(),
								),
							))
						} else {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::TypeExpectedIdentsAfterType(
									type_.span.next_single_width(),
								),
							));
						}
						ctx.push_node(Node {
							span: expr.span,
							ty: NodeTy::Expr(expr),
						});
						seek_next_stmt(walker);
					} else {
						// We have a type specifier followed by something that can't be parsed as any expression.
						invalidate_qualifiers(walker, qualifiers);
						if parsing_last_for_stmt {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::ForExpectedRParenAfterStmts(
									type_.span.next_single_width(),
								),
							))
						} else {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::TypeExpectedIdentsAfterType(
									type_.span.next_single_width(),
								),
							));
						}
					}
					return;
				}
			};
			let ident_span = ident_info.last().unwrap().0.span;
			type_.qualifiers = qualifiers;

			fn var_def(
				type_: Type,
				idents: Vec<(Ident, Vec<ArrSize>, Span)>,
				end_pos: usize,
			) -> (Vec<(Type, Ident)>, Node) {
				let span = Span::new(type_.span.start, end_pos);
				let mut vars = combine_type_with_idents(type_, idents);
				match vars.len() {
					1 => {
						let (type_, ident) = vars.remove(0);
						(
							vec![(type_.clone(), ident.clone())],
							Node {
								span,
								ty: NodeTy::VarDef { type_, ident },
							},
						)
					}
					_ => (
						vars.clone(),
						Node {
							span,
							ty: NodeTy::VarDefs(vars),
						},
					),
				}
			}

			fn var_def_init(
				type_: Type,
				idents: Vec<(Ident, Vec<ArrSize>, Span)>,
				value: Option<Expr>,
				end_pos: usize,
			) -> (Vec<(Type, Ident)>, Node) {
				let span = Span::new(type_.span.start, end_pos);
				let mut vars = combine_type_with_idents(type_, idents);
				match vars.len() {
					1 => {
						let (type_, ident) = vars.remove(0);
						(
							vec![(type_.clone(), ident.clone())],
							Node {
								span,
								ty: NodeTy::VarDefInit {
									type_,
									ident,
									value: value.unwrap(),
								},
							},
						)
					}
					_ => (
						vars.clone(),
						Node {
							span,
							ty: NodeTy::VarDefsInits(vec![]),
						},
					),
				}
			}

			// Consume the `;` for a definition, or a `=` for a definition with initialization.
			let (token, token_span) = match walker.peek() {
				Some(t) => t,
				None => {
					// We have something that matches the start of a variable definition. Since we have neither the
					// `;` or `=`, we assume that this is a definition without initialization that is missing the
					// semi-colon.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::VarDefExpectedSemiOrEqAfterIdents(
							ident_span.next_single_width(),
						),
					));
					ctx.push_new_variables(
						var_def(type_, ident_info, ident_span.end),
						(SyntaxType::Variable, SyntaxModifiers::empty()),
					);
					return;
				}
			};
			if *token == Token::Semi {
				// We have a variable definition without initialization.
				let semi_span = token_span;
				walker.push_colour(semi_span, SyntaxType::Punctuation);
				walker.advance();
				ctx.push_new_variables(
					var_def(type_, ident_info, semi_span.end),
					(SyntaxType::Variable, SyntaxModifiers::empty()),
				);
				return;
			} else if *token == Token::Op(OpTy::Eq) {
				// We have a variable definition with initialization.
				let eq_span = token_span;
				walker.push_colour(eq_span, SyntaxType::Operator);
				walker.advance();

				// Consume the value expression.
				let value_expr =
					match parse_expr(walker, ctx, Mode::Default, [Token::Semi])
					{
						(Some(e), mut syntax, mut semantic, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut syntax);
							walker.append_semantic_diags(&mut semantic);
							e
						}
						(None, _, _, _) => {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::VarDefInitExpectedValueAfterEq(
									eq_span.next_single_width(),
								),
							));
							ctx.push_new_variables(
								var_def_init(
									type_,
									ident_info,
									None,
									eq_span.end,
								),
								(
									SyntaxType::Variable,
									SyntaxModifiers::empty(),
								),
							);
							seek_next_stmt(walker);
							return;
						}
					};

				// Consume the semi-colon.
				let (token, token_span) = match walker.peek() {
					Some(t) => t,
					None => {
						let value_span = value_expr.span;
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::VarDefInitExpectedSemiAfterValue(
								value_span.next_single_width(),
							),
						));
						ctx.push_new_variables(
							var_def_init(
								type_,
								ident_info,
								Some(value_expr),
								value_span.end,
							),
							(SyntaxType::Variable, SyntaxModifiers::empty()),
						);
						return;
					}
				};
				if *token == Token::Semi {
					let semi_span = token_span;
					walker.push_colour(semi_span, SyntaxType::Punctuation);
					walker.advance();
					ctx.push_new_variables(
						var_def_init(
							type_,
							ident_info,
							Some(value_expr),
							semi_span.end,
						),
						(SyntaxType::Variable, SyntaxModifiers::empty()),
					);
					return;
				} else {
					let end_span = token_span;
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::VarDefInitExpectedSemiAfterValue(
							end_span.next_single_width(),
						),
					));
					ctx.push_new_variables(
						var_def_init(
							type_,
							ident_info,
							Some(value_expr),
							end_span.end,
						),
						(SyntaxType::Variable, SyntaxModifiers::empty()),
					);
					seek_next_stmt(walker);
					return;
				}
			} else {
				// We have something that matches the start of a variable definition. Since we have neither the `;`
				// or `=`, we assume that this is a definition without initialization which is missing the
				// semi-colon.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::VarDefExpectedSemiOrEqAfterIdents(
						ident_span.next_single_width(),
					),
				));
				ctx.push_new_variables(
					var_def(type_, ident_info, ident_span.end),
					(SyntaxType::Variable, SyntaxModifiers::empty()),
				);
				seek_next_stmt(walker);
				return;
			}

			return;
		}
		Err(e) => e,
	};

	let (Some(expr), mut syntax, mut semantic, mut colours) = e else {
		// Could not parse any expression, so this cannot be a valid statement at all.
		invalidate_qualifiers(walker, qualifiers);
		seek_next_stmt(walker);
		return;
	};

	// FIXME: if expr == ident, and next is `{` We have an expression which cannot be parsed as a type specifier,
	// so this cannot start a variable definition nor a function declaration or definition; it must therefore be a
	// standalone expression statement or an interface block.
	/* match walker.peek() {
		   Some((token, token_span)) => match token {
			   Token::LBrace => {
				   // We have an interface block.

				   // Interface blocks can begin with one of the following:
				   // in
				   // out
				   // patch in
				   // patch out
				   // uniform
				   // buffer
				   // A layout() qualifier may precede any of these.
				   let valid_qualifiers = if qualifiers.len() == 1 {
					   match &qualifiers[0].ty {
						   QualifierTy::In
						   | QualifierTy::Out
						   | QualifierTy::Uniform
						   | QualifierTy::Buffer => true,
						   _ => false,
					   }
				   } else if qualifiers.len() == 2 {
					   match (&qualifiers[0].ty, &qualifiers[1].ty) {
						   (QualifierTy::Patch, QualifierTy::In)
						   | (QualifierTy::Patch, QualifierTy::Out)
						   | (QualifierTy::Layout(_), QualifierTy::In)
						   | (QualifierTy::Layout(_), QualifierTy::Out)
						   | (QualifierTy::Layout(_), QualifierTy::Uniform)
						   | (QualifierTy::Layout(_), QualifierTy::Buffer) => true,
						   (_, _) => false,
					   }
				   } else if qualifiers.len() == 3 {
					   match (
						   &qualifiers[0].ty,
						   &qualifiers[1].ty,
						   &qualifiers[2].ty,
					   ) {
						   (
							   QualifierTy::Layout(_),
							   QualifierTy::Patch,
							   QualifierTy::In,
						   )
						   | (
							   QualifierTy::Layout(_),
							   QualifierTy::Patch,
							   QualifierTy::Out,
						   ) => true,
						   (_, _, _) => false,
					   }
				   } else {
					   false
				   };
				   if !valid_qualifiers {
					   // TODO: Syntax error for invalid qualifiers before interface block.
					   return;
				   }
				   let l_brace_span = token_span;
				   walker.append_colours(&mut start_colours);
				   start_syntax.retain(|e| {
					   if let Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
						   _,
						   _,
					   )) = e
					   {
						   false
					   } else {
						   true
					   }
				   });
				   walker.append_syntax_diags(&mut start_syntax);
				   walker.append_semantic_diags(&mut start_semantic);
				   walker.push_colour(l_brace_span, SyntaxType::Punctuation);
				   walker.advance();
				   parse_interface_block(
					   walker,
					   ctx,
					   qualifiers,
					   start,
					   l_brace_span,
				   );
				   return;
			   }
			   _ => {}
		   },
		   None => {}
	   }
	*/
	// We have a standalone expression statement.
	invalidate_qualifiers(walker, qualifiers);
	walker.append_colours(&mut colours);
	walker.append_syntax_diags(&mut syntax);
	walker.append_semantic_diags(&mut semantic);

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::ExprStmtExpectedSemiAfterExpr(
				expr.span.next_single_width(),
			),
		));
		seek_next_stmt(walker);
	}

	ctx.push_node(Node {
		span: if let Some(semi_span) = semi_span {
			Span::new(expr.span.start, semi_span.end)
		} else {
			expr.span
		},
		ty: NodeTy::Expr(expr),
	});
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
	let param_end_span = loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not yet finished parsing the parameter list, but we treat this as a valid declaration
				// since that's the closest match.
				let span = Span::new(return_type.span.start, prev_span.end);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				ctx.push_node(Node {
					span,
					ty: NodeTy::FnDecl {
						return_type,
						ident,
						params,
					},
				});
				return;
			}
		};

		match token {
			Token::Comma => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				} else if prev == Prev::None {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamBetweenParenComma(
							Span::new_between(l_paren_span, token_span),
						),
					));
				}
				prev = Prev::Comma;
				prev_span = token_span;
				continue;
			}
			Token::RParen => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				}
				break token_span;
			}
			Token::Semi => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				// We have not yet finished parsing the parameter list but we've encountered a semi-colon. We treat
				// this as a valid declaration since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				ctx.push_node(Node {
					span: Span::new(return_type.span.start, token_span.end),
					ty: NodeTy::FnDecl {
						return_type,
						ident,
						params,
					},
				});
				return;
			}
			Token::LBrace => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				// We don't advance because the next check after this loop checks for a l-brace.

				// We have not yet finished parsing the parameter list but we've encountered a l-brace. We treat
				// this as a potentially valid definition since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				break token_span;
			}
			_ => {}
		}

		if prev == Prev::Param {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ParamsExpectedCommaAfterParam(
					prev_span.next_single_width(),
				),
			));
		}
		let param_span_start = token_span.start;

		let qualifiers = try_parse_qualifiers(walker, ctx);

		// Consume the type specifier.
		let mut type_ = match try_parse_type_specifier(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
		) {
			Ok((type_, mut syntax, mut semantic, mut colours)) => {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				type_
			}
			Err((expr, mut syntax, mut semantic, mut colours)) => {
				if let Some(expr) = expr {
					// We have an expression which cannot be parsed into a type. We ignore this and continue
					// searching for the next parameter.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidTypeExpr(expr.span),
					));
					prev = Prev::Invalid;
					prev_span = Span::new(param_span_start, expr.span.end);
					continue;
				} else {
					// We immediately have a token that is not an expression. We ignore this and loop until we hit
					// something recognizable.
					let end_span = loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::Comma
									|| *token == Token::RParen || *token
									== Token::Semi || *token == Token::LBrace
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
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidTypeExpr(Span::new(
							param_span_start,
							end_span.end,
						)),
					));
					prev = Prev::Invalid;
					prev_span = token_span;
					continue;
				}
			}
		};

		// Look for the optional ident.
		let ident = match try_parse_new_decl_def_idents_with_type_info(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
			true,
			SyntaxType::Parameter,
		) {
			Ok((i, mut syntax, mut semantic, mut colours)) => {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				i
			}
			Err((expr, mut syntax, mut semantic, mut colours)) => {
				if let Some(expr) = expr {
					// We have a second expression after the first expression, but the second expression can't be
					// converted to an identifier for the parameter. We treat the first type expression as an
					// anonymous parameter, and the second expression as invalid.
					let param_span =
						Span::new(param_span_start, type_.span.end);
					type_.qualifiers = qualifiers;
					params.push(Param {
						span: Span::new(param_span_start, type_.span.end),
						type_,
						ident: Omittable::None,
					});
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidIdentExpr(expr.span),
					));
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				} else {
					// We have a first expression and then something that is not an expression. We treat this as an
					// anonymous parameter, whatever the current token is will be dealt with in the next iteration.
					type_.qualifiers = qualifiers;
					let param_span =
						Span::new(param_span_start, type_.span.end);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
			}
		};
		let ident_span = ident[0].0.span;

		type_.qualifiers = qualifiers;
		let (type_, ident) = combine_type_with_idents(type_, ident).remove(0);
		let param_span = Span::new(param_span_start, ident_span.end);
		params.push(Param {
			span: param_span,
			type_,
			ident: Omittable::Some(ident),
		});
		prev = Prev::Param;
		prev_span = param_span;
	};

	// Consume the `;` for a declaration or a `{` for a definition.
	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// This branch will only be triggered if we exited the param loop with a `)`, it will not trigger if we
			// exit with a `{` because that token is not consumed.

			// We are missing a `;` for a declaration. We treat this as a declaration since that's the closest
			// match.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::FnExpectedSemiOrLBraceAfterParams(
					param_end_span.next_single_width(),
				),
			));
			ctx.push_new_function_decl(
				ident.clone(),
				params.iter().cloned().map(|p| p.into()).collect(),
				return_type.clone(),
				Node {
					span: Span::new(return_type.span.start, param_end_span.end),
					ty: NodeTy::FnDecl {
						return_type,
						ident,
						params,
					},
				},
			);
			return;
		}
	};
	if *token == Token::Semi {
		// We have a declaration.
		walker.push_colour(token_span, SyntaxType::Punctuation);
		walker.advance();
		ctx.push_new_function_decl(
			ident.clone(),
			params.iter().cloned().map(|p| p.into()).collect(),
			return_type.clone(),
			Node {
				span: Span::new(return_type.span.start, param_end_span.end),
				ty: NodeTy::FnDecl {
					return_type,
					ident,
					params,
				},
			},
		);
	} else if *token == Token::LBrace {
		// We have a definition.
		let l_brace_span = token_span;
		walker.push_colour(l_brace_span, SyntaxType::Punctuation);
		walker.advance();

		let scope_handle = ctx.new_temp_scope(l_brace_span, Some(&params));
		parse_scope(walker, ctx, brace_scope, l_brace_span);
		let body = ctx.replace_temp_scope(scope_handle);
		ctx.push_new_function_def(
			scope_handle,
			ident.clone(),
			params.iter().cloned().map(|p| p.into()).collect(),
			return_type.clone(),
			Node {
				span: Span::new(return_type.span.start, body.span.end),
				ty: NodeTy::FnDef {
					return_type,
					ident,
					params,
					body,
				},
			},
		);
	} else {
		// We are missing a `;` for a declaration. We treat this as a declaration since that's the closest match.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::FnExpectedSemiOrLBraceAfterParams(
				param_end_span.next_single_width(),
			),
		));
		ctx.push_new_function_decl(
			ident.clone(),
			params.iter().cloned().map(|p| p.into()).collect(),
			return_type.clone(),
			Node {
				span: Span::new(return_type.span.start, param_end_span.end),
				ty: NodeTy::FnDecl {
					return_type,
					ident,
					params,
				},
			},
		);
		seek_next_stmt(walker);
	}
}
 */
/// Parses a subroutine type declaration, subroutine associated function definition, or a subroutine uniform
/// definition.
///
/// This function assumes that the `subroutine` keyword is not yet consumed.
fn parse_subroutine<'a, P: TokenStreamProvider<'a>>(
	walker: &mut Walker<'a, P>,
	ctx: &mut Ctx,
	kw_span: Span,
	mut qualifiers: Vec<Qualifier>,
) {
	let subroutine_kw_span = kw_span;
	let start_pos = if let Some(q) = qualifiers.first() {
		q.span.start
	} else {
		subroutine_kw_span.start
	};
	walker.push_colour(kw_span, SyntaxType::Keyword);
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
							walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineAssociatedListExpectedRParen(
							prev_span.next_single_width(),
						),
					));
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
								walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentAfterComma(
								Span::new_between(prev_span, token_span),
							),
						));
							} else if prev == Prev::None {
								walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentBetweenParenComma(
								Span::new_between(l_paren_span, token_span),
							),
						));
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
								walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentAfterComma(
								Span::new_between(prev_span, token_span),
							),
						));
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
							walker.push_colour(token_span, SyntaxType::Ident);
							walker.advance();
							if prev == Prev::Ident {
								walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SubroutineAssociatedListExpectedCommaAfterIdent(
							prev_span.next_single_width()
						)));
							}
							prev = Prev::Ident;
							prev_span = token_span;
							continue;
						}
						_ => {
							walker.push_colour(token_span, SyntaxType::Invalid);
							walker.advance();
							prev = Prev::Invalid;
							prev_span = token_span;
						}
					}
				};

				Some((associations, l_paren_span, r_paren_span))
			}
			_ => None,
		},
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubroutineExpectedTypeFuncUniformAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// We can have qualifiers after the `subroutine` keyword, though only for subroutine uniform definitions.
	let qualifiers_end_pos = if let Some(q) = qualifiers.last() {
		q.span.end
	} else {
		kw_span.end
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
	qualifier_span_start: usize,
	name: Ident,
	l_brace_span: Span,
) {
	// Parse the contents of the body.
	let scope_handle = ctx.new_temp_scope(l_brace_span, None);
	walker.parsing_struct = true;
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	walker.parsing_struct = false;
	let body = ctx.take_temp_scope(scope_handle);

	if body.contents.is_empty() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::InterfaceExpectedAtLeastOneStmtInBody(body.span),
		));
	}
	let mut fields = Vec::new();
	for handle in body.contents.iter() {
		let node = ctx.get_node(*handle);
		match &node.ty {
			NodeTy::VarDef { type_, ident } => {
				fields.push(super::StructField {
					type_: type_.clone(),
					name: Omittable::Some(ident.name.clone()),
					refs: vec![ident.span],
				});
			}
			NodeTy::VarDefs(defs) => {
				for def in defs {
					fields.push(super::StructField {
						type_: def.0.clone(),
						name: Omittable::Some(def.1.name.clone()),
						refs: vec![name.span],
					});
				}
			}
			NodeTy::VarDefInit {
				type_,
				ident,
				value,
			} => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructMemberCannotBeInitialized(node.span),
				));
				fields.push(super::StructField {
					type_: type_.clone(),
					name: Omittable::Some(ident.name.clone()),
					refs: vec![ident.span],
				});
			}
			NodeTy::VarDefsInits(vars) => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructMemberCannotBeInitialized(node.span),
				));
				for var in vars {
					fields.push(super::StructField {
						type_: var.0.clone(),
						name: Omittable::Some(var.1.name.clone()),
						refs: vec![name.span],
					});
				}
			}
			_ => walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::InterfaceInvalidStmtInBody(node.span),
			)),
		}
	}

	// Look for optional instances.
	let instances = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		SyntaxType::Variable,
	) {
		Ok((vars, mut syntax, mut semantic, mut colours)) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(
				vars.into_iter()
					.map(
						|super::NewVarSpecifier {
						     ident,
						     arr,
						     eq_span,
						     init_expr,
						     span,
						 }| (ident, arr.unwrap_or(Vec::new()), span),
					)
					.collect::<Vec<_>>(),
			)
		}
		Err((expr, mut syntax, mut semantic, mut colours)) => {
			if let Some(expr) = expr {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				/* walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructExpectedInstanceOrSemiAfterBody(expr.span),
				));
				ctx.push_new_struct(
					name.clone(),
					fields,
					Node {
						span: Span::new(struct_span_start, body.span.end),
						ty: NodeTy::StructDef {
							qualifiers,
							name,
							body,
							instances: Vec::new(),
						},
					},
					Vec::new(),
					false,
				); */
				seek_next_stmt(walker);
				return;
			}
			None
		}
	};

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		if let Some(ref i) = instances {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedSemiAfterInstance(
					i.last().unwrap().0.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedInstanceOrSemiAfterBody(
					body.span.next_single_width(),
				),
			));
		}
	}

	/* ctx.push_node(Node {
		span: Span::new(
			interface_span_start,
			if let Some(semi_span) = semi_span {
				semi_span.end
			} else {
				if let Omittable::Some(ref i) = instance {
					i.span.end
				} else {
					body.span.end
				}
			},
		),
		ty: NodeTy::InterfaceDef {
			qualifiers,
			ident,
			body,
			instance,
		},
	}); */
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
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the struct name.
	let name = match try_parse_new_name(
		walker,
		ctx,
		[Token::LBrace, Token::Semi],
		SyntaxType::Struct,
	) {
		Ok((i, mut s)) => {
			walker.semantic_diags.append(&mut s);
			i
		}
		Err(_) => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedNameAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	let struct_span_start = if let Some(q) = qualifiers.first() {
		q.span.start
	} else {
		kw_span.start
	};

	// Consume the `{`.
	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// We don't create a struct declaration because it would result in two errors that would reduce
			// clarity.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedLBraceAfterName(
					name.span.next_single_width(),
				),
			));
			return;
		}
	};
	let l_brace_span = if *token == Token::LBrace {
		walker.push_colour(token_span, SyntaxType::Punctuation);
		walker.advance();
		token_span
	} else if *token == Token::Semi {
		// We have a declaration, (which is illegal).
		let span = Span::new(struct_span_start, token_span.end);
		walker.push_colour(token_span, SyntaxType::Punctuation);
		walker.push_syntax_diag(Syntax::Stmt(StmtDiag::StructDeclIsIllegal(
			span,
		)));
		walker.advance();
		ctx.push_new_struct(
			name.clone(),
			Vec::new(),
			Node {
				span,
				ty: NodeTy::StructDecl { qualifiers, name },
			},
			Vec::new(),
			false,
		);
		return;
	} else {
		// We have something else entirely. We don't create a struct declaration because it would just create a
		// second error over the first, and that would be less clear.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedLBraceAfterName(
				name.span.next_single_width(),
			),
		));
		return;
	};

	// Parse the contents of the body.
	let scope_handle = ctx.new_temp_scope(l_brace_span, None);
	walker.parsing_struct = true;
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	walker.parsing_struct = false;
	let body = ctx.take_temp_scope(scope_handle);

	if body.contents.is_empty() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedAtLeastOneMemberInBody(body.span),
		));
	}
	let mut fields = Vec::new();
	for handle in body.contents.iter() {
		let node = ctx.get_node(*handle);
		match &node.ty {
			NodeTy::VarDef { type_, ident } => {
				fields.push(super::StructField {
					type_: type_.clone(),
					name: Omittable::Some(ident.name.clone()),
					refs: vec![ident.span],
				});
			}
			NodeTy::VarDefs(defs) => {
				for def in defs {
					fields.push(super::StructField {
						type_: def.0.clone(),
						name: Omittable::Some(def.1.name.clone()),
						refs: vec![name.span],
					});
				}
			}
			NodeTy::VarDefInit {
				type_,
				ident,
				value,
			} => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructMemberCannotBeInitialized(node.span),
				));
				fields.push(super::StructField {
					type_: type_.clone(),
					name: Omittable::Some(ident.name.clone()),
					refs: vec![ident.span],
				});
			}
			NodeTy::VarDefsInits(vars) => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructMemberCannotBeInitialized(node.span),
				));
				for var in vars {
					fields.push(super::StructField {
						type_: var.0.clone(),
						name: Omittable::Some(var.1.name.clone()),
						refs: vec![name.span],
					});
				}
			}
			_ => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructInvalidStmtInBody(node.span),
				));
			}
		}
	}

	// Look for optional instances.
	let instances = match try_parse_new_var_specifiers(
		walker,
		ctx,
		[Token::Semi],
		SyntaxType::Variable,
	) {
		Ok((vars, mut syntax, mut semantic, mut colours)) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(
				vars.into_iter()
					.map(
						|super::NewVarSpecifier {
						     ident,
						     arr,
						     eq_span,
						     init_expr,
						     span,
						 }| (ident, arr.unwrap_or(Vec::new()), span),
					)
					.collect::<Vec<_>>(),
			)
		}
		Err((expr, mut syntax, mut semantic, mut colours)) => {
			if let Some(expr) = expr {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructExpectedInstanceOrSemiAfterBody(expr.span),
				));
				ctx.push_new_struct(
					name.clone(),
					fields,
					Node {
						span: Span::new(struct_span_start, body.span.end),
						ty: NodeTy::StructDef {
							qualifiers,
							name,
							body,
							instances: Vec::new(),
						},
					},
					Vec::new(),
					false,
				);
				seek_next_stmt(walker);
				return;
			}
			None
		}
	};

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		if let Some(ref i) = instances {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedSemiAfterInstance(
					i.last().unwrap().0.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedInstanceOrSemiAfterBody(
					body.span.next_single_width(),
				),
			));
		}
	}

	let struct_span_end = if let Some(semi_span) = semi_span {
		semi_span.end
	} else {
		if let Some(ref i) = instances {
			i.last().unwrap().2.end
		} else {
			body.span.end
		}
	};

	let handle = ctx.get_handle_for_next_struct();
	let (instances, var_instances) = if let Some(instances) = instances {
		let (mut a, mut b) = (Vec::new(), Vec::new());
		for (ident, mut arr, span) in instances.into_iter() {
			let type_ = Type {
				span,
				qualifiers: Vec::new(),
				ty: match arr.len() {
					0 => TypeTy::Single(Either::Right(handle)),
					1 => TypeTy::Array(Either::Right(handle), arr.remove(0)),
					2 => TypeTy::Array2D(
						Either::Right(handle),
						arr.remove(0),
						arr.remove(0),
					),
					_ => TypeTy::ArrayND(Either::Right(handle), arr),
				},
			};
			a.push(type_.clone());
			b.push((ident, type_));
		}

		(a, b)
	} else {
		(Vec::new(), Vec::new())
	};

	let is_shader_in_out = qualifiers
		.iter()
		.find(|q| match q.ty {
			QualifierTy::In
			| QualifierTy::Out
			| QualifierTy::Uniform
			| QualifierTy::Attribute => true,
			_ => false,
		})
		.is_some();
	ctx.push_new_struct(
		name.clone(),
		fields,
		Node {
			span: Span::new(struct_span_start, struct_span_end),
			ty: NodeTy::StructDef {
				qualifiers,
				name,
				body,
				instances,
			},
		},
		var_instances,
		is_shader_in_out,
	);
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
				(Some(e), mut syntax, mut semantic, mut colours) => {
					walker.append_colours(&mut colours);
					walker.append_syntax_diags(&mut syntax);
					walker.append_semantic_diags(&mut semantic);
					Some(e)
				}
				(None, _, _, _) => {
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
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
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
					(Some(e), mut syntax, mut semantic, mut colours) => {
						walker.append_colours(&mut colours);
						walker.append_syntax_diags(&mut syntax);
						walker.append_semantic_diags(&mut semantic);
						Some(e)
					}
					(None, _, _, _) => {
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
	let mut init: Option<Node> = None;
	let mut cond: Option<Node> = None;
	let mut inc: Option<Node> = None;
	let mut counter = 0;
	let r_paren_span = 'outer: loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not encountered a `)` yet.
				let span = Span::new(
					kw_span.start,
					if let Some(ref inc) = inc {
						inc.span.end
					} else if let Some(ref cond) = cond {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedIncStmt(
								cond.span.next_single_width(),
							),
						));
						cond.span.end
					} else if let Some(ref init) = init {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedCondStmt(
								init.span.next_single_width(),
							),
						));
						init.span.end
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
				let init = init.map(|n| ctx.push_node(n));
				let cond = cond.map(|n| ctx.push_node(n));
				let inc = inc.map(|n| ctx.push_node(n));
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
					let init = init.map(|n| ctx.push_node(n));
					let cond = cond.map(|n| ctx.push_node(n));
					let inc = inc.map(|n| ctx.push_node(n));
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

		let qualifiers = try_parse_qualifiers(walker, ctx);
		let mut stmt = Vec::new();
		// FIXME:
		/* try_parse_definition_declaration_expr(
			walker,
			ctx,
			qualifiers,
			counter == 2,
		); */

		if !stmt.is_empty() {
			if counter == 0 {
				init = Some(stmt.remove(0));
			} else if counter == 1 {
				cond = Some(stmt.remove(0));
			} else if counter == 2 {
				inc = Some(stmt.remove(0));
			}
			counter += 1;
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
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedLBraceAfterHeader(
						r_paren_span.next_single_width(),
					),
				));
				let init = init.map(|n| ctx.push_node(n));
				let cond = cond.map(|n| ctx.push_node(n));
				let inc = inc.map(|n| ctx.push_node(n));
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
			let init = init.map(|n| ctx.push_node(n));
			let cond = cond.map(|n| ctx.push_node(n));
			let inc = inc.map(|n| ctx.push_node(n));
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
	let scope_handle = ctx.new_temp_scope(l_brace_span, None);
	parse_scope(walker, ctx, brace_scope, l_brace_span);
	let body = ctx.take_temp_scope(scope_handle);
	let init = init.map(|n| ctx.push_node(n));
	let cond = cond.map(|n| ctx.push_node(n));
	let inc = inc.map(|n| ctx.push_node(n));
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
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
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
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
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
	error: impl FnOnce(Span) -> Syntax,
) {
	walker.push_colour(kw_span, SyntaxType::Keyword);
	walker.advance();

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		walker.push_syntax_diag(error(kw_span.next_single_width()));
	}

	ctx.push_node(Node {
		span: Span::new(
			kw_span.start,
			if let Some(s) = semi_span {
				s.end
			} else {
				kw_span.end
			},
		),
		ty: ty(),
	});
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

	// Look for the optional return value expression.
	let return_expr =
		match parse_expr(walker, ctx, Mode::Default, [Token::Semi]) {
			(Some(expr), mut syntax, mut semantic, mut colours) => {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				Omittable::Some(expr)
			}
			(None, _, _, _) => Omittable::None,
		};

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		if let Omittable::Some(ref return_expr) = return_expr {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ReturnExpectedSemiAfterExpr(
					return_expr.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ReturnExpectedSemiOrExprAfterKw(
					kw_span.next_single_width(),
				),
			));
		}
	}

	ctx.push_node(Node {
		span: Span::new(
			kw_span.start,
			if let Some(s) = semi_span {
				s.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::Return { value: return_expr },
	});
}

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
			walker.push_semantic_diag(Semantic::EmptyDirective(dir_span));
			ctx.push_node(Node {
				span: dir_span,
				ty: NodeTy::EmptyDirective,
			});
		}
		PreprocStream::Custom { kw, content } => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(kw.1, SyntaxType::DirectiveName);
			if let Some(content) = content {
				walker.push_colour(content.1, SyntaxType::Directive);
			}
			walker.push_syntax_diag(Syntax::FoundIllegalPreproc(
				dir_span,
				Some(kw),
			));
		}
		PreprocStream::Invalid { content } => {
			walker
				.push_colour(dir_span.first_char(), SyntaxType::DirectiveHash);
			walker.push_colour(content.1, SyntaxType::Directive);
			walker
				.push_syntax_diag(Syntax::FoundIllegalPreproc(dir_span, None));
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

			if ident_tokens.is_empty() {
				// We have a macro that's missing a name.

				walker.push_syntax_diag(Syntax::PreprocDefine(
					PreprocDefineDiag::DefineExpectedMacroName(
						kw_span.next_single_width(),
					),
				));
				body_tokens.iter().for_each(|(t, s)| {
					walker.push_colour_with_modifiers(
						*s,
						t.non_semantic_colour(),
						SyntaxModifiers::MACRO_BODY,
					)
				});
			} else if ident_tokens.len() == 1 {
				// We have an object-like macro.

				let ident = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::ObjectMacro,
							SyntaxModifiers::MACRO_SIGNATURE,
						);
						(s, span)
					}
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
					ident.0.clone(),
					ident.1,
					Macro::Object(body_tokens.clone()),
				);
				ctx.push_node(Node {
					span: dir_span,
					ty: NodeTy::DefineDirective {
						macro_: ast::Macro::Object {
							ident: Ident {
								span: ident.1,
								name: ident.0,
							},
						},
						replacement_tokens: body_tokens,
					},
				});
			} else {
				// We have a function-like macro.

				let ident = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour_with_modifiers(
							span,
							SyntaxType::FunctionMacro,
							SyntaxModifiers::MACRO_SIGNATURE,
						);
						(s, span)
					}
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
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::ParamsExpectedRParen(
								prev_span.next_single_width(),
							),
						));
						ctx.push_node(Node {
							span: dir_span,
							ty: NodeTy::DefineDirective {
								macro_: ast::Macro::Function {
									ident: Ident {
										span: ident.1,
										name: ident.0,
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
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamAfterComma(Span::new_between(
										prev_span, token_span
									))
								));
							} else if prev == Prev::None {
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamBetweenParenComma(Span::new_between(
										l_paren_span, token_span
									))
								));
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
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedCommaAfterParam(prev_span.next_single_width())
								));
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
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamAfterComma(Span::new_between(
										prev_span, token_span
									))
								));
							}
							break token_span;
						}
						DefineToken::Invalid(_) | _ => {
							walker.push_colour_with_modifiers(
								token_span,
								SyntaxType::Invalid,
								SyntaxModifiers::MACRO_SIGNATURE,
							);
							walker.push_syntax_diag(Syntax::PreprocDefine(
								PreprocDefineDiag::ParamsExpectedParam(
									token_span,
								),
							));
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

				// Syntax highlight the body. If any identifier matches a parameter, we correctly highlight that.
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
					ident.0.clone(),
					Span::new(ident.1.start, r_paren_span.end),
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
								span: ident.1,
								name: ident.0,
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
				walker.push_syntax_diag(Syntax::PreprocDefine(
					PreprocDefineDiag::UndefExpectedMacroName(
						kw_span.next_single_width(),
					),
				));
				Omittable::None
			} else {
				let (token, token_span) = tokens.remove(0);
				let ident = match token {
					UndefToken::Ident(s) => {
						walker.unregister_macro(&s, token_span);
						Omittable::Some(Ident {
							name: s,
							span: token_span,
						})
					}
					UndefToken::Invalid(_) => {
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::UndefExpectedMacroName(
								token_span,
							),
						));
						Omittable::None
					}
				};

				if !tokens.is_empty() {
					let (_, first) = tokens.first().unwrap();
					let (_, last) = tokens.last().unwrap();
					walker.push_colour_with_modifiers(
						Span::new(first.start, last.end),
						SyntaxType::Invalid,
						SyntaxModifiers::UNDEFINE,
					);
					walker.push_syntax_diag(Syntax::PreprocTrailingTokens(
						Span::new(first.start, last.end),
					));
				}

				ident
			};

			ctx.push_node(Node {
				span: Span::new(
					dir_span.start,
					if let Omittable::Some(ref ident) = ident {
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
		walker.push_syntax_diag(Syntax::PreprocVersion(
			PreprocVersionDiag::ExpectedNumber(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (VersionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					VersionToken::Invalid(_) => SyntaxType::Invalid,
					_ => SyntaxType::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
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
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::UnsupportedVersion(span, number),
				));
				Some(number)
			}
			_ => {
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::InvalidVersion(span, number),
				));
				None
			}
		}
	}

	/// Parses the profile.
	fn parse_profile<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		str: &str,
		span: Span,
	) -> Option<ProfileTy> {
		match str {
			"core" => {
				walker.push_colour(span, SyntaxType::DirectiveProfile);
				Some(ProfileTy::Core)
			}
			"compatability" => {
				walker.push_colour(span, SyntaxType::DirectiveProfile);
				Some(ProfileTy::Compatability)
			}
			"es" => {
				walker.push_colour(span, SyntaxType::DirectiveProfile);
				Some(ProfileTy::Es)
			}
			_ => {
				let str = str.to_lowercase();
				match str.as_ref() {
					"core" => {
						walker.push_colour(span, SyntaxType::DirectiveProfile);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span, "core",
							),
						));
						Some(ProfileTy::Core)
					}
					"compatability" => {
						walker.push_colour(span, SyntaxType::DirectiveProfile);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span,
								"compatability",
							),
						));
						Some(ProfileTy::Compatability)
					}
					"es" => {
						walker.push_colour(span, SyntaxType::DirectiveProfile);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span, "es",
							),
						));
						Some(ProfileTy::Es)
					}
					_ => None,
				}
			}
		}
	}

	// Consume the version number.
	let version = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			VersionToken::Num(n) => {
				match parse_version(walker, n, token_span) {
					Some(n) => {
						walker.push_colour(
							token_span,
							SyntaxType::DirectiveVersion,
						);
						(n, token_span)
					}
					None => {
						walker.push_colour(token_span, SyntaxType::Directive);
						seek_end(walker, tokens, false);
						return;
					}
				}
			}
			VersionToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::InvalidNumber(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::ExpectedNumber(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Word(str) => {
				match parse_profile(walker, &str, token_span) {
					Some(profile) => {
						// We have a profile immediately after the `version` keyword.
						walker.push_syntax_diag(Syntax::PreprocVersion(PreprocVersionDiag::MissingNumberBetweenKwAndProfile(
								Span::new_between(kw_span, token_span)
							)));
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
						walker.push_colour(token_span, SyntaxType::Directive);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::ExpectedNumber(token_span),
						));
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
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfile(token_span),
						));
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
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::ExpectedProfile(token_span),
				));
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
		walker.push_syntax_diag(Syntax::PreprocExt(
			PreprocExtDiag::ExpectedName(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (ExtensionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					ExtensionToken::Invalid(_) => SyntaxType::Invalid,
					_ => SyntaxType::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
		}
	}

	/// Parses the behaviour.
	fn parse_behaviour(
		str: &str,
		span: Span,
	) -> Option<(BehaviourTy, Option<Syntax>)> {
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
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "require",
							),
						)),
					)),
					"enable" => Some((
						BehaviourTy::Enable,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "enable",
							),
						)),
					)),
					"warn" => Some((
						BehaviourTy::Warn,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "warn",
							),
						)),
					)),
					"disable" => Some((
						BehaviourTy::Disable,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "disable",
							),
						)),
					)),
					_ => None,
				}
			}
		}
	}

	// Consume the extension name.
	let name = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour(
							token_span,
							SyntaxType::DirectiveExtBehaviour,
						);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::MissingNameBetweenKwAndBehaviour(
								Span::new_between(kw_span, token_span),
							),
						));
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
						walker.push_colour(
							token_span,
							SyntaxType::DirectiveExtName,
						);
						(str, token_span)
					}
				}
			}
			ExtensionToken::Colon => {
				walker.push_colour(token_span, SyntaxType::Directive);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::MissingNameBetweenKwAndColon(
						Span::new_between(kw_span, token_span),
					),
				));
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
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedName(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
		}
	};

	// Consume the colon.
	let colon_span = match tokens.next() {
		Some((token, token_span)) => match token {
			ExtensionToken::Colon => {
				walker.push_colour(token_span, SyntaxType::Directive);
				token_span
			}
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour(
							token_span,
							SyntaxType::DirectiveExtBehaviour,
						);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::MissingColonBetweenNameAndBehaviour(
								Span::new_between(name.1, token_span),
							),
						));
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
						walker.push_colour(token_span, SyntaxType::Directive);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::ExpectedColon(token_span),
						));
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
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedColon(token_span),
				));
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
			walker.push_syntax_diag(Syntax::PreprocExt(
				PreprocExtDiag::ExpectedColon(name.1.next_single_width()),
			));
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
						walker.push_colour(
							token_span,
							SyntaxType::DirectiveExtBehaviour,
						);
						if let Some(diag) = diag {
							walker.push_syntax_diag(diag);
						}
						(behaviour, token_span)
					}
					None => {
						walker.push_colour(token_span, SyntaxType::Directive);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviour(token_span),
						));
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
				walker.push_colour(token_span, SyntaxType::Directive);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedBehaviour(token_span),
				));
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
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedBehaviour(token_span),
				));
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
			walker.push_syntax_diag(Syntax::PreprocExt(
				PreprocExtDiag::ExpectedBehaviour(name.1.next_single_width()),
			));
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
		walker.push_syntax_diag(Syntax::PreprocLine(
			PreprocLineDiag::ExpectedNumber(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end<'a, P: TokenStreamProvider<'a>>(
		walker: &mut Walker<'a, P>,
		mut tokens: impl Iterator<Item = (LineToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					LineToken::Invalid(_) => SyntaxType::Invalid,
					_ => SyntaxType::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
		}
	}

	let line = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			LineToken::Num(n) => {
				walker.push_colour(token_span, SyntaxType::DirectiveLineNumber);
				Some((n, token_span))
			}
			LineToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::InvalidNumber(token_span),
				));
				None
			}
			LineToken::Ident(_str) => {
				let _ident_span = token_span;

				let line = None;
				let src_str_num = Omittable::None;
				if src_str_num.is_some() {
					seek_end(walker, tokens, true);
					ctx.push_node(Node {
						span: Span::new(dir_span.start, kw_span.end),
						ty: NodeTy::LineDirective { line, src_str_num },
					});
					return;
				} else {
					line
				}
			}
			LineToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::ExpectedNumber(token_span),
				));
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
				walker.push_colour(token_span, SyntaxType::DirectiveLineNumber);
				Omittable::Some((n, token_span))
			}
			LineToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::InvalidNumber(token_span),
				));
				Omittable::None
			}
			LineToken::Ident(_str) => Omittable::None,
			LineToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxType::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::ExpectedNumber(token_span),
				));
				seek_end(walker, tokens, false);
				ctx.push_node(Node {
					span: Span::new(
						dir_span.start,
						if let Some(line) = line {
							line.1.end
						} else {
							kw_span.end
						},
					),
					ty: NodeTy::LineDirective {
						line,
						src_str_num: Omittable::None,
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
			if let Omittable::Some(src_str_num) = src_str_num {
				src_str_num.1.end
			} else if let Some(line) = line {
				line.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::LineDirective { line, src_str_num },
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
	if let Some(ref message) = message {
		walker.push_colour(message.1, SyntaxType::DirectiveError);
	}
	ctx.push_node(Node {
		span: Span::new(
			dir_span.start,
			if let Some(ref message) = message {
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
	if let Some(ref options) = options {
		walker.push_colour(options.1, SyntaxType::DirectivePragma);
	}
	ctx.push_node(Node {
		span: Span::new(
			dir_span.start,
			if let Some(ref options) = options {
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
	// specifier.
	let e =
		match try_parse_subroutine_type_specifier(walker, ctx, [Token::Semi]) {
			Ok((mut type_, mut syntax, mut semantic, mut colours)) => {
				// This must be a subroutine type declaration, an associated function definition, or a subroutine
				// uniform definition.
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);

				let (token, token_span) = match walker.peek() {
					Some(t) => t,
					None => {
						// We are lacking an identifier after the type.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubExpectedTypeFnOrUniformAfterQualifiers(
								Span::new_single_width(qualifiers_end_pos),
							),
						));
						return;
					}
				};

				// Check whether we have a subroutine type declaration or an associated function definition.
				match token {
					Token::Ident(i) => match walker.lookahead_1() {
						Some(next) => match next.0 {
							Token::LParen => {
								// We have a function declaration/definition.
								match &mut type_ {
									Either::Left(type_) => {
										type_.qualifiers = qualifiers
									}
									Either::Right(type_) => {
										type_.qualifiers = qualifiers
									}
								}
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
				) {
					Ok((i, mut syntax, mut semantic, mut colours)) => {
						walker.append_colours(&mut colours);
						walker.append_syntax_diags(&mut syntax);
						walker.append_semantic_diags(&mut semantic);
						i
					}
					Err((expr, mut syntax, mut semantic, mut colours)) => {
						walker.append_colours(&mut colours);
						walker.append_syntax_diags(&mut syntax);
						walker.append_semantic_diags(&mut semantic);

						if let Some(expr) = expr {
							// We have a (subroutine/normal) type specifier, followed by a second expression but
							// the second expression isn't one or more new variable specifiers. We treat the first
							// expression as an incomplete subroutine uniform grammar and the second expression as
							// a standalone expression.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::TypeExpectedIdentsAfterType(
									match type_ {
										Either::Left(t) => {
											t.span.next_single_width()
										}
										Either::Right(t) => {
											t.span.next_single_width()
										}
									},
								),
							));
							ctx.push_node(Node {
								span: expr.span,
								ty: NodeTy::Expr(expr),
							});
							seek_next_stmt(walker);
						} else {
							// We have a (subroutine/normal) type specifier followed by something that can't be
							// parsed at all as an expression.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::TypeExpectedIdentsAfterType(
									match type_ {
										Either::Left(t) => {
											t.span.next_single_width()
										}
										Either::Right(t) => {
											t.span.next_single_width()
										}
									},
								),
							));
						}
						return;
					}
				};

				// Panic: `var_specifiers` has a length of at least 1.
				let last_var_spec_span = var_specifiers.last().unwrap().span;

				// We definitely have something which matches a variable(s) definition, irrespective of what comes
				// next. That means the only node that makes sense to produce is a subroutine uniform definition
				// node. For that to be valid, we need a) lack of an association list, b) the `uniform` keyword
				// after the subroutine keyword, c) a subroutine type specifier rather than a normal type
				// specifier. If (a) is present, we can just ignore it. If (b) is missing, we can just assume it's
				// present. If (c) is not met, we can't create the node since the ast node explicitly takes only a
				// subroutine type.

				// Check (a)
				if let Some((_, l_paren, r_paren)) = association_list {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubUniformFoundAssociationList(Span::new(
							l_paren.start,
							r_paren.end,
						)),
					));
				}

				// Check (b)
				if let Some(span) = uniform_kw_span {
					if is_uniform_before_subroutine {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubUniformFoundUniformKwBeforeSubKw(span),
						));
					}
				} else {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubUniformExpectedUniformKw(
							Span::new_single_width(qualifiers_end_pos),
						),
					));
				}

				// Consume the `;` to end the statement.
				let semi_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Semi {
							Some(token_span)
						} else {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SubUniformExpectedSemiAfterVars(
									last_var_spec_span.next_single_width(),
								),
							));
							None
						}
					}
					None => {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubUniformExpectedSemiAfterVars(
								last_var_spec_span.next_single_width(),
							),
						));
						None
					}
				};

				// Check (c)
				let type_ = match type_ {
					Either::Left(type_) => type_,
					Either::Right(type_) => {
						// Since the subroutine uniform node takes a subroutine type handle, there is really
						// nothing else we can do other than abort creating anything.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubUniformExpectedSubroutineType(
								type_.span,
							),
						));
						return;
					}
				};

				ctx.push_new_subroutine_uniforms(
					walker,
					type_,
					var_specifiers,
					if let Some(semi_span) = semi_span {
						semi_span.end
					} else {
						last_var_spec_span.end
					},
				);
				return;
			}
			Err(e) => e,
		};

	let (Some(expr), mut syntax, mut semantic, mut colours) = e else {
		// We couldn't parse a (subroutine/normal) type specifier nor even an expression, so this cannot be a
		// valid statement.
		invalidate_qualifiers(walker, qualifiers);
		seek_next_stmt(walker);
		return;
	};

	// We have an expression, it must therefore be a standalone expression statement or an interface block.

	match (&expr.ty, walker.peek()) {
		(ExprTy::Local { name: ident, .. }, Some((token, token_span))) => {
			match token {
				Token::LBrace => {
					// We have an interface block. Because of the presence of the `subroutine` keyword this isn't
					// valid, but we allow it anyway for better error recovery.
					let l_brace_span = token_span;
					syntax.retain(|e| {
						if let Syntax::Expr(
							ExprDiag::FoundOperandAfterOperand(_, _),
						) = e
						{
							false
						} else {
							true
						}
					});
					// TODO: Syntax error
					walker.append_syntax_diags(&mut syntax);
					walker.append_semantic_diags(&mut semantic);
					walker.push_colour(ident.span, SyntaxType::Variable);
					walker.push_colour(l_brace_span, SyntaxType::Punctuation);
					walker.advance();
					parse_interface_block(
						walker,
						ctx,
						qualifiers,
						start_pos,
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

	// We have a standalone expression statement. This is incompatible with the `subroutine` keyword. We treat the
	// qualifiers (inc. subroutine keyword) as a half-finished subroutine statement of some kind and ignore it,
	// whilst treating the expression as a standalone expression statement.
	walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SubExpectedAfterKw(
		Span::new_single_width(qualifiers_end_pos),
	)));
	walker.append_colours(&mut colours);
	walker.append_syntax_diags(&mut syntax);
	walker.append_semantic_diags(&mut semantic);

	// Consume the `;` to end the statement.
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
	if semi_span.is_none() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::ExprStmtExpectedSemiAfterExpr(
				expr.span.next_single_width(),
			),
		));
		seek_next_stmt(walker);
	}

	ctx.push_node(Node {
		span: if let Some(semi_span) = semi_span {
			Span::new(expr.span.start, semi_span.end)
		} else {
			expr.span
		},
		ty: NodeTy::Expr(expr),
	});
}

/// Parses a function declaration/definition.
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
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubTypeDeclFoundAssociationList(Span::new(
					l_paren.start,
					r_paren.end,
				)),
			));
		}
		if let Some(span) = uniform_kw_span {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubTypeDeclFoundUniformKw(span),
			));
		}
		let return_type = match return_type {
			Either::Left(type_) => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SubTypeDeclExpectedNormalType(type_.span),
				));
				return;
			}
			Either::Right(type_) => type_,
		};

		ctx.push_new_subroutine_type(return_type, ident, params, end_pos);
	}

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
	let param_end_span = loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not yet finished parsing the parameter list, but we treat this as a valid declaration
				// since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));

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
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				} else if prev == Prev::None {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamBetweenParenComma(
							Span::new_between(l_paren_span, token_span),
						),
					));
				}
				prev = Prev::Comma;
				prev_span = token_span;
				continue;
			}
			Token::RParen => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				}
				break token_span;
			}
			Token::Semi => {
				walker.push_colour(token_span, SyntaxType::Punctuation);
				walker.advance();
				// We have not yet finished parsing the parameter list but we've encountered a semi-colon. We treat
				// this as a valid declaration since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));

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
				// We don't advance because the next check after this loop checks for a l-brace.

				// We have not yet finished parsing the parameter list but we've encountered a l-brace. We treat
				// this as a potentially valid definition since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				break token_span;
			}
			_ => {}
		}

		if prev == Prev::Param {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ParamsExpectedCommaAfterParam(
					prev_span.next_single_width(),
				),
			));
		}
		let param_span_start = token_span.start;

		let qualifiers = try_parse_qualifiers(walker, ctx);

		// Consume the type specifier.
		let mut type_ = match try_parse_type_specifier(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
		) {
			Ok((type_, mut syntax, mut semantic, mut colours)) => {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				type_
			}
			Err((expr, mut syntax, mut semantic, mut colours)) => {
				if let Some(expr) = expr {
					// We have an expression which cannot be parsed into a type. We ignore this and continue
					// searching for the next parameter.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidTypeExpr(expr.span),
					));
					prev = Prev::Invalid;
					prev_span = Span::new(param_span_start, expr.span.end);
					continue;
				} else {
					// We immediately have a token that is not an expression. We ignore this and loop until we hit
					// something recognizable.
					let end_span = loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::Comma
									|| *token == Token::RParen || *token
									== Token::Semi || *token == Token::LBrace
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
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidTypeExpr(Span::new(
							param_span_start,
							end_span.end,
						)),
					));
					prev = Prev::Invalid;
					prev_span = token_span;
					continue;
				}
			}
		};

		// Look for the optional ident.
		/* let ident = match try_parse_new_decl_def_idents_with_type_info(
			walker,
			ctx,
			[Token::Semi, Token::LBrace],
			true,
			SyntaxType::Parameter,
		) {
			Ok((i, mut syntax, mut semantic, mut colours)) => {
				walker.append_colours(&mut colours);
				walker.append_syntax_diags(&mut syntax);
				walker.append_semantic_diags(&mut semantic);
				i
			}
			Err((expr, mut syntax, mut semantic, mut colours)) => {
				if let Some(expr) = expr {
					// We have a second expression after the first expression, but the second expression can't be
					// converted to an identifier for the parameter. We treat the first type expression as an
					// anonymous parameter, and the second expression as invalid.
					let param_span =
						Span::new(param_span_start, type_.span.end);
					type_.qualifiers = qualifiers;
					params.push(Param {
						span: Span::new(param_span_start, type_.span.end),
						type_,
						ident: Omittable::None,
					});
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidIdentExpr(expr.span),
					));
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				} else {
					// We have a first expression and then something that is not an expression. We treat this as an
					// anonymous parameter, whatever the current token is will be dealt with in the next iteration.
					type_.qualifiers = qualifiers;
					let param_span =
						Span::new(param_span_start, type_.span.end);
					params.push(Param {
						span: param_span,
						type_,
						ident: Omittable::None,
					});
					prev = Prev::Param;
					prev_span = param_span;
					continue;
				}
			}
		}; */
		// FIXME:
		let ident: Vec<(Ident, Vec<Omittable<Expr>>, Span)> = vec![];
		let ident_span = ident[0].0.span;

		type_.qualifiers = qualifiers;
		let (type_, ident) = combine_type_with_idents(type_, ident).remove(0);
		let param_span = Span::new(param_span_start, ident_span.end);
		params.push(Param {
			span: param_span,
			type_,
			ident: Omittable::Some(ident),
		});
		prev = Prev::Param;
		prev_span = param_span;
	};

	// Consume the `;` for a declaration or a `{` for a definition.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => match token {
			Token::Semi => Some(token_span),
			Token::LBrace => {
				// We have a subroutine associated-function definition.
				let l_brace_span = token_span;
				walker.push_colour(l_brace_span, SyntaxType::Punctuation);
				walker.advance();

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
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubFnDefExpectedAssociationList(
								subroutine_kw_span.next_single_width(),
							),
						));
						Vec::new()
					};
				if let Some(span) = uniform_kw_span {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubFnDefFoundUniformKw(span),
					));
				}
				let return_type = match return_type {
					Either::Left(type_) => {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubFnDefExpectedNormalType(type_.span),
						));
						return;
					}
					Either::Right(type_) => type_,
				};

				ctx.push_new_associated_subroutine_fn_def(
					scope_handle,
					association_list,
					ident.clone(),
					params.iter().cloned().map(|p| p.into()).collect(),
					return_type.clone(),
					Node {
						span: Span::new(return_type.span.start, body.span.end),
						ty: NodeTy::FnDef {
							return_type,
							ident,
							params,
							body,
						},
					},
				);
				return;
			}
			_ => None,
		},
		None => None,
	};

	// We have a subroutine type declaration.

	match semi_span {
		Some(semi_span) => {
			walker.push_colour(semi_span, SyntaxType::Punctuation);
			walker.advance();
		}
		None => {
			// We are missing a `;` to make this grammatically valid. We treat this as a declaration though since
			// it's the closest unambiguous match.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::FnExpectedSemiOrLBraceAfterParams(
					param_end_span.next_single_width(),
				),
			));
		}
	}

	push_type_decl(
		walker,
		ctx,
		return_type,
		ident,
		association_list,
		uniform_kw_span,
		params,
		semi_span.map(|s| s.end).unwrap_or(param_end_span.end),
	);

	if semi_span.is_none() {
		seek_next_stmt(walker);
	}
}

/// Combines the ident information with the type to create one or more type-ident pairs. This step is necessary
/// because the idents themselves can contain type information, e.g. `int[3] i[9]`.
fn combine_type_with_idents(
	type_: Type,
	ident_info: Vec<(Ident, Vec<ArrSize>, Span)>,
) -> Vec<(Type, Ident)> {
	let mut vars = Vec::new();
	for (ident, sizes, _) in ident_info {
		if sizes.is_empty() {
			vars.push((type_.clone(), ident));
		} else {
			let mut sizes = sizes.clone();
			let Type {
				ty,
				qualifiers,
				span,
			} = type_.clone();
			let primitive = match ty {
				TypeTy::Single(p) => p,
				TypeTy::Array(p, i) => {
					sizes.push(i);
					p
				}
				TypeTy::Array2D(p, i, j) => {
					sizes.push(i);
					sizes.push(j);
					p
				}
				TypeTy::ArrayND(p, mut v) => {
					sizes.append(&mut v);
					p
				}
			};

			let type_ = if sizes.len() == 0 {
				Type {
					span,
					ty: TypeTy::Single(primitive),
					qualifiers,
				}
			} else if sizes.len() == 1 {
				Type {
					span,
					ty: TypeTy::Array(primitive, sizes.remove(0)),
					qualifiers,
				}
			} else if sizes.len() == 2 {
				Type {
					span,
					ty: TypeTy::Array2D(
						primitive,
						sizes.remove(0),
						sizes.remove(0),
					),
					qualifiers,
				}
			} else {
				Type {
					span,
					ty: TypeTy::ArrayND(primitive, sizes),
					qualifiers,
				}
			};

			vars.push((type_, ident))
		}
	}
	vars
}

/// Combines the ident information with the subroutine type to create one or more subroutine type-ident pairs. This
/// step is necessary because the idents themselves can contain type information, e.g. `foo[3] i[9]`.
pub(super) fn combine_subroutine_type_with_idents(
	type_: SubroutineType,
	arr: Option<Vec<ArrSize>>,
) -> SubroutineType {
	let Some(arr) = arr else { return type_; };

	let mut sizes = arr.clone();
	let SubroutineType {
		ty,
		qualifiers,
		span,
	} = type_.clone();
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

	let type_ = if sizes.len() == 0 {
		SubroutineType {
			span,
			ty: SubroutineTypeTy::Single(handle),
			qualifiers,
		}
	} else if sizes.len() == 1 {
		SubroutineType {
			span,
			ty: SubroutineTypeTy::Array(handle, sizes.remove(0)),
			qualifiers,
		}
	} else if sizes.len() == 2 {
		SubroutineType {
			span,
			ty: SubroutineTypeTy::Array2D(
				handle,
				sizes.remove(0),
				sizes.remove(0),
			),
			qualifiers,
		}
	} else {
		SubroutineType {
			span,
			ty: SubroutineTypeTy::ArrayND(handle, sizes),
			qualifiers,
		}
	};

	type_
}
