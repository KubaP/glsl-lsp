pub mod ast;
mod syntax;

pub use syntax::*;

use crate::{
	cst::{Comment, Comments},
	error::{Diag, PreprocDefineDiag},
	token::{preprocessor::TokenStream as PreprocStream, Token, TokenStream},
	Span, Spanned,
};
use ast::*;
use std::collections::{HashMap, HashSet};

pub fn parse_from_str(
	source: &str,
) -> (Vec<ast::Node>, Vec<Diag>, Vec<Spanned<SyntaxToken>>) {
	let token_stream = crate::token::parse_from_str(source);
	let mut walker = Walker::new(token_stream);
	let mut nodes = Vec::new();
	while !walker.is_done() {
		parse_stmt(&mut walker, &mut nodes);
	}
	(nodes, walker.diagnostics, walker.syntax_tokens)
}

pub(crate) struct Walker {
	/// The active token streams.
	///
	/// - `(identifier, token_stream, cursor)`.
	streams: Vec<(String, TokenStream, usize)>,

	/// The currently defined macros.
	///
	/// Key: The macro identifier
	///
	/// Value:
	/// - `0` - The span of the identifier,
	/// - `1` - The body/replacement-list of tokens.
	macros: HashMap<String, (Span, TokenStream)>,
	/// The span of an initial macro call site. Only the first macro call site is registered.
	macro_call_site: Option<Span>,
	/// The actively called macros.
	active_macros: HashSet<String>,

	/// The diagnostics created from the tokens parsed so-far.
	diagnostics: Vec<Diag>,

	/// The syntax highlighting tokens created from the tokens parsed so-far.
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(token_stream: TokenStream) -> Self {
		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

		Self {
			streams: vec![("".into(), token_stream, 0)],
			macros: HashMap::new(),
			macro_call_site: None,
			active_macros,
			diagnostics: Vec::new(),
			syntax_tokens: Vec::new(),
		}
	}

	/// Returns a reference to the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<Spanned<&Token>> {
		if self.streams.is_empty() {
			None
		} else if self.streams.len() == 1 {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream.get(*cursor).map(|(t, s)| (t, *s))
		} else {
			let (_, stream, cursor) = self.streams.last().unwrap();
			match stream.get(*cursor).map(|(t, _)| t) {
				Some(token) => Some((
					token,
					// Panic: This is guaranteed to be some if `self.streams.len() > 1`.
					self.macro_call_site.unwrap(),
				)),
				None => None,
			}
		}
	}

	/// Returns the current token under the cursor, without advancing the cursor. (The token gets cloned).
	fn get(&self) -> Option<Spanned<Token>> {
		if self.streams.is_empty() {
			None
		} else if self.streams.len() == 1 {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream.get(*cursor).cloned()
		} else {
			let (_, stream, cursor) = self.streams.last().unwrap();
			let token = stream.get(*cursor).map(|(t, _)| t).cloned();
			token.map(|t| {
				(
					t,
					// Panic: This is guaranteed to be some if `self.streams.len() > 1`.
					self.macro_call_site.unwrap(),
				)
			})
		}
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	/* fn lookahead_1(&self) -> Option<&Spanned<Token>> {
		let token = self.token_stream.get(self.cursor + 1);
		if let Some((token, _)) = token {
			match token {
				Token::Ident(s) => {
					if let Some((_, replacement_stream)) = self.macros.get(s) {
						if let Some(first_replacement_token) =
							replacement_stream.get(0)
						{
							return Some(first_replacement_token);
						}
						// FIXME: Deal with empty replacement stream.
					}
				}
				_ => {}
			}
		}

		token
	} */

	/// Peeks the next token without advancing the cursor whilst ignoring any comments.
	/* fn lookahead_1_ignore_comments(&self) -> Option<&Spanned<Token>> {
		// FIXME: replacement
		let mut cursor = self.cursor + 1;
		while let Some(i) = self.token_stream.get(cursor) {
			match i.0 {
				Token::LineComment(_)
				| Token::BlockComment {
					str: _,
					contains_eof: _,
				} => {
					cursor += 1;
					continue;
				}
				_ => return Some(i),
			}
		}
		None
	} */

	/// Advances the cursor by one.
	fn advance(&mut self) {
		let mut dont_increment = false;
		'outer: while let Some((identifier, stream, cursor)) =
			self.streams.last_mut()
		{
			if !dont_increment {
				*cursor += 1;
			}
			dont_increment = false;

			if *cursor == stream.len() {
				// We have reached the end of this stream. We close it and re-run the loop on the next stream (if
				// there is one).

				// Panic: Anytime a stream is added the identifier is inserted into the set.
				self.active_macros.remove(identifier);
				// Panic: We checked the length.
				self.streams.remove(self.streams.len() - 1);
				continue;
			}

			// Panic: We check the length.
			let (token, token_span) = stream.get(*cursor).unwrap();

			// We now check if the new token is a macro call site.
			match token {
				Token::Ident(s) => {
					if let Some((_, new_stream)) = self.macros.get(s) {
						if self.active_macros.contains(s) {
							// We have already visited a macro with this identifier. Recursion is not supported so
							// we don't continue.
							break;
						}

						let token_span = *token_span;

						if new_stream.is_empty() {
							// The macro is empty, so we want to move to the next token of the existing stream.
							self.push_diag(Diag::EmptyMacroCallSite(
								token_span,
							));
							if self.streams.len() == 1 {
								self.syntax_tokens.push((
									SyntaxToken::ObjectMacro,
									token_span,
								));
							}
							continue;
						}

						let ident = s.to_owned();

						// We only syntax highlight and note the macro call site when it is the first macro call.
						if self.streams.len() == 1 {
							self.macro_call_site = Some(token_span);
							self.syntax_tokens
								.push((SyntaxToken::ObjectMacro, token_span));
						}

						self.active_macros.insert(ident.clone());
						self.streams.push((ident, new_stream.clone(), 0));

						// The first token in the new stream could be another macro call, so we re-run the loop on
						// this new stream in case.
						dont_increment = true;
						continue;
					}
					break;
				}
				_ => break,
			}
		}

		if self.streams.len() <= 1 {
			self.macro_call_site = None;
		}
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	/* fn next(&mut self) -> Option<Spanned<Token>> {
		// FIXME: replacement
		// If we are successful in getting the token, advance the cursor.
		match self.token_stream.get(self.cursor) {
			Some(i) => {
				self.cursor += 1;
				Some(i.clone())
			}
			None => None,
		}
	} */

	/// Returns any potential comment tokens until the next non-comment token.
	fn consume_comments(&mut self) -> Comments {
		// FIXME: replacement
		let mut comments = Vec::new();
		while let Some((token, span)) = self.get() {
			match token {
				Token::LineComment(str) => {
					comments.push((Comment::Line(str.clone()), span));
				}
				Token::BlockComment { str, .. } => {
					comments.push((Comment::Block(str.clone()), span));
				}
				_ => break,
			}
			self.advance();
		}
		comments
	}

	/// Registers a define macro. Note: currently only supports object-like macros.
	fn register_macro(&mut self, ident: Spanned<String>, tokens: TokenStream) {
		if let Some(_prev) = self.macros.insert(ident.0, (ident.1, tokens)) {
			// TODO: Emit error if the macros aren't identical (will require scanning the tokenstream to compare).
		}
	}

	/// Un-registers a defined macro. Note: currently only supports object-like macros.
	fn unregister_macro(&mut self, ident: String, span: Span) {
		match self.macros.remove(&ident) {
			Some(_) => self.colour(span, SyntaxToken::ObjectMacro),
			None => {
				self.push_diag(Diag::PreprocDefine(
					PreprocDefineDiag::UndefMacroNameUnresolved(span),
				));
				self.colour(span, SyntaxToken::Unresolved);
			}
		}
	}

	/// Pushes a diagnostic.
	pub(crate) fn push_diag(&mut self, diag: Diag) {
		self.diagnostics.push(diag);
	}

	fn colour(&mut self, span: Span, token: SyntaxToken) {
		// When we are within a macro, we don't want to produce syntax tokens.
		if self.streams.len() == 1 {
			self.syntax_tokens.push((token, span));
		}
	}

	/// Returns whether the `Lexer` has reached the end of the token list.
	fn is_done(&self) -> bool {
		self.streams.is_empty()
	}

	/* /// Returns the [`Span`] of the current `Token`.
	///
	/// *Note:* If we have reached the end of the tokens, this will return the value of
	/// [`get_last_span()`](Self::get_last_span).
	fn get_current_span(&self) -> Span {
		// FIXME: replacement
		match self.token_stream.get(self.cursor) {
			Some(t) => t.1,
			None => self.get_last_span(),
		}
	} */

	/* /// Returns the [`Span`] of the previous `Token`.
	///
	/// *Note:* If the current token is the first, the span returned will be `0-0`.
	fn get_previous_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.get(self.cursor - 1)
			.map_or(Span::new_zero_width(0), |t| t.1)
	} */

	/* /// Returns the [`Span`] of the last `Token`.
	///
	/// *Note:* If there are no tokens, the span returned will be `0-0`.
	fn get_last_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.last()
			.map_or(Span::new_zero_width(0), |t| t.1)
	} */
}

/// Parses an individual statement at the current position.
fn parse_stmt(walker: &mut Walker, nodes: &mut Vec<ast::Node>) {
	use crate::token::preprocessor::{self, DefineToken, UndefToken};

	let (token, token_span) = walker.get().expect("This function should be called from a loop that checks this invariant!");

	match token {
		Token::Semi => {
			walker.colour(token_span, SyntaxToken::Punctuation);
			walker.advance();
			nodes.push(Node {
				span: token_span,
				ty: NodeTy::Empty,
			});
		}
		Token::Directive(dir) => match dir {
			preprocessor::TokenStream::Define {
				kw: kw_span,
				mut ident_tokens,
				body_tokens,
			} => {
				walker.colour(token_span.first_char(), SyntaxToken::Directive);
				walker.colour(kw_span, SyntaxToken::Directive);

				if ident_tokens.is_empty() {
					// We have a macro that's missing a name.

					walker.push_diag(Diag::PreprocDefine(
						PreprocDefineDiag::DefineExpectedMacroName(
							kw_span.next_single_width(),
						),
					));
					body_tokens.iter().for_each(|(_, s)| {
						walker.colour(*s, SyntaxToken::Invalid)
					});
				} else if ident_tokens.len() == 1 {
					// We have an object-like macro.

					let ident = match ident_tokens.remove(0) {
						(DefineToken::Ident(s), span) => (s, span),
						_ => unreachable!(),
					};
					walker.colour(ident.1, SyntaxToken::ObjectMacro);

					// Since object-like macros don't have parameters, we can perform the concatenation once right
					// here since we know the contents of the macro body will never change.
					let body_tokens = preprocessor::concat_object_macro_body(
						walker,
						body_tokens,
					);
					body_tokens.iter().for_each(|(t, s)| {
						walker.colour(*s, t.non_semantic_colour())
					});
					walker.register_macro(ident, body_tokens);
				} else {
					// We have a function-like macro.
					// TODO: Implement
				}

				walker.advance();
			}
			preprocessor::TokenStream::Undef {
				kw: kw_span,
				mut tokens,
			} => {
				walker.colour(token_span.first_char(), SyntaxToken::Directive);
				walker.colour(kw_span, SyntaxToken::Directive);

				if tokens.is_empty() {
					walker.push_diag(Diag::PreprocDefine(
						PreprocDefineDiag::UndefExpectedMacroName(
							kw_span.next_single_width(),
						),
					));
				} else {
					let (token, token_span) = tokens.remove(0);

					match token {
						UndefToken::Ident(s) => {
							walker.unregister_macro(s, token_span)
						}
						_ => {
							walker.push_diag(Diag::PreprocDefine(
								PreprocDefineDiag::UndefExpectedMacroName(
									token_span,
								),
							));
						}
					}

					if !tokens.is_empty() {
						let (_, first) = tokens.first().unwrap();
						let (_, last) = tokens.last().unwrap();
						walker.push_diag(Diag::PreprocTrailingTokens(
							Span::new(first.start, last.end),
						));
					}
				}

				walker.advance();
			}
			_ => {
				walker.advance();
			}
		},
		Token::Break => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Break,
			|span| Diag::ExpectedSemiAfterBreakKw(span),
		),
		Token::Continue => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Continue,
			|span| Diag::ExpectedSemiAfterContinueKw(span),
		),
		Token::Discard => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Discard,
			|span| Diag::ExpectedSemiAfterDiscardKw(span),
		),
		_ => {
			walker.advance();
		}
	}
}

/// Parses a break/continue/discard statement.
///
/// This assumes that the keyword has already been parsed.
fn parse_break_continue_discard(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	kw_span: Span,
	ty: impl FnOnce() -> NodeTy,
	error: impl FnOnce(Span) -> Diag,
) {
	walker.colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::Semi {
				walker.colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				Some(token_span)
			} else {
				None
			}
		}
		None => None,
	};

	if semi_span.is_none() {
		walker.push_diag(error(kw_span.next_single_width()));
	}

	nodes.push(Node {
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
