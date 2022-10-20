pub mod ast;
mod syntax;

pub use syntax::*;

use crate::{
	cst::{Comment, Comments},
	error::Diag,
	span::{Span, Spanned},
	token::{Token, TokenStream},
};
use ast::*;
use std::collections::HashMap;

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

struct Walker {
	/// The token stream.
	token_stream: TokenStream,
	/// The current position within the token stream.
	cursor: usize,
	/// The currently defined macros.
	///
	/// Key: The macro identifier
	///
	/// Value:
	/// - `0` - The span of the identifier,
	/// - `1` - The body/replacement-list of tokens.
	macros: HashMap<String, (Span, TokenStream)>,
	/// A replacement [`TokenStream`] from a `#define` macro body.
	///
	/// - `0` - The replacement stream,
	/// - `1` - The span of the macro identifier instance.
	///
	/// PERF: Optimize this to store a reference. This may require some wrapper structs or pinning because this
	/// would be a self-reference into the `macros` field. In reality there shouldn't be a problem because whilst
	/// we are using this replacement stream the `macros` field will never be modified, but we can't easily express
	/// that through the type system.
	temp_replacement_stream: Option<(TokenStream, Span)>,
	/// The current position within the replacement token stream.
	temp_cursor: usize,

	/// The diagnostics created from the tokens parsed so-far.
	diagnostics: Vec<Diag>,

	/// The syntax highlighting tokens created from the tokens parsed so-far.
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(token_stream: TokenStream) -> Self {
		Self {
			token_stream,
			cursor: 0,
			macros: HashMap::new(),
			temp_replacement_stream: None,
			temp_cursor: 0,
			diagnostics: Vec::new(),
			syntax_tokens: Vec::new(),
		}
	}

	/// Returns a reference to the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<(&Token, &Span)> {
		if let Some((ref replacement_stream, ref instance_span)) =
			self.temp_replacement_stream
		{
			replacement_stream
				.get(self.temp_cursor)
				.map(|(token, _)| (token, instance_span))
		} else {
			self.token_stream.get(self.cursor).map(|(t, s)| (t, s))
		}
	}

	/// Returns the current token under the cursor, without advancing the cursor. (The token gets cloned).
	fn get(&self) -> Option<Spanned<Token>> {
		if let Some((ref replacement_stream, instance_span)) =
			self.temp_replacement_stream
		{
			replacement_stream
				.get(self.temp_cursor)
				.cloned()
				.map(|(token, _)| (token, instance_span))
		} else {
			self.token_stream.get(self.cursor).cloned()
		}
	}

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	fn lookahead_1(&self) -> Option<&Spanned<Token>> {
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
	}

	/// Peeks the next token without advancing the cursor whilst ignoring any comments.
	fn lookahead_1_ignore_comments(&self) -> Option<&Spanned<Token>> {
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
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		if let Some((ref replacement_stream, _)) = self.temp_replacement_stream
		{
			// If we are in a replacement stream we want to move the temporary cursor instead.
			self.temp_cursor += 1;

			if self.temp_cursor == replacement_stream.len() {
				// We have reached the end of the replacement stream. We can now switch back to the normal stream.
				self.temp_replacement_stream = None;
				self.temp_cursor = 0;
				self.cursor += 1;
			} else {
				// Since we are still within the replacement stream, we don't want to check for a macro match
				// because that would result in an infinite loop.
				return;
			}
		} else {
			self.cursor += 1;
		}

		// Check if we are now at an identifier which matches a macro identifier.
		if let Some((token, token_span)) = self.token_stream.get(self.cursor) {
			match token {
				Token::Ident(s) => {
					if let Some((_, replacement_stream)) = self.macros.get(s) {
						// The identifier matches an already-defined macro.
						self.temp_replacement_stream =
							Some((replacement_stream.clone(), *token_span));
						self.temp_cursor = 0;
						self.syntax_tokens
							.push((SyntaxToken::ObjectMacro, *token_span));
					}
				}
				_ => {}
			}
		}
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	fn next(&mut self) -> Option<Spanned<Token>> {
		// FIXME: replacement
		// If we are successful in getting the token, advance the cursor.
		match self.token_stream.get(self.cursor) {
			Some(i) => {
				self.cursor += 1;
				Some(i.clone())
			}
			None => None,
		}
	}

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

	/// Registers a `#define` macro. Note: currently only supports object-like macros.
	fn register_macro(&mut self, ident: Spanned<String>, tokens: TokenStream) {
		if let Some(_prev) = self.macros.insert(ident.0, (ident.1, tokens)) {
			// MAYBE: Emit warning about overwriting a macro?
		}
	}

	fn push_diag(&mut self, diag: Diag) {
		self.diagnostics.push(diag);
	}

	// TODO: Functions to push syntax highlighting spans. Properly deals with calls when we are within a macro.

	fn colour(&mut self, span: Span, token: SyntaxToken) {
		// When we are within a macro, we don't want to produce syntax tokens.
		if let None = self.temp_replacement_stream {
			self.syntax_tokens.push((token, span));
		}
	}

	/// Returns whether the `Lexer` has reached the end of the token list.
	fn is_done(&self) -> bool {
		// We check that the cursor is equal to the length, because that means we have gone past the last token
		// of the string, and hence, we are done.
		self.cursor == self.token_stream.len()
	}

	/// Returns the [`Span`] of the current `Token`.
	///
	/// *Note:* If we have reached the end of the tokens, this will return the value of
	/// [`get_last_span()`](Self::get_last_span).
	fn get_current_span(&self) -> Span {
		// FIXME: replacement
		match self.token_stream.get(self.cursor) {
			Some(t) => t.1,
			None => self.get_last_span(),
		}
	}

	/// Returns the [`Span`] of the previous `Token`.
	///
	/// *Note:* If the current token is the first, the span returned will be `0-0`.
	fn get_previous_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.get(self.cursor - 1)
			.map_or(Span::new_zero_width(0), |t| t.1)
	}

	/// Returns the [`Span`] of the last `Token`.
	///
	/// *Note:* If there are no tokens, the span returned will be `0-0`.
	fn get_last_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.last()
			.map_or(Span::new_zero_width(0), |t| t.1)
	}
}

/// Parses an individual statement at the current position.
fn parse_stmt(walker: &mut Walker, nodes: &mut Vec<ast::Node>) {
	use crate::token::preprocessor::{self, DefineToken};

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
				kw,
				mut ident_tokens,
				body_tokens,
			} => {
				walker.colour(token_span.first_char(), SyntaxToken::Directive);
				walker.colour(kw, SyntaxToken::Directive);

				if ident_tokens.is_empty() {
					// TODO: Emit error
				} else if ident_tokens.len() == 1 {
					// We have an object-like macro.

					// Panic: If this has a length of `1`, it's guaranteed that the token is an `Ident` token.
					let ident = match ident_tokens.remove(0) {
						(DefineToken::Ident(s), span) => (s, span),
						_ => unreachable!(),
					};
					walker.colour(ident.1, SyntaxToken::ObjectMacro);

					let body_tokens =
						preprocessor::concat_object_macro_body(body_tokens);
					body_tokens.iter().for_each(|(t, s)| {
						walker.colour(*s, t.non_semantic_colour())
					});
					// FIXME: Iterate through the tokens and look for any already-defined macros, to expand them.
					walker.register_macro(ident, body_tokens);
				} else {
					// We have a function-like macro.
					// TODO: Colour the `body_tokens`
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
				let span = *token_span;
				walker.colour(*token_span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
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
