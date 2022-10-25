pub mod ast;
mod syntax;

pub use syntax::*;

use crate::{
	error::{Diag, PreprocDefineDiag},
	token::{preprocessor::TokenStream as PreprocStream, Token, TokenStream},
	Span, Spanned,
};
use ast::*;
use std::collections::{HashMap, HashSet};

pub type TranslationUnit = (Vec<ast::Node>, Vec<Diag>, Vec<Spanned<SyntaxToken>>);

pub fn parse_from_str(source: &str) -> TokenTree {
	let (mut token_stream, metadata) = crate::token::parse_from_str(source);

	// Skip tree generation if there are no conditional compilation blocks.
	if !metadata.contains_conditional_compilation {
		return TokenTree {
			content: vec![TreeNode {
				parent: None,
				content: vec![Content::Tokens(token_stream)],
			}],
			order_by_appearance: vec![],
			contains_conditional_compilation: false,
		};
	}

	fn push_condition(arena: &mut Vec<TreeNode>, id: usize) -> usize {
		let new_id = arena.len();
		arena.push(TreeNode {
			parent: Some(id),
			content: vec![Content::Tokens(vec![])],
		});
		arena
			.get_mut(id)
			.unwrap()
			.content
			.push(Content::ConditionalBlock {
				if_: new_id,
				completed_if: false,
				elses: vec![],
			});
		new_id
	}

	fn push_token(arena: &mut Vec<TreeNode>, id: usize, token: Spanned<Token>) {
		let node = arena.get_mut(id).unwrap();
		match node.content.last_mut() {
			Some(content) => match content {
				Content::Tokens(v) => v.push(token),
				Content::ConditionalBlock { .. } => {
					node.content.push(Content::Tokens(vec![token]));
				}
			},
			None => node.content.push(Content::Tokens(vec![token])),
		};
	}

	let mut arena = vec![TreeNode {
		parent: None,
		content: vec![Content::Tokens(vec![])],
	}];
	let mut stack = vec![0];
	let mut order_by_appearance = vec![(0, 0)];
	loop {
		let (token, token_span) = if !token_stream.is_empty() {
			token_stream.remove(0)
		} else {
			break;
		};

		match token {
			Token::Directive(d) => match d {
				PreprocStream::IfDef { .. }
				| PreprocStream::IfNotDef { .. }
				| PreprocStream::If { .. } => {
					let new_id =
						push_condition(&mut arena, *stack.last().unwrap());
					order_by_appearance.push((new_id, *stack.last().unwrap()));
					stack.push(new_id);
				}
				PreprocStream::ElseIf { .. } => {
					if stack.len() > 1 {
						stack.pop();
						let new_id = arena.len();
						arena.push(TreeNode {
							parent: Some(*stack.last().unwrap()),
							content: vec![],
						});
						let container =
							arena.get_mut(*stack.last().unwrap()).unwrap();
						if let Some(Content::ConditionalBlock {
							if_: _,
							completed_if,
							elses,
						}) = container.content.last_mut()
						{
							*completed_if = true;
							elses.push((Condition::ElseIf, new_id));
							order_by_appearance
								.push((new_id, *stack.last().unwrap()));
							stack.push(new_id);
						} else {
							// TODO: Error.
						}
					} else {
						// TODO: Emit error.
					}
				}
				PreprocStream::Else { .. } => {
					if stack.len() > 1 {
						stack.pop();
						let new_id = arena.len();
						arena.push(TreeNode {
							parent: Some(*stack.last().unwrap()),
							content: vec![],
						});
						let container =
							arena.get_mut(*stack.last().unwrap()).unwrap();
						if let Some(Content::ConditionalBlock {
							if_: _,
							completed_if,
							elses,
						}) = container.content.last_mut()
						{
							*completed_if = true;
							elses.push((Condition::Else, new_id));
							order_by_appearance
								.push((new_id, *stack.last().unwrap()));
							stack.push(new_id);
						} else {
							// TODO: Error.
						}
					} else {
						// TODO: Emit error.
					}
				}
				PreprocStream::EndIf { .. } => {
					if stack.len() > 1 {
						stack.pop();
					} else {
						// TODO: Emit error.
					}
				}
				_ => push_token(
					&mut arena,
					*stack.last().unwrap(),
					(Token::Directive(d), token_span),
				),
			},
			_ => push_token(
				&mut arena,
				*stack.last().unwrap(),
				(token, token_span),
			),
		}
	}

	TokenTree {
		content: arena,
		order_by_appearance,
		contains_conditional_compilation: true,
	}
}

pub struct TokenTree {
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is:
	/// ```
	/// vec![TreeNode {
	///		parent: None,
	///		content: vec![Content::Tokens(token_stream)],
	///	}]
	/// ```
	content: Vec<TreeNode>,
	/// IDs of the relevant nodes ordered by appearance.
	///
	/// - `0` - The ID of the `[n]`th conditional node,
	/// - `1` - The ID of the node which this conditional node depends on.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is empty.
	order_by_appearance: Vec<(usize, usize)>,

	/// Whether there are any conditional compilation brances.
	contains_conditional_compilation: bool,
}

impl TokenTree {
	/// Parses the root token stream.
	///
	/// Whilst this is guaranteed to succeed, if the entire source string is wrapped within a conditional block
	/// this will return an empty AST.
	pub fn root(&self) -> TranslationUnit {
		let streams = if !self.contains_conditional_compilation {
			// Panics: See invariant.
			match self.content.get(0).unwrap().content.first().unwrap() {
				Content::Tokens(s) => vec![s.clone()],
				Content::ConditionalBlock { .. } => unreachable!(),
			}
		} else {
			let mut streams = Vec::new();
			let node = self.content.get(0).unwrap();
			for content in &node.content {
				match content {
					Content::Tokens(s) => streams.push(s.clone()),
					Content::ConditionalBlock { .. } => {}
				}
			}

			streams
		};

		let mut walker = Walker::new(streams);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		(nodes, walker.diagnostics, walker.syntax_tokens)
	}

	/// Parses a token tree by enabling conditional branches in the order of their appearance.
	///
	/// This method can return an `Err` in the following cases:
	/// - The `order` has a number which doesn't exist,
	/// - The `order` has a number which depends on another number that is missing.
	pub fn parse_by_order_of_appearance(
		&self,
		order: impl AsRef<[usize]>,
	) -> Result<TranslationUnit, ParseErr> {
		let order = order.as_ref();

		if !self.contains_conditional_compilation {
			return Err(ParseErr::NoConditionalCompilation);
		}

		// Check that the order is valid.
		{
			let mut visited_node_ids = vec![0];
			for num in order {
				let (id, parent_id) = match self.order_by_appearance.get(*num) {
					Some(t) => t,
					None => return Err(ParseErr::InvalidNum(*num)),
				};

				if !visited_node_ids.contains(parent_id) {
					return Err(ParseErr::InvalidChain(*num));
				}

				visited_node_ids.push(*id);
			}
		}

		let mut order_idx = 0;
		let mut streams = Vec::new();
		let mut nodes = vec![(0, 0)];
		'outer: loop {
			let current_order_id = {
				match order.get(order_idx) {
					Some(num) => match self.order_by_appearance.get(*num) {
						Some((arena_id, _)) => Some(*arena_id),
						None => unreachable!(),
					},
					None => None,
				}
			};

			let (node_id, content_idx) = nodes.last_mut().unwrap();
			let node = self.content.get(*node_id).unwrap();

			while let Some(inner) = &node.content.get(*content_idx) {
				*content_idx += 1;
				match inner {
					Content::Tokens(s) => streams.push(s.clone()),
					Content::ConditionalBlock { if_, elses, .. } => {
						// Check if any of the conditional branches match the current order number.
						if let Some(current_order_id) = current_order_id {
							if *if_ == current_order_id {
								nodes.push((*if_, 0));
								order_idx += 1;
								continue 'outer;
							} else {
								for (_, else_) in elses {
									if *else_ == current_order_id {
										nodes.push((*else_, 0));
										order_idx += 1;
										continue 'outer;
									}
								}
							}
						}
					}
				}
			}

			// We have consumed all the content of this node which means we can pop it from the stack and continue
			// with the parent node (if there is one).
			if nodes.len() > 1 {
				nodes.pop();
			} else {
				break 'outer;
			}
		}

		let mut walker = Walker::new(streams);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		Ok((nodes, walker.diagnostics, walker.syntax_tokens))
	}

	#[allow(unused)]
	pub fn parse_by_order_of_nesting(
		&self,
		order: impl AsRef<[(usize, usize)]>,
	) -> Option<TranslationUnit> {
		todo!()
	}
}

#[derive(Debug)]
pub enum ParseErr {
	/// The number doesn't exist.
	InvalidNum(usize),
	/// The number has a dependent number that was not specified.
	InvalidChain(usize),
	/// This tree contains no conditional compilation branches.
	NoConditionalCompilation,
}

#[derive(Debug)]
struct TreeNode {
	parent: Option<usize>,
	content: Vec<Content>,
}

#[derive(Debug)]
enum Content {
	Tokens(Vec<Spanned<Token>>),
	ConditionalBlock {
		if_: usize,
		completed_if: bool,
		elses: Vec<(Condition, usize)>,
	},
}

#[derive(Debug)]
enum Condition {
	ElseIf,
	Else,
}

pub(crate) struct Walker {
	/// The active token streams.
	///
	/// - `0` - The macro identifier, (for the root source stream this is just `""`),
	/// - `1` - The token stream,
	/// - `2` - The cursor.
	streams: Vec<(String, TokenStream, usize)>,

	original_sources: Vec<TokenStream>,

	/// The currently defined macros.
	///
	/// Key: The macro identifier.
	///
	/// Value:
	/// - `0` - The span of the identifier,
	/// - `1` - The body/replacement-list of tokens.
	macros: HashMap<String, (Span, TokenStream)>,
	/// The span of an initial macro call site. Only the first macro call site is registered here.
	macro_call_site: Option<Span>,
	/// The actively-called macro identifiers.
	active_macros: HashSet<String>,

	/// Any diagnostics created from the tokens parsed so-far.
	diagnostics: Vec<Diag>,

	/// The syntax highlighting tokens created from the tokens parsed so-far.
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(mut token_streams: Vec<TokenStream>) -> Self {
		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

		let first_source = token_streams.remove(0);

		Self {
			streams: vec![("".into(), first_source, 0)],
			original_sources: token_streams,
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

				let ident = identifier.clone();
				if self.streams.len() == 1 {
					// If we aren't in a macro, that means we've finished the current source stream but there may
					// be another one (as they can be split up due to conditional compilation).

					if self.original_sources.is_empty() {
						// We have reached the final end.
						self.streams.remove(0);
						break;
					} else {
						let mut next_source = self.original_sources.remove(0);
						let (_, s, c) = self.streams.get_mut(0).unwrap();
						std::mem::swap(s, &mut next_source);
						*c = 0;
						dont_increment = true;
						continue;
					}
				} else {
					// Panic: Anytime a stream is added the identifier is inserted into the set.
					self.active_macros.remove(&ident);
					self.streams.remove(self.streams.len() - 1);
					continue;
				}
			}

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
								// We only syntax highlight when it is the first macro call.
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

	/* /// Returns any potential comment tokens until the next non-comment token.
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
	} */

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

	/// Creates a syntax highlighting token over the given span.
	fn colour(&mut self, span: Span, token: SyntaxToken) {
		// When we are within a macro, we don't want to produce syntax tokens.
		if self.streams.len() == 1 {
			self.syntax_tokens.push((token, span));
		}
	}

	/// Returns whether the walker has reached the end of the token streams.
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
			PreprocStream::Define {
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

					// Since object-like macros don't have parameters, we can perform the concatenation right here
					// since we know the contents of the macro body will never change.
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
			PreprocStream::Undef {
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
