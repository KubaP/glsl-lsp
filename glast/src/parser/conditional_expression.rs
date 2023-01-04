//! The parser for conditional directive expressions.

use super::{
	ast::conditional::{BinOp, BinOpTy, Expr, ExprTy, PreOp, PreOpTy},
	ast::Ident,
	Macro, SyntaxModifiers, SyntaxToken, SyntaxType,
};
use crate::{
	diag::{ExprDiag, PreprocDefineDiag, Semantic, Syntax},
	lexer::preprocessor::ConditionToken,
	Either, Span, SpanEncoding, Spanned,
};
use std::{
	collections::{HashMap, HashSet, VecDeque},
	fmt::Write,
};

/*
The functionality of this parser is largely copied from the expression parser. The decision to copy the relevant
parts of the code over was done in order to prevent the complexity of the expression parser from growing even
larger. There are already a *lot* of conditions and checks and feature-gates; adding more would make it even
less maintainable. Furthermore, this parser uses an entirely different token type so the amount of direct code
reuse would be limited anyway.

The functionality of this walker is largely copied from the main walker. It's slightly simplified since there is
only one source token stream, but all of the macro-expansion related functionality has been copied verbatim. The
only change is that the conditional tokens must get converted to/from normal tokens as macro bodies are defined
in normal tokens, and that if the macro has no body but is defined, the token `1` is returned.
*/

/// Tries to parse a conditional directive expression.
///
/// This function consumes all of the tokens; if a syntax error is encountered and the parser cannot continue, it
/// will invalidate the rest of the tokens.
pub(super) fn cond_parser(
	tokens: Vec<Spanned<ConditionToken>>,
	macros: &HashMap<String, (Span, Macro)>,
	span_encoding: SpanEncoding,
) -> (Option<Expr>, Vec<Syntax>, Vec<SyntaxToken>) {
	let mut walker = Walker::new(tokens, macros, span_encoding);

	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: Vec::new(),
	};
	parser.parse(&mut walker);

	(
		parser.create_ast(),
		walker.syntax_diags,
		walker.syntax_tokens,
	)
}

/// Allows for stepping through a token stream. Takes care of dealing with irrelevant details from the perspective
/// of the parser, such as comments and macro expansion.
struct Walker<'a> {
	/// The active token streams.
	///
	/// - `0` - The macro identifier, (for the root source stream this is just `""`).
	/// - `1` - The token stream.
	/// - `2` - The cursor.
	streams: Vec<(String, Vec<Spanned<ConditionToken>>, usize)>,

	/// The currently defined macros.
	///
	/// Key: The macro identifier.
	///
	/// Value:
	/// - `0` - The span of the macro signature.
	/// - `1` - Macro information.
	macros: &'a HashMap<String, (Span, Macro)>,
	/// The span of an initial macro call site. Only the first macro call site is registered here.
	macro_call_site: Option<Span>,
	/// The actively-called macro identifiers.
	active_macros: HashSet<String>,
	/// Whether macro expansion upon encountering an identifier is disabled.
	disable_macro_expansion: bool,

	/// Any syntax diagnostics created from the tokens parsed so-far.
	syntax_diags: Vec<Syntax>,
	/// Any semantic diagnostics created from the tokens parsed so-far.
	semantic_diags: Vec<Semantic>,

	/// The syntax highlighting tokens created from the tokens parsed so-far.
	syntax_tokens: Vec<SyntaxToken>,
	/// The type of encoding of spans.
	span_encoding: SpanEncoding,
}

impl<'a> Walker<'a> {
	/// Constructs a new walker.
	fn new(
		tokens: Vec<Spanned<ConditionToken>>,
		macros: &'a HashMap<String, (Span, Macro)>,
		span_encoding: SpanEncoding,
	) -> Self {
		let streams = if !tokens.is_empty() {
			vec![("".into(), tokens, 0)]
		} else {
			vec![]
		};

		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

		let mut walker = Self {
			streams,
			macros,
			macro_call_site: None,
			active_macros,
			disable_macro_expansion: false,
			syntax_diags: Vec::new(),
			semantic_diags: Vec::new(),
			syntax_tokens: Vec::new(),
			span_encoding,
		};
		walker._advance(true);
		walker
	}

	/// Returns a reference to the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<Spanned<&ConditionToken>> {
		if self.streams.is_empty() {
			None
		} else if self.streams.len() == 1 {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream.get(*cursor).map(|(t, s)| (t, *s))
		} else {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream
				.get(*cursor)
				.map(|(t, _)| (t, self.macro_call_site.unwrap()))
		}
	}

	/// Advances the cursor by one.
	///
	/// This method correctly steps into/out-of macros and consumes any comments.
	fn advance(&mut self) {
		self._advance(false);
	}

	fn _advance(&mut self, mut dont_increment: bool) {
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
				// Panic: Anytime a stream is added the identifier is inserted into the set.
				self.active_macros.remove(&ident);
				self.streams.remove(self.streams.len() - 1);
				continue;
			}

			let (token, token_span) = stream.get(*cursor).unwrap();

			match token {
				// We check if the new token is a macro call site.
				ConditionToken::Ident(s) if !self.disable_macro_expansion => {
					if let Some((signature_span, macro_)) = self.macros.get(s) {
						if self.active_macros.contains(s) {
							// We have already visited a macro with this identifier. Recursion is not supported so
							// we don't continue.
							break;
						}

						let ident_span = *token_span;

						if let Macro::Function { params, body } = macro_ {
							// We have an identifier which matches a function-like macro, so we are expecting a
							// parameter list in the current token stream before we do any switching.

							// We don't need to worry about having to switch source streams because that would
							// imply that a conditional compilation directive is in the middle of a function-like
							// macro call site, which isn't valid. A function-like macro call cannot have
							// preprocessor directives within, which means that the source stream won't be split up
							// by a conditional, which means the entire invocation of the macro will be within this
							// stream.

							let mut tmp_cursor = *cursor + 1;
							let mut syntax_spans = vec![SyntaxToken {
								ty: SyntaxType::FunctionMacro,
								modifiers: SyntaxModifiers::empty(),
								span: ident_span,
							}];
							loop {
								match stream.get(tmp_cursor) {
									Some((token, token_span)) => match token {
										ConditionToken::LineComment(_)
										| ConditionToken::BlockComment {
											..
										} => {
											syntax_spans.push(SyntaxToken {
												ty: SyntaxType::Comment,
												modifiers:
													SyntaxModifiers::empty(),
												span: *token_span,
											});
											tmp_cursor += 1;
										}
										_ => break,
									},
									None => break 'outer,
								}
							}

							// Consume the opening `(` parenthesis.
							let l_paren_span = match stream.get(tmp_cursor) {
								Some((token, token_span)) => match token {
									ConditionToken::LParen => {
										syntax_spans.push(SyntaxToken {
											ty: SyntaxType::Punctuation,
											modifiers: SyntaxModifiers::empty(),
											span: *token_span,
										});
										*cursor = tmp_cursor + 1;
										*token_span
									}
									_ => {
										// We did not immediately encounter a parenthesis, which means that this is
										// not a call to a function-like macro even if the names match.
										break;
									}
								},
								None => break,
							};

							// Look for any arguments until we hit a closing `)` parenthesis. The preprocessor
							// immediately switches to the next argument when a `,` is encountered, unless we are
							// within a parenthesis group.
							/* #[derive(PartialEq)]
							enum Prev {
								None,
								Param,
								Comma,
								Invalid,
							}
							let mut prev = Prev::None; */
							let mut prev_span = l_paren_span;
							let mut paren_groups = 0;
							let mut args = Vec::new();
							let mut arg = Vec::new();
							let mut first_token = true;
							let r_paren_span = loop {
								let (token, token_span) = match stream
									.get(*cursor)
								{
									Some(t) => t,
									None => {
										self.syntax_diags.push(Syntax::PreprocDefine(PreprocDefineDiag::ParamsExpectedRParen(
											prev_span.next_single_width()
										)));
										break 'outer;
									}
								};

								match token {
									ConditionToken::Comma => {
										syntax_spans.push(SyntaxToken {
											ty: SyntaxType::Punctuation,
											modifiers: SyntaxModifiers::empty(),
											span: *token_span,
										});
										if paren_groups == 0 {
											let arg = std::mem::take(&mut arg);
											args.push(arg);
											/* prev = Prev::Comma; */
										}
										prev_span = *token_span;
										*cursor += 1;
										continue;
									}
									ConditionToken::LParen => {
										paren_groups += 1;
									}
									ConditionToken::RParen => {
										if paren_groups == 0 {
											// We have reached the end of this function-like macro call site.
											syntax_spans.push(SyntaxToken {
												ty: SyntaxType::Punctuation,
												modifiers:
													SyntaxModifiers::empty(),
												span: *token_span,
											});
											if !first_token {
												let arg =
													std::mem::take(&mut arg);
												args.push(arg);
											}
											// It is important that we don't increment the cursor to the next token
											// after the macro call site. This is because once this macro is
											// finished, and we return to the previous stream, we will
											// automatically increment the cursor onto the next token which will be
											// the first token after the macro call site. The object-like macro
											// branch also doesn't perform this increment.
											// *cursor += 1;
											break *token_span;
										}
										paren_groups -= 1;
									}
									_ => {}
								}
								syntax_spans.push(SyntaxToken {
									ty: token.non_semantic_colour(),
									modifiers: SyntaxModifiers::empty(),
									span: *token_span,
								});
								arg.push((token.clone(), *token_span));
								/* prev = Prev::Param; */
								*cursor += 1;
								first_token = false;
							};
							let call_site_span =
								Span::new(ident_span.start, r_paren_span.end);

							// We have a set of arguments now.
							if params.len() != args.len() {
								// If there is a mismatch in the argument/parameter count, we ignore this macro
								// call and move onto the next token after the call site.
								self.semantic_diags.push(
									Semantic::FunctionMacroMismatchedArgCount(
										call_site_span,
										*signature_span,
									),
								);
								continue;
							}
							let mut param_map = HashMap::new();
							params.iter().zip(args.into_iter()).for_each(
								|(ident, tokens)| {
									param_map.insert(&ident.name, tokens);
								},
							);

							// We now go through the replacement token list and replace any identifiers which match
							// a parameter name with the relevant argument's tokens.
							let mut new_body = Vec::with_capacity(body.len());
							for (token, token_span) in body {
								match &token {
									crate::lexer::Token::Ident(str) => {
										if let Some(arg) = param_map.get(&str) {
											for token in arg {
												new_body.push(ConditionToken::to_normal_token(token.clone()));
											}
											continue;
										}
									}
									_ => {}
								}
								new_body.push((token.clone(), *token_span));
							}

							// Then, we perform token concatenation.
							let (new_body, mut syntax, mut semantic) =
								crate::lexer::preprocessor::concat_macro_body(
									new_body,
									self.span_encoding,
								);
							self.syntax_diags.append(&mut syntax);
							self.semantic_diags.append(&mut semantic);

							if body.is_empty() {
								let ident = s.to_owned();

								if self.streams.len() == 1 {
									// We only syntax highlight when it is the first macro call.
									self.macro_call_site = Some(ident_span);
									self.syntax_tokens
										.append(&mut syntax_spans);
								}

								self.active_macros.insert(ident.clone());
								self.streams.push((
									ident,
									vec![(
										ConditionToken::Num(1),
										signature_span.end_zero_width(),
									)],
									0,
								));

								// The first token in a new stream could be another macro call, so we re-run the
								// loop on this new stream in case.
								dont_increment = true;
								continue;
							}

							let ident = s.to_owned();

							// We only syntax highlight and note the macro call site when it is the first macro
							// call.
							if self.streams.len() == 1 {
								self.macro_call_site = Some(call_site_span);
								self.syntax_tokens.append(&mut syntax_spans);
							}

							self.active_macros.insert(ident.clone());

							// Since macro bodies are parsed with the normal GLSL lexer, but we are working with
							// conditional directive tokens, we must convert them to the valid subset. The easiest
							// way which will also 100% guarantee correct behaviour is to write out the macro body
							// as a string, and then parse the string as a condition body. This ensures any weird
							// edge cases are correctly handled.
							let mut s = String::with_capacity(50);
							for (token, _) in new_body {
								write!(s, "{token}").unwrap();
							}
							use crate::lexer::{self, Lexer, Utf16};
							let mut lexer: Lexer<Utf16> =
								Lexer::new(&s, self.span_encoding);
							let new_tokens =
								lexer::preprocessor::parse_condition_tokens(
									&mut lexer,
								);
							self.streams.push((ident, new_tokens, 0));

							// The first token in the new stream could be another macro call, so we re-run the loop
							// on this new stream in case.
							dont_increment = true;
							continue;
						} else if let Macro::Object(stream) = macro_ {
							if stream.is_empty() {
								let ident = s.to_owned();

								if self.streams.len() == 1 {
									// We only syntax highlight when it is the first macro call.
									self.macro_call_site = Some(ident_span);
									self.syntax_tokens.push(SyntaxToken {
										ty: SyntaxType::ObjectMacro,
										modifiers: SyntaxModifiers::CONDITIONAL,
										span: ident_span,
									});
								}

								self.active_macros.insert(ident.clone());
								self.streams.push((
									ident,
									vec![(
										ConditionToken::Num(1),
										signature_span.end_zero_width(),
									)],
									0,
								));

								// The first token in a new stream could be another macro call, so we re-run the
								// loop on this new stream in case.
								dont_increment = true;
								continue;
							}

							let ident = s.to_owned();

							// We only syntax highlight and note the macro call site when it is the first macro
							// call.
							if self.streams.len() == 1 {
								self.macro_call_site = Some(ident_span);
								self.syntax_tokens.push(SyntaxToken {
									ty: SyntaxType::ObjectMacro,
									modifiers: SyntaxModifiers::CONDITIONAL,
									span: ident_span,
								});
							}

							self.active_macros.insert(ident.clone());

							// Since macro bodies are parsed with the normal GLSL lexer, but we are working with
							// conditional directive tokens, we must convert them to the valid subset. The easiest
							// way which will also 100% guarantee correct behaviour is to write out the macro body
							// as a string, and then parse the string as a condition body. This ensures any weird
							// edge cases are correctly handled.
							let mut s = String::with_capacity(50);
							for (token, _) in stream {
								write!(s, "{token}").unwrap();
							}
							use crate::lexer::{self, Lexer, Utf16};
							let mut lexer: Lexer<Utf16> =
								Lexer::new(&s, self.span_encoding);
							let new_tokens =
								lexer::preprocessor::parse_condition_tokens(
									&mut lexer,
								);
							self.streams.push((ident, new_tokens, 0));

							// The first token in a new stream could be another macro call, so we re-run the loop
							// on this new stream in case.
							dont_increment = true;
							continue;
						}
					} else {
						break;
					}
				}
				// We want to consume any comments since they are semantically ignored.
				ConditionToken::LineComment(_) => {
					let token_span = *token_span;
					if self.streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						self.syntax_tokens.push(SyntaxToken {
							ty: SyntaxType::Comment,
							modifiers: SyntaxModifiers::empty(),
							span: token_span,
						});
					}
				}
				ConditionToken::BlockComment { contains_eof, .. } => {
					if *contains_eof {
						self.syntax_diags.push(Syntax::BlockCommentMissingEnd(
							token_span.end_zero_width(),
						));
					}
					let token_span = *token_span;
					if self.streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						self.syntax_tokens.push(SyntaxToken {
							ty: SyntaxType::Comment,
							modifiers: SyntaxModifiers::empty(),
							span: token_span,
						});
					}
				}
				_ => break,
			}
		}

		if self.streams.len() <= 1 {
			self.macro_call_site = None;
		}
	}

	/// Returns whether the walker has reached the end of the token stream.
	fn is_done(&self) -> bool {
		self.streams.is_empty()
	}

	/// Pushes a syntax highlighting token over the given span.
	fn push_colour(&mut self, span: Span, token: SyntaxType) {
		self.syntax_tokens.push(SyntaxToken {
			ty: token,
			modifiers: SyntaxModifiers::CONDITIONAL,
			span,
		});
	}
}

/// A node; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Node {
	ty: NodeTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum NodeTy {
	Num(usize),
	Defined(Ident),
}

/// A node operator; used in the parser stack.
#[derive(Debug, Clone, PartialEq)]
struct Op {
	ty: OpTy,
	span: Span,
}

#[derive(Debug, Clone, PartialEq)]
enum OpTy {
	/* OPERATORS */
	/* - `0` - Whether to consume a node for the right-hand side expression. */
	Add(bool),
	Sub(bool),
	Mul(bool),
	Div(bool),
	Rem(bool),
	And(bool),
	Or(bool),
	Xor(bool),
	LShift(bool),
	RShift(bool),
	EqEq(bool),
	NotEq(bool),
	AndAnd(bool),
	OrOr(bool),
	Gt(bool),
	Lt(bool),
	Ge(bool),
	Le(bool),
	Neg(bool),
	Flip(bool),
	Not(bool),
	/* GROUPS */
	/// The `(` token.
	ParenStart,
	/// A parenthesis group. This operator spans from the opening parenthesis to the closing parenthesis.
	///
	/// - `0` - Whether to consume a node for the inner expression within the `(...)` parenthesis.
	/// - `1` - The span of the opening parenthesis.
	/// - `2` - The span of the closing parenthesis. If this is zero-width, that means there is no `)` token
	///   present.
	Paren(bool, Span, Span),
}

impl Op {
	/// Converts from a lexer `ConditionalToken` token to the `Op` type used in this expression parser.
	fn from_token(token: ConditionToken, span: Span) -> Self {
		Self {
			span,
			ty: match token {
				ConditionToken::Add => OpTy::Add(false),
				ConditionToken::Sub => OpTy::Sub(false),
				ConditionToken::Mul => OpTy::Mul(false),
				ConditionToken::Div => OpTy::Div(false),
				ConditionToken::Rem => OpTy::Rem(false),
				ConditionToken::And => OpTy::And(false),
				ConditionToken::Or => OpTy::Or(false),
				ConditionToken::Xor => OpTy::Xor(false),
				ConditionToken::LShift => OpTy::LShift(false),
				ConditionToken::RShift => OpTy::RShift(false),
				ConditionToken::EqEq => OpTy::EqEq(false),
				ConditionToken::NotEq => OpTy::NotEq(false),
				ConditionToken::AndAnd => OpTy::AndAnd(false),
				ConditionToken::OrOr => OpTy::OrOr(false),
				ConditionToken::Gt => OpTy::Gt(false),
				ConditionToken::Lt => OpTy::Lt(false),
				ConditionToken::Ge => OpTy::Ge(false),
				ConditionToken::Le => OpTy::Le(false),
				ConditionToken::Not | ConditionToken::Flip | _ => {
					// These tokens are handled by individual branches in the main parser loop.
					unreachable!("Given a conditional `token` which should never be handled by this function.")
				}
			},
		}
	}

	/// Returns the precedence of this operator.
	#[rustfmt::skip]
	fn precedence(&self) -> usize {
		match &self.ty {
			OpTy::Neg(_)
			| OpTy::Flip(_)
			| OpTy::Not(_) => 29,
			OpTy::Mul(_) | OpTy::Div(_) | OpTy::Rem(_) => 27,
			OpTy::Add(_) | OpTy::Sub(_) => 25,
			OpTy::LShift(_) | OpTy::RShift(_) => 23,
			OpTy::Lt(_) | OpTy::Gt(_) | OpTy::Le(_) | OpTy::Ge(_) => 21,
			OpTy::EqEq(_) | OpTy::NotEq(_) => 19,
			OpTy::And(_) => 17,
			OpTy::Xor(_) => 15,
			OpTy::Or(_) => 13,
			OpTy::AndAnd(_) => 11,
			OpTy::OrOr(_) => 9,
			// These are never directly checked for precedence, but rather have special branches.
			_ => unreachable!("The conditional expression operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!"),
		}
	}

	/// Returns whether this operator is a binary operator.
	fn is_bin(&self) -> bool {
		match &self.ty {
			OpTy::Add(_)
			| OpTy::Sub(_)
			| OpTy::Mul(_)
			| OpTy::Div(_)
			| OpTy::Rem(_)
			| OpTy::And(_)
			| OpTy::Or(_)
			| OpTy::Xor(_)
			| OpTy::LShift(_)
			| OpTy::RShift(_)
			| OpTy::EqEq(_)
			| OpTy::NotEq(_)
			| OpTy::AndAnd(_)
			| OpTy::OrOr(_)
			| OpTy::Gt(_)
			| OpTy::Lt(_)
			| OpTy::Ge(_)
			| OpTy::Le(_) => true,
			OpTy::Neg(_) | OpTy::Flip(_) | OpTy::Not(_) => false,
			OpTy::ParenStart => false,
			OpTy::Paren(_, _, _) => false,
		}
	}

	fn to_bin_op(self) -> BinOp {
		let ty = match self.ty {
				OpTy::Add(_) => BinOpTy::Add,
				OpTy::Sub(_) => BinOpTy::Sub,
				OpTy::Mul(_) => BinOpTy::Mul,
				OpTy::Div(_) => BinOpTy::Div,
				OpTy::Rem(_) => BinOpTy::Rem,
				OpTy::And(_) => BinOpTy::And,
				OpTy::Or(_) => BinOpTy::Or,
				OpTy::Xor(_) => BinOpTy::Xor,
				OpTy::LShift(_) => BinOpTy::LShift,
				OpTy::RShift(_) => BinOpTy::RShift,
				OpTy::EqEq(_) => BinOpTy::EqEq,
				OpTy::NotEq(_) => BinOpTy::NotEq,
				OpTy::AndAnd(_) => BinOpTy::AndAnd,
				OpTy::OrOr(_) => BinOpTy::OrOr,
				OpTy::Gt(_) => BinOpTy::Gt,
				OpTy::Lt(_) => BinOpTy::Lt,
				OpTy::Ge(_) => BinOpTy::Ge,
				OpTy::Le(_) => BinOpTy::Le,
				_ => unreachable!("Given a conditional expression `ty` which should not be handled here.")
			};

		BinOp {
			span: self.span,
			ty,
		}
	}
}

/// An open grouping of items.
enum Group {
	/// A parenthesis group.
	///
	/// - `0` - Whether this group has an inner expression within the parenthesis.
	/// - `1` - The span of the opening parenthesis.
	Paren(bool, Span),
}

/// The implementation of a shunting yard-based parser.
struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Node, Op>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The last entry is the group being currently parsed.
	groups: Vec<Group>,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Op) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			match back.ty {
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				OpTy::ParenStart => break,
				_ => {}
			}

			if op.precedence() == back.precedence()
				&& op.is_bin() && back.is_bin()
			{
				// By checking for `==`, we make operators of the same precedence right-associative. This is
				// important so that the final constructed recursive expression tree is nested in such an order
				// that allows it to be evaluated with the correct operator order. If this wasn't in place, an
				// expression such as `2 - 1 - 1` would evaluate to `2`, because the `1 - 1` part would be
				// evaluated first.
				//
				// Note that we only do this for binary operators. For unaries this logic actually breaks the final
				// output.
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
			} else if op.precedence() < back.precedence() {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
			} else {
				// If the precedence is greater, we aren't going to be moving any operators to the stack anymore,
				// so we can exit the loop.
				break;
			}
		}
		self.operators.push_back(op);
	}

	/// Registers the end of a parenthesis group, popping any operators until the start of the group is reached.
	fn end_paren(&mut self, end_span: Span) -> Result<(), ()> {
		let group = if !self.groups.is_empty() {
			self.groups.remove(self.groups.len() - 1)
		} else {
			return Err(());
		};

		match group {
			Group::Paren(has_inner, l_paren) => {
				while self.operators.back().is_some() {
					let op = self.operators.pop_back().unwrap();

					if let OpTy::ParenStart = op.ty {
						self.stack.push_back(Either::Right(Op {
							span: Span::new(l_paren.start, end_span.end),
							ty: OpTy::Paren(has_inner, l_paren, end_span),
						}));
						break;
					} else {
						// Any other operators get moved, since we are moving everything until we hit the start
						// delimiter.
						self.stack.push_back(Either::Right(op));
					}
				}
			}
		}

		Ok(())
	}

	/// Sets the toggle on the last operator that it has a right-hand side operand, (if applicable).
	fn set_op_rhs_toggle(&mut self) {
		if let Some(op) = self.operators.back_mut() {
			match &mut op.ty {
				OpTy::Add(b)
				| OpTy::Sub(b)
				| OpTy::Mul(b)
				| OpTy::Div(b)
				| OpTy::Rem(b)
				| OpTy::And(b)
				| OpTy::Or(b)
				| OpTy::Xor(b)
				| OpTy::LShift(b)
				| OpTy::RShift(b)
				| OpTy::EqEq(b)
				| OpTy::NotEq(b)
				| OpTy::AndAnd(b)
				| OpTy::OrOr(b)
				| OpTy::Gt(b)
				| OpTy::Lt(b)
				| OpTy::Ge(b)
				| OpTy::Le(b)
				| OpTy::Neg(b)
				| OpTy::Flip(b)
				| OpTy::Not(b) => *b = true,
				_ => {}
			}
		}
		if let Some(Group::Paren(b, _)) = self.groups.last_mut() {
			*b = true;
		}
	}

	/// Returns whether we have just started to parse a parenthesis group, i.e. `..(<HERE>`.
	fn just_started_paren(&self) -> bool {
		if let Some(Group::Paren(has_inner, _)) = self.groups.last() {
			*has_inner == false
		} else {
			false
		}
	}

	/// Returns the [`Span`] of the last item on the stack or operator stack.
	fn get_previous_span(&self) -> Option<Span> {
		let stack_span = self.stack.back().map(|i| match i {
			Either::Left(e) => e.span,
			Either::Right(op) => op.span,
		});
		let op_span = self.operators.back().map(|op| op.span);

		match (stack_span, op_span) {
			(Some(stack), Some(op)) => {
				if stack.is_after(&op) {
					stack_span
				} else {
					op_span
				}
			}
			(Some(_), None) => stack_span,
			(None, Some(_)) => op_span,
			(None, None) => None,
		}
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse(&mut self, walker: &mut Walker) {
		#[derive(PartialEq)]
		enum State {
			/// We are looking for either a) a prefix operator, b) an atom, c) bracket group start, d) function
			/// call group start, e) initializer list group start.
			Operand,
			/// We are looking for either a) a postfix operator, b) an index operator start or end, c) a binary
			/// operator, d) bracket group end, e) function call group end, f) initializer list group end, g) a
			/// comma, h) end of expression.
			AfterOperand,
		}
		let mut state = State::Operand;

		// If this is set to `true`, that means that the parser has exited early because of a syntax error and we
		// want to invalidate the rest of the tokens, (if there are any).
		let mut invalidate_rest = false;

		'main: while !walker.is_done() {
			let (token, span) = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break 'main,
			};

			match token {
				ConditionToken::Num(num) if state == State::Operand => {
					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Num(*num),
						span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					state = State::AfterOperand;
					self.set_op_rhs_toggle();

					walker.push_colour(span, SyntaxType::Number);
				}
				ConditionToken::Num(_) if state == State::AfterOperand => {
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));

					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Ident(_) if state == State::Operand => {
					// Since we are in this branch, that means that the identifier does not match an existing macro
					// name, and since it doesn't match we assume a value of `0`.
					self.stack.push_back(Either::Left(Node {
						ty: NodeTy::Num(0),
						span,
					}));

					// We switch state since after an operand, we are expecting an operator, i.e.
					// `..10 + i` instead of `..10 i`.
					state = State::AfterOperand;
					self.set_op_rhs_toggle();

					walker.push_colour(span, SyntaxType::Ident);
				}
				ConditionToken::Ident(_) if state == State::AfterOperand => {
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));

					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Sub if state == State::Operand => {
					self.set_op_rhs_toggle();
					self.push_operator(Op {
						span,
						ty: OpTy::Neg(false),
					});

					walker.push_colour(span, SyntaxType::Operator);
				}
				ConditionToken::Not if state == State::Operand => {
					self.set_op_rhs_toggle();
					self.push_operator(Op {
						span,
						ty: OpTy::Not(false),
					});

					walker.push_colour(span, SyntaxType::Operator);
				}
				ConditionToken::Flip if state == State::Operand => {
					self.set_op_rhs_toggle();
					self.push_operator(Op {
						span,
						ty: OpTy::Flip(false),
					});

					walker.push_colour(span, SyntaxType::Operator);
				}
				ConditionToken::Not | ConditionToken::Flip
					if state == State::AfterOperand =>
				{
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::InvalidBinOrPostOperator(span),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::LParen if state == State::Operand => {
					self.set_op_rhs_toggle();
					self.operators.push_back(Op {
						span,
						ty: OpTy::ParenStart,
					});
					self.groups.push(Group::Paren(false, span));

					walker.push_colour(span, SyntaxType::Punctuation);
				}
				ConditionToken::LParen if state == State::AfterOperand => {
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::RParen if state == State::AfterOperand => {
					match self.end_paren(span) {
						Ok(_) => {}
						Err(_) => {
							invalidate_rest = true;
							break 'main;
						}
					}

					walker.push_colour(span, SyntaxType::Punctuation);

					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`
				}
				ConditionToken::RParen if state == State::Operand => {
					let prev_op_span = self.get_previous_span();
					let just_started_paren = self.just_started_paren();
					match self.end_paren(span) {
						Ok(_) => {}
						Err(_) => {
							invalidate_rest = true;
							break 'main;
						}
					}

					if just_started_paren {
						walker.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundEmptyParens(Span::new(
								prev_op_span.unwrap().start,
								span.end,
							)),
						));
					} else {
						walker.syntax_diags.push(Syntax::Expr(
							ExprDiag::FoundRParenInsteadOfOperand(
								prev_op_span.unwrap(),
								span,
							),
						))
					}

					state = State::AfterOperand;

					walker.push_colour(span, SyntaxType::Punctuation);
				}
				ConditionToken::Defined if state == State::Operand => {
					walker.disable_macro_expansion = true;
					let defined_kw_span = span;
					walker.push_colour(defined_kw_span, SyntaxType::Keyword);
					walker.advance();

					// Consume either an identifier or an opening parenthesis `(`.
					let (token, token_span) = match walker.peek() {
						Some(t) => t,
						None => {
							walker.syntax_diags.push(Syntax::Expr(
								ExprDiag::ExpectedIdentOrLParenAfterDefinedOp(
									defined_kw_span.next_single_width(),
								),
							));
							break 'main;
						}
					};
					match token {
						ConditionToken::Ident(str) => {
							let ident = str.clone();
							walker.push_colour(token_span, SyntaxType::Ident);
							walker.advance();
							self.stack.push_back(Either::Left(Node {
								ty: NodeTy::Defined(Ident {
									name: ident,
									span: token_span,
								}),
								span: Span::new(
									defined_kw_span.start,
									token_span.end,
								),
							}));
							walker.disable_macro_expansion = false;
							continue 'main;
						}
						ConditionToken::LParen => {
							let l_paren_span = token_span;
							walker.push_colour(
								l_paren_span,
								SyntaxType::Punctuation,
							);
							walker.advance();

							// Consume the identifier.
							let (token, token_span) = match walker.peek() {
								Some(t) => t,
								None => {
									walker.syntax_diags.push(Syntax::Expr(ExprDiag::ExpectedIdentAfterDefineOpLParen(l_paren_span.next_single_width())));
									break 'main;
								}
							};
							let (ident, ident_span) = match token {
								ConditionToken::Ident(str) => {
									let ident = str.clone();
									walker.push_colour(
										token_span,
										SyntaxType::Ident,
									);
									(
										Ident {
											name: ident,
											span: token_span,
										},
										token_span,
									)
								}
								_ => {
									walker.syntax_diags.push(Syntax::Expr(ExprDiag::ExpectedIdentAfterDefineOpLParen(l_paren_span.next_single_width())));
									break 'main;
								}
							};
							walker.advance();

							// Consume the closing parenthesis `)`.
							let (token, token_span) = match walker.peek() {
								Some(t) => t,
								None => {
									walker.syntax_diags.push(Syntax::Expr(ExprDiag::ExpectedRParenAfterDefineOpIdent(ident_span.next_single_width())));
									break 'main;
								}
							};
							match token {
								ConditionToken::RParen => {}
								_ => {
									walker.syntax_diags.push(Syntax::Expr(ExprDiag::ExpectedRParenAfterDefineOpIdent(ident_span.next_single_width())));
									break 'main;
								}
							}
							walker.advance();

							self.stack.push_back(Either::Left(Node {
								ty: NodeTy::Defined(ident),
								span: Span::new(
									defined_kw_span.start,
									token_span.end,
								),
							}));
							walker.disable_macro_expansion = false;
							continue 'main;
						}
						_ => {
							walker.syntax_diags.push(Syntax::Expr(
								ExprDiag::ExpectedIdentOrLParenAfterDefinedOp(
									defined_kw_span.next_single_width(),
								),
							));
							break 'main;
						}
					}
				}
				ConditionToken::Defined if state == State::AfterOperand => {
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::FoundOperandAfterOperand(
							self.get_previous_span().unwrap(),
							span,
						),
					));
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::InvalidNum(_) => {
					invalidate_rest = true;
					break 'main;
				}
				ConditionToken::Invalid(_) => {
					// We have encountered an unexpected token that's not allowed to be part of an expression.
					walker
						.syntax_diags
						.push(Syntax::Expr(ExprDiag::FoundInvalidToken(span)));
					invalidate_rest = true;
					break 'main;
				}
				_ if state == State::AfterOperand => {
					self.push_operator(Op::from_token(token.clone(), span));
					state = State::Operand;

					walker.push_colour(span, SyntaxType::Operator);
				}
				_ if state == State::Operand => {
					walker.syntax_diags.push(Syntax::Expr(
						ExprDiag::InvalidPrefixOperator(span),
					));
					invalidate_rest = true;
					break 'main;
				}
				_ => unreachable!(),
			}

			walker.advance();
		}

		// If we break early because of a syntax error, we want to colour the rest of the tokens as invalid.
		if invalidate_rest {
			walker.advance();
			while let Some((_, span)) = walker.peek() {
				walker.push_colour(span, SyntaxType::Invalid);
				walker.advance();
			}
		}

		// Close any open groups. Any groups still open must be missing a closing delimiter.
		if !self.groups.is_empty() {
			// The end position of this expression will be the end position of the last parsed item. This is
			// important because in the case of encountering an error, the relevant branches above will consume the
			// rest of the tokens since no further processing is done outside of this function. That means that
			// naively getting the last token span could potentially result in an incorrect span.
			let group_end = self.get_previous_span().unwrap().end_zero_width();

			// We don't take ownership of the groups because the `end_paren_defined()` method does that.
			while let Some(group) = self.groups.last() {
				match group {
					Group::Paren(_, l_paren) => {
						walker.syntax_diags.push(Syntax::Expr(
							ExprDiag::UnclosedParens(*l_paren, group_end),
						));
					}
				}
				let _ = self.end_paren(group_end);
			}
		}

		// If there is an open group, then all of the operators will have been already moved as part of the
		// ending function. However, if we didn't need to close any groups, we may have leftover operators which
		// still need moving.
		while let Some(op) = self.operators.pop_back() {
			self.stack.push_back(Either::Right(op));
		}
	}

	/// Converts the internal RPN stack into a singular `Expr` node, which contains the entire expression.
	fn create_ast(&mut self) -> Option<Expr> {
		if self.stack.is_empty() {
			return None;
		}

		let mut stack: VecDeque<Expr> = VecDeque::new();
		let pop_back = |stack: &mut VecDeque<Expr>| stack.pop_back().unwrap();

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the n-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(item) = self.stack.pop_front() {
			match item {
				Either::Left(node) => match node.ty {
					NodeTy::Num(num) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Num(num),
					}),
					NodeTy::Defined(ident) => stack.push_back(Expr {
						span: node.span,
						ty: ExprTy::Defined { ident },
					}),
				},
				Either::Right(op) => match op.ty {
					OpTy::Neg(has_operand) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};

						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Neg,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Flip(has_operand) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};

						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Flip,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Not(has_operand) => {
						let expr = if has_operand {
							Some(pop_back(&mut stack))
						} else {
							None
						};
						let span = if let Some(ref expr) = expr {
							Span::new(op.span.start, expr.span.end)
						} else {
							op.span
						};

						stack.push_back(Expr {
							span,
							ty: ExprTy::Prefix {
								op: PreOp {
									span: op.span,
									ty: PreOpTy::Not,
								},
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Paren(has_inner, _l_paren, _end) => {
						let expr = if has_inner {
							Some(pop_back(&mut stack))
						} else {
							None
						};

						stack.push_back(Expr {
							span: op.span,
							ty: ExprTy::Parens {
								expr: expr.map(|e| Box::from(e)),
							},
						});
					}
					OpTy::Add(has_rhs)
					| OpTy::Sub(has_rhs)
					| OpTy::Mul(has_rhs)
					| OpTy::Div(has_rhs)
					| OpTy::Rem(has_rhs)
					| OpTy::And(has_rhs)
					| OpTy::Or(has_rhs)
					| OpTy::Xor(has_rhs)
					| OpTy::LShift(has_rhs)
					| OpTy::RShift(has_rhs)
					| OpTy::EqEq(has_rhs)
					| OpTy::NotEq(has_rhs)
					| OpTy::Gt(has_rhs)
					| OpTy::Lt(has_rhs)
					| OpTy::Ge(has_rhs)
					| OpTy::Le(has_rhs)
					| OpTy::AndAnd(has_rhs)
					| OpTy::OrOr(has_rhs) => {
						let last = pop_back(&mut stack);
						let (left, right) = if has_rhs {
							(pop_back(&mut stack), Some(last))
						} else {
							(last, None)
						};

						let span = if let Some(ref right) = right {
							Span::new(left.span.start, right.span.end)
						} else {
							Span::new(left.span.start, op.span.end)
						};
						let bin_op = op.to_bin_op();

						stack.push_back(Expr {
							ty: ExprTy::Binary {
								left: Box::from(left),
								op: bin_op,
								right: right.map(|e| Box::from(e)),
							},
							span,
						});
					}
					_ => {
						unreachable!("Invalid operator {op:?} in conditional expression shunting yard stack. This operator should never be present in the final RPN stack.");
					}
				},
			}
		}

		if stack.len() != 1 {
			unreachable!("After processing the conditional expression shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap())
	}
}

#[cfg(test)]
mod tests {
	//! Behaviour tests for the conditional expression parser, and also of the conditional expression lexer since
	//! that is a prerequisite.

	use crate::{
		diag::{ExprDiag, Syntax},
		lexer::{NumType, OpTy, Token},
		parser::{
			ast::{conditional::*, Ident},
			Macro,
		},
		span,
	};
	use std::collections::HashMap;

	/// Asserts that the given source string produces the specified expression.
	macro_rules! assert_expr {
		($macros:expr, $src:expr, $result:expr) => {
			let mut lexer = crate::lexer::Lexer::<crate::lexer::Utf16>::new(
				$src,
				crate::SpanEncoding::Utf16,
			);
			let tokens =
				crate::lexer::preprocessor::parse_condition_tokens(&mut lexer);
			assert_eq!(
				super::cond_parser(
					tokens,
					&$macros,
					crate::SpanEncoding::Utf16
				)
				.0
				.unwrap(),
				$result
			);
		};
		($src:expr, $result:expr) => {
			let mut lexer = crate::lexer::Lexer::<crate::lexer::Utf16>::new(
				$src,
				crate::SpanEncoding::Utf16,
			);
			let tokens =
				crate::lexer::preprocessor::parse_condition_tokens(&mut lexer);
			let macros = std::collections::HashMap::new();
			assert_eq!(
				super::cond_parser(tokens, &macros, crate::SpanEncoding::Utf16)
					.0
					.unwrap(),
				$result
			);
		};
	}

	/// Asserts that the given source string produces the specified expression and syntax error(s).
	macro_rules! assert_expr_err {
		($macros:expr, $src:expr, $result:expr, $($error:expr),+) => {
			let mut lexer = crate::lexer::Lexer::<crate::lexer::Utf16>::new($src, crate::SpanEncoding::Utf16);
			let tokens =
				crate::lexer::preprocessor::parse_condition_tokens(&mut lexer);
			let (expr, syntax, _) = super::cond_parser(tokens, &$macros, crate::SpanEncoding::Utf16);
			assert_eq!(expr.unwrap(), $result);
			assert_eq!(
				syntax,
				vec![
					$($error),*
				]
			);
		};
		($src:expr, $result:expr, $($error:expr),+) => {
			let mut lexer = crate::lexer::Lexer::<crate::lexer::Utf16>::new($src, crate::SpanEncoding::Utf16);
			let tokens =
				crate::lexer::preprocessor::parse_condition_tokens(&mut lexer);
			let macros = std::collections::HashMap::new();
			let (expr, syntax, _) = super::cond_parser(tokens, &macros, crate::SpanEncoding::Utf16);
			assert_eq!(expr.unwrap(), $result);
			assert_eq!(
				syntax,
				vec![
					$($error),*
				]
			);
		};
	}

	/// Asserts that the given source string produces no expression and the specified syntax error(s).
	macro_rules! assert_err {
		($src:expr, $($error:expr),+) => {
			let mut lexer = crate::lexer::Lexer::<crate::lexer::Utf16>::new($src, crate::SpanEncoding::Utf16);
			let tokens =
				crate::lexer::preprocessor::parse_condition_tokens(&mut lexer);
			let macros = std::collections::HashMap::new();
			let (expr, syntax, _) = super::cond_parser(tokens, &macros, crate::SpanEncoding::Utf16);
			assert_eq!(expr, None);
			assert_eq!(
				syntax,
				vec![
					$($error),*
				]
			);
		};
	}

	#[test]
	fn single_value() {
		assert_expr!(
			"0",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 1),
			}
		);
		assert_expr!(
			"1",
			Expr {
				ty: ExprTy::Num(1),
				span: span(0, 1),
			}
		);
		assert_expr!(
			"50",
			Expr {
				ty: ExprTy::Num(50),
				span: span(0, 2),
			}
		);
		assert_expr!(
			"undefined",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 9),
			}
		);
		assert_expr!(
			"foo_bar_11245_",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 14),
			}
		);
		assert_expr_err!(
			"50 0",
			Expr {
				ty: ExprTy::Num(50),
				span: span(0, 2),
			},
			Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
				span(0, 2),
				span(3, 4),
			))
		);
		assert_expr_err!(
			"50 foo",
			Expr {
				ty: ExprTy::Num(50),
				span: span(0, 2),
			},
			Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
				span(0, 2),
				span(3, 6),
			))
		);
	}

	#[test]
	fn pre() {
		assert_expr!(
			"-100",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Neg,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Num(100),
						span: span(1, 4),
					})),
				},
				span: span(0, 4),
			}
		);
		assert_expr!(
			"~1",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Flip,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Num(1),
						span: span(1, 2),
					})),
				},
				span: span(0, 2),
			}
		);
		assert_expr!(
			"!90",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Not,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Num(90),
						span: span(1, 3),
					})),
				},
				span: span(0, 3),
			}
		);
		assert_expr!(
			"-undefined",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Neg,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Num(0),
						span: span(1, 10),
					})),
				},
				span: span(0, 10),
			}
		);
		assert_expr!(
			"--3",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Neg,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Prefix {
							op: PreOp {
								ty: PreOpTy::Neg,
								span: span(1, 2),
							},
							expr: Some(Box::from(Expr {
								ty: ExprTy::Num(3),
								span: span(2, 3),
							})),
						},
						span: span(1, 3),
					})),
				},
				span: span(0, 3),
			}
		);
		assert_expr!(
			"!-3",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Not,
						span: span(0, 1)
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Prefix {
							op: PreOp {
								ty: PreOpTy::Neg,
								span: span(1, 2),
							},
							expr: Some(Box::from(Expr {
								ty: ExprTy::Num(3),
								span: span(2, 3),
							})),
						},
						span: span(1, 3),
					})),
				},
				span: span(0, 3),
			}
		);
		assert_expr_err!(
			"5!",
			Expr {
				ty: ExprTy::Num(5),
				span: span(0, 1),
			},
			Syntax::Expr(ExprDiag::InvalidBinOrPostOperator(span(1, 2)))
		);
		assert_expr_err!(
			"5~",
			Expr {
				ty: ExprTy::Num(5),
				span: span(0, 1),
			},
			Syntax::Expr(ExprDiag::InvalidBinOrPostOperator(span(1, 2)))
		);
		assert_expr_err!(
			"-- *",
			Expr {
				ty: ExprTy::Prefix {
					op: PreOp {
						ty: PreOpTy::Neg,
						span: span(0, 1),
					},
					expr: Some(Box::from(Expr {
						ty: ExprTy::Prefix {
							op: PreOp {
								ty: PreOpTy::Neg,
								span: span(1, 2),
							},
							expr: None
						},
						span: span(1, 2),
					}))
				},
				span: span(0, 2),
			},
			Syntax::Expr(ExprDiag::InvalidPrefixOperator(span(3, 4)))
		);
	}

	#[test]
	fn defined() {
		assert_expr!(
			"defined bar",
			Expr {
				ty: ExprTy::Defined {
					ident: Ident {
						name: "bar".into(),
						span: span(8, 11),
					},
				},
				span: span(0, 11),
			}
		);
		assert_expr!(
			"defined(foo)",
			Expr {
				ty: ExprTy::Defined {
					ident: Ident {
						name: "foo".into(),
						span: span(8, 11),
					},
				},
				span: span(0, 12),
			}
		);
		assert_expr!(
			"defined ( bar_2 )",
			Expr {
				ty: ExprTy::Defined {
					ident: Ident {
						name: "bar_2".into(),
						span: span(10, 15),
					},
				},
				span: span(0, 17),
			}
		);
		assert_err!(
			"defined",
			Syntax::Expr(ExprDiag::ExpectedIdentOrLParenAfterDefinedOp(span(
				7, 8
			)))
		);
		assert_err!(
			"defined  +",
			Syntax::Expr(ExprDiag::ExpectedIdentOrLParenAfterDefinedOp(span(
				7, 8
			)))
		);
		assert_err!(
			"defined (",
			Syntax::Expr(ExprDiag::ExpectedIdentAfterDefineOpLParen(span(
				9, 10
			)))
		);
		assert_err!(
			"defined ( foo",
			Syntax::Expr(ExprDiag::ExpectedRParenAfterDefineOpIdent(span(
				13, 14
			)))
		);
		assert_err!(
			"defined (   +",
			Syntax::Expr(ExprDiag::ExpectedIdentAfterDefineOpLParen(span(
				9, 10
			)))
		);
	}

	#[test]
	fn binary() {
		assert_expr!(
			"5 + 6",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(5),
						span: span(0, 1),
					}),
					op: BinOp {
						ty: BinOpTy::Add,
						span: span(2, 3),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(6),
						span: span(4, 5),
					})),
				},
				span: span(0, 5),
			}
		);
		assert_expr!(
			"5 - 8",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(5),
						span: span(0, 1),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(2, 3),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(8),
						span: span(4, 5),
					})),
				},
				span: span(0, 5),
			}
		);
		assert_expr!(
			"5 * 1 - 25",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr {
								ty: ExprTy::Num(5),
								span: span(0, 1),
							}),
							op: BinOp {
								ty: BinOpTy::Mul,
								span: span(2, 3),
							},
							right: Some(Box::from(Expr {
								ty: ExprTy::Num(1),
								span: span(4, 5),
							})),
						},
						span: span(0, 5),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(6, 7),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(25),
						span: span(8, 10),
					})),
				},
				span: span(0, 10),
			}
		);
		assert_expr!(
			"16 / 7 - 4 + 3",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr {
								ty: ExprTy::Binary {
									left: Box::from(Expr {
										ty: ExprTy::Num(16),
										span: span(0, 2),
									}),
									op: BinOp {
										ty: BinOpTy::Div,
										span: span(3, 4),
									},
									right: Some(Box::from(Expr {
										ty: ExprTy::Num(7),
										span: span(5, 6),
									})),
								},
								span: span(0, 6),
							}),
							op: BinOp {
								ty: BinOpTy::Sub,
								span: span(7, 8),
							},
							right: Some(Box::from(Expr {
								ty: ExprTy::Num(4),
								span: span(9, 10),
							})),
						},
						span: span(0, 10),
					}),
					op: BinOp {
						ty: BinOpTy::Add,
						span: span(11, 12),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(3),
						span: span(13, 14),
					})),
				},
				span: span(0, 14),
			}
		);
		assert_expr!(
			"0 - !1",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(0),
						span: span(0, 1),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(2, 3),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Prefix {
							op: PreOp {
								ty: PreOpTy::Not,
								span: span(4, 5),
							},
							expr: Some(Box::from(Expr {
								ty: ExprTy::Num(1),
								span: span(5, 6),
							}))
						},
						span: span(4, 6),
					}))
				},
				span: span(0, 6),
			}
		);
		assert_expr_err!(
			"0 - 5 ! 4",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(0),
						span: span(0, 1),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(2, 3),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(5),
						span: span(4, 5),
					}))
				},
				span: span(0, 5),
			},
			Syntax::Expr(ExprDiag::InvalidBinOrPostOperator(span(6, 7)))
		);
		assert_expr_err!(
			"0 - * 5",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(0),
						span: span(0, 1),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(2, 3),
					},
					right: None,
				},
				span: span(0, 3),
			},
			Syntax::Expr(ExprDiag::InvalidPrefixOperator(span(4, 5)))
		);
	}

	#[test]
	fn undefined_object_macro() {
		assert_expr!(
			"FOO",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 3),
			}
		);
		assert_expr!(
			"FOO_BAR_22",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 10),
			}
		);
		assert_expr_err!(
			"FOO BAR",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 3),
			},
			Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
				span(0, 3),
				span(4, 7)
			))
		);
	}

	#[test]
	fn object_macro_expansion() {
		let mut macros = HashMap::new();
		// #define FOO 2
		macros.insert(
			"FOO".to_owned(),
			(
				span(0, 0),
				Macro::Object(vec![(
					Token::Num {
						type_: NumType::Dec,
						num: "2".into(),
						suffix: None,
					},
					span(0, 1),
				)]),
			),
		);
		assert_expr!(
			macros,
			"FOO",
			Expr {
				ty: ExprTy::Num(2),
				span: span(0, 3),
			}
		);

		let mut macros = HashMap::new();
		// #define FOO 50 - 5
		macros.insert(
			"FOO".to_owned(),
			(
				span(0, 0),
				Macro::Object(vec![
					(
						Token::Num {
							type_: NumType::Dec,
							num: "50".into(),
							suffix: None,
						},
						span(0, 2),
					),
					(Token::Op(OpTy::Sub), span(3, 4)),
					(
						Token::Num {
							type_: NumType::Dec,
							num: "5".into(),
							suffix: None,
						},
						span(5, 6),
					),
				]),
			),
		);
		assert_expr!(
			macros,
			"FOO",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(50),
						span: span(0, 3),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(0, 3),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(5),
						span: span(0, 3),
					})),
				},
				span: span(0, 3),
			}
		);
	}

	#[test]
	fn undefined_function_macro() {
		assert_expr_err!(
			"FOO()",
			Expr {
				ty: ExprTy::Num(0),
				span: span(0, 3)
			},
			Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
				span(0, 3),
				span(3, 4)
			))
		);
	}

	#[test]
	fn function_macro_expansion() {
		let mut macros = HashMap::new();
		// #define FOO() 2
		macros.insert(
			"FOO".to_owned(),
			(
				span(0, 0),
				Macro::Function {
					params: vec![],
					body: vec![(
						Token::Num {
							type_: NumType::Dec,
							num: "2".into(),
							suffix: None,
						},
						span(0, 1),
					)],
				},
			),
		);
		assert_expr!(
			macros,
			"FOO()",
			Expr {
				ty: ExprTy::Num(2),
				span: span(0, 5),
			}
		);

		let mut macros = HashMap::new();
		// #define FOO(A) A - 2
		macros.insert(
			"FOO".to_owned(),
			(
				span(0, 0),
				Macro::Function {
					params: vec![Ident {
						name: "A".into(),
						span: span(0, 1),
					}],
					body: vec![
						(Token::Ident("A".into()), span(0, 1)),
						(Token::Op(OpTy::Sub), span(2, 3)),
						(
							Token::Num {
								type_: NumType::Dec,
								num: "2".into(),
								suffix: None,
							},
							span(4, 5),
						),
					],
				},
			),
		);
		assert_expr!(
			macros,
			"FOO(3)",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(3),
						span: span(0, 6),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(0, 6),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(2),
						span: span(0, 6),
					})),
				},
				span: span(0, 6),
			}
		);

		let mut macros = HashMap::new();
		// #define FOO(A) A - 2
		macros.insert(
			"FOO".to_owned(),
			(
				span(0, 0),
				Macro::Function {
					params: vec![Ident {
						name: "A".into(),
						span: span(0, 1),
					}],
					body: vec![
						(Token::Ident("A".into()), span(0, 1)),
						(Token::Op(OpTy::Sub), span(2, 3)),
						(
							Token::Num {
								type_: NumType::Dec,
								num: "2".into(),
								suffix: None,
							},
							span(4, 5),
						),
					],
				},
			),
		);
		// #define BAR(B) B
		macros.insert(
			"BAR".to_owned(),
			(
				span(0, 0),
				Macro::Function {
					params: vec![Ident {
						name: "b".into(),
						span: span(0, 1),
					}],
					body: vec![(Token::Ident("B".into()), span(0, 1))],
				},
			),
		);
		assert_expr_err!(
			macros,
			"FOO(3) BAR(2)",
			Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr {
						ty: ExprTy::Num(3),
						span: span(0, 6),
					}),
					op: BinOp {
						ty: BinOpTy::Sub,
						span: span(0, 6),
					},
					right: Some(Box::from(Expr {
						ty: ExprTy::Num(2),
						span: span(0, 6),
					})),
				},
				span: span(0, 6),
			},
			Syntax::Expr(ExprDiag::FoundOperandAfterOperand(
				span(0, 6),
				span(7, 13)
			))
		);
	}
}
