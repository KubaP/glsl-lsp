//! Types and functionality related to the Token Stream.
//!
//! This module contains the structs and enums used to represent tokens, and the [`parse_from_str()`] function
//! which returns a [`TokenStream`]. The [`preprocessor`] submodule contains things related to the preprocessor.
//!
//! # Differences in behaviour
//! Since this crate is part of a larger language extension effort, it is designed to handle syntax errors in a UX
//! friendly manner. This means that there are some minor differences between the behaviour of this lexer and of a
//! lexer as specified by the official GLSL specification. The differences are listed below:
//!
//! - When the lexer comes across a character which is not part of the allowed character set it emits the
//!   [`Invalid`](Token::Invalid) token. The only exception is in preprocessor directives where any characters are
//!   allowed, but after preprocessor expansion only the allowed characters can remain. The specification says that
//!   upon such a case a compile-time error must be produced.
//! - When the lexer comes across a block comment which does not have a delimiter (and therefore goes to the
//!   end-of-file) it still produces a [`BlockComment`](Token::BlockComment) token with the `contains_eof` field
//!   set to `true`. The specification does not mention what should technically happen in such a case, but
//!   compilers seem to produce a compile-time error.
//! - The lexer treats any number that matches the following pattern `0[0-9]+` as an octal number. The
//!   specification says that an octal number can only contain digits `[0-7]`.
//! - The lexer treats any identifier immediately after a number (without separating whitespace) as a valid suffix.
//!   The specification only defines the `u|U` suffix as valid for integers, and the `f|F` & `lf|LF` suffix as
//!   valid for floating point numbers. Anything afterwards should be treated as a new token, so this would be
//!   valid: `#define TEST +5 \n uint i = 5uTEST`. Currently, this crate doesn't work according to this behaviour,
//!   hence for now the lexer will treat the suffix as `uTEST` instead.
//!
//! To be certain that the source is valid, these cases (apart from the define issue) must be checked afterwards by
//! iterating over the [`TokenStream`]. The parsing functions provided in the `ast`/`cst` modules do this for you,
//! but if you are performing your own manipulation you must perform these checks yourself.
//!
//! A potential idea for consideration would be to include the official-spec behaviour behind a flag (i.e. stop
//! parsing after encountering an error). This is currently not a priority, but if you would like such
//! functionality please file an issue on the github repository to show interest. An alternative would be to
//! produce a flag along with the `TokenStream` which signifies whether any errors were encountered.
//!
//! For a BNF notation of the official lexer grammar, see
//! [this](https://github.com/KubaP/glsl-lsp/blob/release/glast/docs/lexer_grammar.bnf) file.

pub mod preprocessor;

use crate::{
	cst::{Expr, Layout, LayoutTy},
	span::{Span, Spanned},
	Either,
};

/// A vector of tokens representing a GLSL source string.
pub type TokenStream = Vec<Spanned<Token>>;

/// Parses a GLSL source string into a Token Stream.
///
/// This lexer uses the "Maximal munch" principle to greedily create tokens. This means the longest possible valid
/// token is always produced. Some examples:
///
/// ```text
/// i---7      becomes (i) (--) (-) (7)
/// i----7     becomes (i) (--) (--) (7)
/// i-----7    becomes (i) (--) (--) (-) (7)
/// i-- - --7  becomes (i) (--) (-) (--) (7)
/// ```
/// The longest possible tokens are produced even if they form an invalid expression, for example, `i----7`
/// could've been a valid GLSL expression if it was parsed as `(i) (--) (-) (-) (7)` but this behaviour is not
/// exhibited.
///
/// # Examples
/// Parse a simple GLSL expression:
/// ```rust
/// # use glast::token::parse_from_str;
/// let src = r#"
/// int i = 5.0 + 1;
/// "#;
/// let token_stream = parse_from_str(&src);
/// ```
pub fn parse_from_str(source: &str) -> TokenStream {
	let mut lexer = Lexer::new(source);
	parse_tokens(&mut lexer, false)
}

/// Parses GLSL tokens, continuing off from the current position of the lexer.
///
/// - `parsing_define_body` - Whether we are parsing the body of a `#define` preprocessor directive, which slightly
///   changes the behaviour of the lexer.
///
/// TODO: Track spans of line-continuators.
fn parse_tokens(lexer: &mut Lexer, parsing_define_body: bool) -> TokenStream {
	let mut tokens = Vec::new();

	// This is a flag as to whether we can start parsing a directive if we encounter a `#` symbol.
	// After an EOL or end of block comment this is set to `true`. Any branch other than the whitespace branch sets
	// this to `false`. This makes it easy to keep track of when we are allowed to parse a directive, since they
	// must exist at the start of a line barring any whitespace.
	let mut can_start_directive = true;

	// Any time we want to test the next character, we first `peek()` to see what it is. If it is valid in whatever
	// branch we are in, we can `advance()` the lexer to the next character and repeat the process. If it is
	// invalid (and hence we want to finish this branch and try another one), we don't `advance()` the lexer
	// because we don't want to consume this character; we want to test it against the other branches.
	//
	// Any time we reach a EOL, we don't bother checking what type it is. If it's \n then any check consumes it and
	// the next iteration of the loop starts a new token. If it's \r\n then the next iteration will consume the \n,
	// after which we do _another_ iteration to start a new token.
	let mut buffer = String::new();
	'outer: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => {
				break;
			}
		};

		if parsing_define_body && (current == '\r' || current == '\n') {
			// We are parsing the body of a `#define` macro. And EOL signifies the end of the body, and a return to
			// the normal lexer behaviour.
			return tokens;
		}

		if is_word_start(&current) {
			can_start_directive = false;
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							match_word(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'word;
					}
				};

				// Check if it can be part of a word.
				if is_word(&current) {
					// The character can be part of an word, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of an word, so we can produce a token and exit this loop without
					// consuming it.
					tokens.push((
						match_word(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					break 'word;
				}
			}
		} else if is_number_start(&current) {
			/// The current state when parsing a number.
			#[derive(Debug, Clone, Copy, PartialEq, Eq)]
			enum NumState {
				/// Parsing either an octal or decimal or a floating point number (depending on what follows).
				Zero,
				/// Parsing a hexadecimal number.
				Hex,
				/// Parsing a decimal number.
				Dec,
				/// Parsing a decimal floating point number.
				Float,
			}

			can_start_directive = false;

			// We don't need to worry about having a word character before this first digit character because if
			// there was a word character before, this digit character would be getting parsed as part of the
			// word in the first place, so this branch would not be executing.

			let mut num_buffer = String::new();
			let mut suffix_buffer = None;

			// If we begin with [1-9], we know it's 100% a decimal number. If we begin with `0x`, we know it's 100%
			// a hexadecimal number and we can ignore this prefix as it's not part of the number itself.
			//
			// If we begin with a `0`, however, this can either be:
			// - an octal number (and we need to ignore this prefix later down the line) or,
			// - a decimal number `0` assuming the number ends at the next character or,
			// - it's a floating point which can have a variable amount of `0`s before the decimal point.
			//
			// If we begin with a `.`, we 100% know it's a floating point if there's at least one [0-9] digit
			// afterwards, otherwise this is just a dot token.
			let mut state = if lexer.take_pat("0x") {
				NumState::Hex
			} else if lexer.take_pat("0X") {
				NumState::Hex
			} else if current == '0' {
				// We have a `0`, so either an octal number or a decimal `0` or a floating point.
				num_buffer.push(current);
				lexer.advance();
				NumState::Zero
			} else if current == '.' {
				if let Some(lookahead) = lexer.lookahead_1() {
					if lookahead.is_ascii_digit() {
						// We have a `.` followed by a character that is a floating point digit.
						num_buffer.push(current);
						lexer.advance();
						NumState::Float
					} else {
						// We have a `.` followed by a character that is not a digit, so this must be a punctuation
						// token. We consume the character because otherwise we'd end up back in this branch again.
						lexer.advance();
						tokens.push((
							Token::Dot,
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						continue;
					}
				} else {
					// We have a `.` followed by the end of the source string, so this must be a punctuation token.
					// We consume the character because otherwise we'd end up back in this branch again.
					lexer.advance();
					tokens.push((
						Token::Dot,
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					continue;
				}
			} else {
				// We have a [1-9] digit, so a decimal number.
				num_buffer.push(current);
				lexer.advance();
				NumState::Dec
			};

			'number: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the number.
						let type_ = match state {
							NumState::Hex => NumType::Hex,
							NumState::Zero => {
								if num_buffer.as_str() == "0" {
									NumType::Dec
								} else {
									num_buffer.remove(0);
									NumType::Oct
								}
							}
							NumState::Dec => NumType::Dec,
							NumState::Float => NumType::Float,
						};
						tokens.push((
							Token::Num {
								num: num_buffer,
								suffix: suffix_buffer,
								type_,
							},
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'number;
					}
				};

				if current == '.' && state == NumState::Hex {
					// If we encounter a `.` and we are parsing a hexadecimal number, that means we've reached the
					// end of this number, and the `.` is a punctuation symbol. We consume the character because
					// otherwise we'd end up back in this branch again.
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_: NumType::Hex,
						},
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
					));
					lexer.advance();
					break 'number;
				}
				if current == '.' && suffix_buffer.is_some() {
					// If we have finished parsing the digits and are now parsing the suffix, that means we've
					// reached the end of the number and this `.` is a punctuation symbol. We consume the character
					// because otherwise we'd end up back in this branch again.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
					));
					lexer.advance();
					break 'number;
				}
				if current == '.'
					&& (state == NumState::Dec || state == NumState::Zero)
				{
					// If we are still parsing the digits of a number beginning with [0-9] and haven't reached a
					// suffix yet, and haven't encountered a `.` yet either, that means this number is a floating
					// point.
					state = NumState::Float;
					num_buffer.push(current);
					lexer.advance();
					continue 'number;
				}
				if current == '.' && state == NumState::Float {
					// If we are still parsing the digits and haven't reached a suffix yet, and have already
					// encountered a `.` before, that means we've reached the end of the number and this `.` is a
					// punctuation symbol. We consume the character because otherwise we'd end up back in this
					// branch again.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
					));
					lexer.advance();
					break 'number;
				}

				if current == 'e' {
					// Note: In the case we encounter an `e` followed by nothing after, that can only be a suffix,
					// so the logic below will deal with that.
					if let Some(lookahead) = lexer.lookahead_1() {
						if lookahead.is_ascii_digit() {
							// We have an `e` followed by a digit, so this is an exponent notation rather than a
							// suffix.
							num_buffer.push(current);
							lexer.advance();
							// If the number isn't already a float, then an exponent makes it one.
							state = NumState::Float;
							continue 'number;
						} else if lookahead == '+' || lookahead == '-' {
							//  We have an `e` followed by a `+`/`-`, so this _may_ be an exponent notation depending
							//  on whether a digit follows.
							if let Some(lookahead_2) = lexer.lookahead_2() {
								if lookahead_2.is_ascii_digit() {
									// We have an `e+`/`e-` followed by a digit, so this is an exponent notation rather
									// than a suffix.
									num_buffer.push(current);
									num_buffer.push(lookahead);
									lexer.advance();
									lexer.advance();
									// If the number isn't already a float, then an exponent makes it one.
									state = NumState::Float;
									continue 'number;
								} else {
									// We have an `e` followed by a `+`/`-` and something that's not a digit after, so
									// this becomes a suffix.
									lexer.advance();
									suffix_buffer = Some(String::from(current));
									let type_ = match state {
										NumState::Hex => NumType::Hex,
										NumState::Zero => {
											if num_buffer.as_str() == "0" {
												NumType::Dec
											} else {
												num_buffer.remove(0);
												NumType::Oct
											}
										}
										NumState::Dec => NumType::Dec,
										NumState::Float => NumType::Float,
									};
									tokens.push((
										Token::Num {
											num: num_buffer,
											suffix: suffix_buffer,
											type_,
										},
										Span {
											start: buffer_start,
											end: lexer.position(),
										},
									));
									break 'number;
								}
							} else {
								// We have an `e` followed by a `+`/`-` and nothing after, so this becomes a suffix.
								suffix_buffer = Some(String::from(current));
								lexer.advance();
								let type_ = match state {
									NumState::Hex => NumType::Hex,
									NumState::Zero => {
										if num_buffer.as_str() == "0" {
											NumType::Dec
										} else {
											num_buffer.remove(0);
											NumType::Oct
										}
									}
									NumState::Dec => NumType::Dec,
									NumState::Float => NumType::Float,
								};
								tokens.push((
									Token::Num {
										num: num_buffer,
										suffix: suffix_buffer,
										type_,
									},
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
								));
								break 'number;
							}
						}
					}
				}

				// We want to check for any word characters (and digits of course). This is to follow the spec.
				//
				// Something like `51ufoo` should be parsed as a decimal integer `51` with an invalid postfix
				// `ufoo`, hence why we must be greedy and pick up _any_ word characters.
				if current.is_ascii_hexdigit() || is_word(&current) {
					match state {
						NumState::Zero | NumState::Dec | NumState::Float => {
							if !current.is_ascii_digit()
								&& suffix_buffer.is_none()
							{
								// We have reached the beginning of a word, so flag that we are now parsing the
								// suffix.
								suffix_buffer = Some(String::new());
							}
						}
						NumState::Hex => {
							if !current.is_ascii_hexdigit()
								&& suffix_buffer.is_none()
							{
								// We have reached the beginning of a word, so flag that we are now parsing the
								// suffix.
								suffix_buffer = Some(String::new());
							}
						}
					}

					// Append the character to the appropriate buffer.
					if let Some(suffix) = &mut suffix_buffer {
						suffix.push(current);
					} else {
						num_buffer.push(current);
					}

					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					break 'number;
				}
			}
		} else if is_punctuation_start(&current) {
			can_start_directive = false;

			if lexer.take_pat("//") {
				// If we have a `//`, that means this is a comment until the EOL.
				'line_comment: loop {
					// Peek the current character.
					current = match lexer.peek() {
						Some(c) => c,
						None => {
							// We have reached the end of the source string, and therefore the end of the comment.
							tokens.push((
								Token::LineComment(std::mem::take(&mut buffer)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
							));
							break 'line_comment;
						}
					};

					if current == '\r' || current == '\n' {
						// We have an EOL without a line-continuator, so therefore this is the end of the directive.
						tokens.push((
							Token::LineComment(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'line_comment;
					} else {
						// Any other character is just added to the comment buffer.
						buffer.push(current);
						lexer.advance();
					}
				}
			} else if lexer.take_pat("/*") {
				// If we have a `/*`, that means this is a comment until the first `*/`
				'comment: loop {
					// Test if the end delimiter is here.
					if lexer.take_pat("*/") {
						tokens.push((
							Token::BlockComment {
								str: std::mem::take(&mut buffer),
								contains_eof: false,
							},
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						can_start_directive = true;
						break 'comment;
					}

					// Continue pushing any characters into the buffer.
					if let Some(char) = lexer.next() {
						buffer.push(char);
					} else {
						// We have reached the end of the source string, and therefore the end of the comment. This
						// comment however therefore contains the EOF and hence is not valid.
						tokens.push((
							Token::BlockComment {
								str: std::mem::take(&mut buffer),
								contains_eof: true,
							},
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'comment;
					}
				}
			} else {
				tokens.push((
					match_punctuation(lexer),
					Span {
						start: buffer_start,
						end: lexer.position(),
					},
				));
			}
		} else if current.is_whitespace() {
			// Check for an EOL, to reset the directive parsing flag.
			if current == '\r' || current == '\n' {
				can_start_directive = true;
			}
			// We ignore whitespace characters.
			lexer.advance();
		} else if can_start_directive && current == '#' && !parsing_define_body
		{
			// If we are parsing a directive string, then the only difference in behaviour is that we don't start a
			// new directive within the existing directive. This means the `#` character will be treated as an
			// invalid character instead.
			let directive_start = lexer.position();
			lexer.advance();

			// Consume whitespace since any whitespace between the `#` and `<keyword>` is ignored.
			loop {
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and hence the end of this directive.
						tokens.push((
							Token::Directive(preprocessor::TokenStream::Empty),
							Span {
								start: directive_start,
								end: lexer.position(),
							},
						));
						break 'outer;
					}
				};

				if current == '\r' || current == '\n' {
					// We have an EOL without a line-continuator, which marks the end of this directive.
					tokens.push((
						Token::Directive(preprocessor::TokenStream::Empty),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					));
					continue 'outer;
				}

				if current.is_ascii_whitespace() {
					lexer.advance();
					continue;
				} else {
					break;
				}
			}

			if !is_word_start(&current) {
				// We have a directive which doesn't begin with a word, which is invalid.
				let content_start = lexer.position();
				'content: loop {
					// Peek the current character.
					current = match lexer.peek() {
						Some(c) => c,
						None => {
							tokens.push((
								Token::Directive(
									preprocessor::TokenStream::Invalid {
										content: (
											std::mem::take(&mut buffer),
											Span {
												start: content_start,
												end: lexer.position(),
											},
										),
									},
								),
								Span {
									start: directive_start,
									end: lexer.position(),
								},
							));
							break 'outer;
						}
					};

					if current == '\r' || current == '\n' {
						// We have an EOL without a line-continuator, which marks the end of this directive.
						break 'content;
					} else {
						// Any other character is just added to the content buffer.
						buffer.push(current);
						lexer.advance();
					}
				}

				tokens.push((
					Token::Directive(preprocessor::TokenStream::Invalid {
						content: (
							std::mem::take(&mut buffer),
							Span {
								start: content_start,
								end: lexer.position(),
							},
						),
					}),
					Span {
						start: directive_start,
						end: lexer.position(),
					},
				));
				continue 'outer;
			}

			// Consume the first word, which is the name of the directive.
			let directive_kw_start = lexer.position();
			buffer.push(current);
			lexer.advance();
			'directive_name: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and hence of this directive.
						tokens.push((
							Token::Directive(preprocessor::construct_empty(
								buffer,
								Span {
									start: directive_kw_start,
									end: lexer.position(),
								},
							)),
							Span {
								start: directive_start,
								end: lexer.position(),
							},
						));
						break 'outer;
					}
				};

				// Check if it can be part of a word.
				if is_word(&current) {
					// The character can be part of a word, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else {
					break 'directive_name;
				}
			}

			let directive_kw_span = Span {
				start: directive_kw_start,
				end: lexer.position(),
			};

			// Consume the rest of the directive, and create appropriate tokens depending on the directive keyword.
			match buffer.as_ref() {
				"version" => tokens.push((
					Token::Directive(preprocessor::parse_version(
						lexer,
						directive_kw_span,
					)),
					Span {
						start: directive_start,
						end: lexer.position(),
					},
				)),
				"extension" => tokens.push((
					Token::Directive(preprocessor::parse_extension(
						lexer,
						directive_kw_span,
					)),
					Span {
						start: directive_start,
						end: lexer.position(),
					},
				)),
				"line" => tokens.push((
					Token::Directive(preprocessor::parse_line(
						lexer,
						directive_kw_span,
					)),
					Span {
						start: directive_start,
						end: lexer.position(),
					},
				)),
				"define" => {
					tokens.push((
						Token::Directive(preprocessor::TokenStream::Define {
							kw: directive_kw_span,
							ident_tokens: preprocessor::parse_define(lexer),
							body_tokens: parse_tokens(lexer, true),
						}),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					));
				}
				"undef" => tokens.push((
					Token::Directive(preprocessor::parse_undef(
						lexer,
						directive_kw_span,
					)),
					Span {
						start: directive_start,
						end: lexer.position(),
					},
				)),
				"ifdef" | "ifndef" | "if" | "elif" | "else" | "endif" => tokens
					.push((
						Token::Directive(preprocessor::parse_condition(
							lexer,
							&buffer,
							directive_kw_span,
						)),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					)),
				"error" => {
					buffer.clear();
					let content_start = lexer.position();

					'content: loop {
						// Peek the current character.
						current = match lexer.peek() {
							Some(c) => c,
							None => {
								// We have reached the end of the source string, and therefore the end of this
								// directive.
								break 'content;
							}
						};

						if current == '\r' || current == '\n' {
							// We have an EOL without a line-continuator, which marks the end of this directive.
							break 'content;
						} else {
							// Any other character is just added to the content buffer.
							buffer.push(current);
							lexer.advance();
						}
					}

					tokens.push((
						Token::Directive(preprocessor::TokenStream::Error {
							kw: directive_kw_span,
							message: Some((
								std::mem::take(&mut buffer),
								Span {
									start: content_start,
									end: lexer.position(),
								},
							)),
						}),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					));
				}
				"pragma" => {
					buffer.clear();
					let content_start = lexer.position();

					'content: loop {
						// Peek the current character.
						current = match lexer.peek() {
							Some(c) => c,
							None => {
								// We have reached the end of the source string, and therefore the end of this
								// directive.
								break 'content;
							}
						};

						if current == '\r' || current == '\n' {
							// We have an EOL without a line-continuator, which marks the end of this directive.
							break 'content;
						} else {
							// Any other character is just added to the content buffer.
							buffer.push(current);
							lexer.advance();
						}
					}

					tokens.push((
						Token::Directive(preprocessor::TokenStream::Pragma {
							kw: directive_kw_span,
							options: Some((
								std::mem::take(&mut buffer),
								Span {
									start: content_start,
									end: lexer.position(),
								},
							)),
						}),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					));
				}
				_ => {
					let kw = (std::mem::take(&mut buffer), directive_kw_span);
					let content_start = lexer.position();

					'content: loop {
						// Peek the current character.
						current = match lexer.peek() {
							Some(c) => c,
							None => {
								// We have reached the end of the source string, and therefore the end of this
								// directive.
								break 'content;
							}
						};

						if current == '\r' || current == '\n' {
							// We have an EOL without a line-continuator, which marks the end of this directive.
							break 'content;
						} else {
							// Any other character is just added to the content buffer.
							buffer.push(current);
							lexer.advance();
						}
					}

					tokens.push((
						Token::Directive(preprocessor::TokenStream::Custom {
							kw,
							content: Some((
								std::mem::take(&mut buffer),
								Span {
									start: content_start,
									end: lexer.position(),
								},
							)),
						}),
						Span {
							start: directive_start,
							end: lexer.position(),
						},
					));
				}
			}
			buffer.clear();
		} else if current == '#' && parsing_define_body {
			// Look for a `##` which is valid within the body of a `#define` macro.
			if lexer.take_pat("##") {
				tokens.push((
					Token::MacroConcat,
					Span {
						start: buffer_start,
						end: lexer.position(),
					},
				));
			}
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				Token::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				},
			));
		}
	}

	tokens
}

/// A token representing a unit of text in the GLSL source string.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
	/// A number, e.g. `1`, `517u`, `0xA9C`, `07113`, `7.3e-2`, `.015LF`.
	Num {
		/// The type of number.
		type_: NumType,
		/// The numeric contents, (this excludes any prefixes or suffixes).
		num: String,
		/// An optional suffix after the numeric contents.
		suffix: Option<String>,
	},
	/// A boolean, either `true` or `false`.
	Bool(bool),
	/// An identifier, e.g. `foo_bar`, `_900_a`.
	Ident(String),
	/// A preprocessor directive, e.g. `#version 450 core`, `#define FOO 42`, `#ifdef TOGGLE`.
	Directive(preprocessor::TokenStream),
	/// The `##` punctuation symbol. This token is only emitted when parsing the body of a `#define` preprocessor
	/// directive.
	MacroConcat,
	/// A line comment, e.g. `// comment`.
	LineComment(String),
	/// A block comment, e.g. `/* comment */`.
	BlockComment {
		str: String,
		/// Only `true` if this comment is missing the closing delimiter.
		contains_eof: bool,
	},
	/// An invalid character, e.g. `@`, `"`, `'`.
	Invalid(char),
	/* Keywords */
	/// The `if` keyword.
	If,
	/// The `else` keyword.
	Else,
	/// The `for` keyword.
	For,
	/// The `do` keyword.
	Do,
	/// The `while` keyword.
	While,
	/// The `continue` keyword.
	Continue,
	/// The `switch` keyword.
	Switch,
	/// The `case` keyword.
	Case,
	/// The `default` keyword.
	Default,
	/// The `break` keyword.
	Break,
	/// The `return` keyword.
	Return,
	/// The `discard` keyword.
	Discard,
	/// The `struct` keyword.
	Struct,
	/// The `subroutine` keyword.
	Subroutine,
	/// A reserved keyword, e.g. `class`, `public`, `typedef`, `union`.
	Reserved(String),
	/* Qualifiers */
	/// The `const` keyword.
	Const,
	/// The `in` keyword.
	In,
	/// The `out` keyword.
	Out,
	/// The `inout` keyword.
	InOut,
	/// The `attribute` keyword.
	Attribute,
	/// The `uniform` keyword.
	Uniform,
	/// The `varying` keyword.
	Varying,
	/// The `buffer` keyword.
	Buffer,
	/// The `shared` keyword.
	Shared,
	/// The `centroid` keyword.
	Centroid,
	/// The `sample` keyword.
	Sample,
	/// The `patch` keyword.
	Patch,
	/// The `layout` keyword.
	Layout,
	/// The `flat` keyword.
	Flat,
	/// The `smooth` keyword.
	Smooth,
	/// The `noperspective` keyword.
	NoPerspective,
	/// The `highp` keyword.
	HighP,
	/// The `mediump` keyword.
	MediumP,
	/// The `lowp` keyword.
	LowP,
	/// The `invariant` keyword.
	Invariant,
	/// The `precise` keyword.
	Precise,
	/// The `coherent` keyword.
	Coherent,
	/// The `volatile` keyword.
	Volatile,
	/// The `restrict` keyword.
	Restrict,
	/// The `readonly` keyword.
	Readonly,
	/// The `writeonly` keyword.
	Writeonly,
	/* Punctuation tokens */
	/// A punctuation token.
	Op(OpTy),
	/// A comma `,`.
	Comma,
	/// A dot `.`.
	Dot,
	/// A semi-colon `;`.
	Semi,
	/// A colon `:`.
	Colon,
	/// A question mark `?`.
	Question,
	/// An opening parenthesis `(`.
	LParen,
	/// A closing parenthesis `)`.
	RParen,
	/// An opening bracket `[`.
	LBracket,
	/// A closing bracket `]`.
	RBracket,
	/// An opening brace `{`.
	LBrace,
	/// A closing brace `}`.
	RBrace,
}

/// The type/notation of a number token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumType {
	/// A decimal is any number beginning with `1-9` without a decimal point or an exponent, or just the digit `0` on it's own.
	Dec,
	/// An octal is any number beginning with `0` without a decimal point or an exponent.
	Oct,
	/// A hexadecimal is any number beginning with `0x` without a decimal point or an exponent.
	Hex,
	/// A float is any number that contains a decimal point or an exponent.
	Float,
}

/// A mathematical/comparison operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpTy {
	/* Maths */
	/// The `+` symbol.
	Add,
	/// The `-` symbol.
	Sub,
	/// The `*` symbol.
	Mul,
	/// The `/` symbol.
	Div,
	/// The `%` symbol.
	Rem,
	/// The `&` symbol.
	And,
	/// The `|` symbol.
	Or,
	/// The `^` symbol.
	Xor,
	/// The `<<` symbol.
	LShift,
	/// The `>>` symbol.
	RShift,
	/// The `-` symbol.
	Flip,
	/// The `=` symbol.
	Eq,
	/// The `++` symbol.
	AddAdd,
	/// The `--` symbol.
	SubSub,
	/// The `+=` symbol.
	AddEq,
	/// The `-=` symbol.
	SubEq,
	/// The `*=` symbol.
	MulEq,
	/// The `/=` symbol.
	DivEq,
	/// The `%=` symbol.
	RemEq,
	/// The `&=` symbol.
	AndEq,
	/// The `|=` symbol.
	OrEq,
	/// The `^=` symbol.
	XorEq,
	/// The `<<=` symbol.
	LShiftEq,
	/// The `>>=` symbol.
	RShiftEq,
	/* Comparison */
	/// The `==` symbol.
	EqEq,
	/// The `!=` symbol.
	NotEq,
	/// The `!` symbol.
	Not,
	/// The `>` symbol.
	Gt,
	/// The `<` symbol.
	Lt,
	/// The `>=` symbol.
	Ge,
	/// The `<=` symbol.
	Le,
	/// The `&&` symbol.
	AndAnd,
	/// The `||` symbol.
	OrOr,
	/// The `^^` symbol.
	XorXor,
}

impl Token {
	/// Returns whether the current token is a keyword that can start a statement.
	pub fn starts_statement(&self) -> bool {
		match self {
			Self::If
			| Self::Else
			| Self::For
			| Self::Do
			| Self::While
			| Self::Continue
			| Self::Switch
			| Self::Case
			| Self::Default
			| Self::Break
			| Self::Return
			| Self::Discard
			| Self::Struct
			| Self::Subroutine
			| Self::Reserved(_)
			| Self::Const
			| Self::In
			| Self::Out
			| Self::InOut
			| Self::Attribute
			| Self::Uniform
			| Self::Varying
			| Self::Buffer
			| Self::Shared
			| Self::Centroid
			| Self::Sample
			| Self::Patch
			| Self::Layout
			| Self::Flat
			| Self::Smooth
			| Self::NoPerspective
			| Self::HighP
			| Self::MediumP
			| Self::LowP
			| Self::Invariant
			| Self::Precise
			| Self::Coherent
			| Self::Volatile
			| Self::Restrict
			| Self::Readonly
			| Self::Writeonly => true,
			_ => false,
		}
	}

	/// Returns whether the current token is a punctuation assuming we are at the beginning of parsing a statement.
	pub fn is_punctuation_for_stmt(&self) -> bool {
		match self {
			Self::Op(_)
			| Self::Comma
			| Self::Dot
			| Self::Colon
			| Self::Question
			| Self::LParen
			| Self::RParen
			| Self::LBracket
			| Self::RBracket => true,
			_ => false,
		}
	}

	/// Tries to convert the current token into a [`LayoutTy`] identifier.
	///
	/// If the token matches a layout identifier that doesn't take an expression, e.g. `early_fragment_tests`, then
	/// `Left` is returned with the converted `LayoutTy`. If the token matches a layout identifier that takes an
	/// expression, e.g. `location = n`, then `Right` is returned; after the expression has been parsed, call
	/// [`to_layout_expr()`](Self::to_layout_expr).
	///
	/// If `None` is returned, the current token is not a valid layout identifier.
	pub fn to_layout(&self) -> Option<Either<LayoutTy, ()>> {
		match self {
			// `shared` is a keyword in all circumstances, apart from when it is used as a qualifier, hence it's a
			// distinct variant rather than a string.
			Self::Shared => Some(Either::Left(LayoutTy::Shared)),
			Self::Ident(s) => match s.as_ref() {
				"packed" => Some(Either::Left(LayoutTy::Packed)),
				"std140" => Some(Either::Left(LayoutTy::Std140)),
				"std430" => Some(Either::Left(LayoutTy::Std430)),
				"row_major" => Some(Either::Left(LayoutTy::RowMajor)),
				"column_major" => Some(Either::Left(LayoutTy::ColumnMajor)),
				"binding" => Some(Either::Right(())),
				"offset" => Some(Either::Right(())),
				"align" => Some(Either::Right(())),
				"location" => Some(Either::Right(())),
				"component" => Some(Either::Right(())),
				"index" => Some(Either::Right(())),
				"points" => Some(Either::Left(LayoutTy::Points)),
				"lines" => Some(Either::Left(LayoutTy::Lines)),
				"isolines" => Some(Either::Left(LayoutTy::Isolines)),
				"triangles" => Some(Either::Left(LayoutTy::Triangles)),
				"quads" => Some(Either::Left(LayoutTy::Quads)),
				"equal_spacing" => Some(Either::Left(LayoutTy::EqualSpacing)),
				"fractional_even_spacing" => {
					Some(Either::Left(LayoutTy::FractionalEvenSpacing))
				}
				"fractional_odd_spacing" => {
					Some(Either::Left(LayoutTy::FractionalOddSpacing))
				}
				"cw" => Some(Either::Left(LayoutTy::Clockwise)),
				"ccw" => Some(Either::Left(LayoutTy::CounterClockwise)),
				"point_mode" => Some(Either::Left(LayoutTy::PointMode)),
				"line_adjacency" => {
					Some(Either::Left(LayoutTy::LinesAdjacency))
				}
				"triangle_adjacency" => {
					Some(Either::Left(LayoutTy::TrianglesAdjacency))
				}
				"invocations" => Some(Either::Right(())),
				"origin_upper_left" => {
					Some(Either::Left(LayoutTy::OriginUpperLeft))
				}
				"pixel_center_integer" => {
					Some(Either::Left(LayoutTy::PixelCenterInteger))
				}
				"early_fragment_tests" => {
					Some(Either::Left(LayoutTy::EarlyFragmentTests))
				}
				"local_size_x" => Some(Either::Right(())),
				"local_size_y" => Some(Either::Right(())),
				"local_size_z" => Some(Either::Right(())),
				"xfb_buffer" => Some(Either::Right(())),
				"xfb_stride" => Some(Either::Right(())),
				"xfb_offset" => Some(Either::Right(())),
				"vertices" => Some(Either::Right(())),
				"line_strip" => Some(Either::Left(LayoutTy::LineStrip)),
				"triangle_strip" => Some(Either::Left(LayoutTy::TriangleStrip)),
				"max_vertices" => Some(Either::Right(())),
				"stream" => Some(Either::Right(())),
				"depth_any" => Some(Either::Left(LayoutTy::DepthAny)),
				"depth_greater" => Some(Either::Left(LayoutTy::DepthGreater)),
				"depth_less" => Some(Either::Left(LayoutTy::DepthLess)),
				"depth_unchanged" => {
					Some(Either::Left(LayoutTy::DepthUnchanged))
				}
				_ => None,
			},
			_ => None,
		}
	}

	/// Constructs a [`Layout`] given the identifier, expression and spans.
	///
	/// # Panics
	/// This is only for layout identifiers which take a value expression. See the documentation for
	/// [`to_layout()`](Self::to_layout) for more information.
	#[rustfmt::skip]
	pub fn to_layout_expr(
		&self,
		kw_span: Span,
		eq_span: Option<Span>,
		expr: Option<Expr>,
	) -> Layout {
		// Calculate the span.
		let span = if let Some(expr) = &expr {
			Span::new(kw_span.start, expr.span.end)
		} else if let Some(eq_span) = eq_span {
			Span::new(kw_span.start, eq_span.end)
		} else {
			kw_span
		};

		match self {
			Self::Ident(s) => match s.as_ref() {
				"binding" => Layout {
					span,
					ty: LayoutTy::Binding {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"offset" => Layout {
					span,
					ty: LayoutTy::Offset {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"align" => Layout {
					span,
					ty: LayoutTy::Align {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"location" => Layout {
					span,
					ty: LayoutTy::Location {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"component" => Layout {
					span,
					ty: LayoutTy::Component {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"index" => Layout {
					span,
					ty: LayoutTy::Index {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"invocations" => Layout {
					span,
					ty: LayoutTy::Invocations {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"local_size_x" => Layout{
					span,
					ty: LayoutTy::LocalSizeX {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"local_size_y" => Layout {
					span,
					ty: LayoutTy::LocalSizeY {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"local_size_z" => Layout {
					span,
					ty: LayoutTy::LocalSizeZ {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"xfb_buffer" => Layout {
					span,
					ty: LayoutTy::XfbBuffer {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"xfb_stride" => Layout {
					span,
					ty: LayoutTy::XfbStride {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"xfb_offset" => Layout {
					span,
					ty: LayoutTy::XfbOffset {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"vertices" => Layout {
					span,
					ty: LayoutTy::Vertices {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"max_vertices" => Layout {
					span,
					ty: LayoutTy::MaxVertices {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				"stream" => Layout {
					span,
					ty: LayoutTy::Stream {
						kw: kw_span,
						eq: eq_span,
						value: expr,
					}
				},
				_ => unreachable!("[Token::to_layout_expr] Given a layout `identifier: {s}` that doesn't take an expression value."),
			},
			_ => unreachable!("[Token::to_layout_expr] Given a token which is cannot be a valid layout identifier."),
		}
	}
}

impl std::fmt::Display for Token {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Token::Num { type_, num, suffix } => {
				match type_ {
					NumType::Dec => {}
					NumType::Oct => write!(f, "0")?,
					NumType::Hex => write!(f, "0x")?,
					NumType::Float => {}
				}
				write!(f, "{num}")?;
				if let Some(suffix) = suffix {
					write!(f, "{suffix}")
				} else {
					Ok(())
				}
			}
			Token::Bool(b) => write!(f, "{b}"),
			Token::Ident(s) => write!(f, "{s}"),
			Token::Directive(_) => todo!(),
			Token::MacroConcat => write!(f, "##"),
			Token::LineComment(s) => write!(f, "//{s}"),
			Token::BlockComment { str, contains_eof } => {
				write!(f, "/*{str}")?;
				if *contains_eof {
					write!(f, "*/")
				} else {
					Ok(())
				}
			}
			Token::Invalid(c) => write!(f, "{c}"),
			Token::If => write!(f, "if"),
			Token::Else => write!(f, "else"),
			Token::For => write!(f, "for"),
			Token::Do => write!(f, "do"),
			Token::While => write!(f, "while"),
			Token::Continue => write!(f, "continue"),
			Token::Switch => write!(f, "switch"),
			Token::Case => write!(f, "case"),
			Token::Default => write!(f, "default"),
			Token::Break => write!(f, "break"),
			Token::Return => write!(f, "return"),
			Token::Discard => write!(f, "discard"),
			Token::Struct => write!(f, "struct"),
			Token::Subroutine => write!(f, "subroutine"),
			Token::Reserved(s) => write!(f, "{s}"),
			Token::Const => write!(f, "const"),
			Token::In => write!(f, "in"),
			Token::Out => write!(f, "out"),
			Token::InOut => write!(f, "inout"),
			Token::Attribute => write!(f, "attribute"),
			Token::Uniform => write!(f, "uniform"),
			Token::Varying => write!(f, "varying"),
			Token::Buffer => write!(f, "buffer"),
			Token::Shared => write!(f, "shared"),
			Token::Centroid => write!(f, "centroid"),
			Token::Sample => write!(f, "sample"),
			Token::Patch => write!(f, "patch"),
			Token::Layout => write!(f, "layout"),
			Token::Flat => write!(f, "flat"),
			Token::Smooth => write!(f, "smooth"),
			Token::NoPerspective => write!(f, "noperspective"),
			Token::HighP => write!(f, "highp"),
			Token::MediumP => write!(f, "mediump"),
			Token::LowP => write!(f, "lowp"),
			Token::Invariant => write!(f, "invariant"),
			Token::Precise => write!(f, "precise"),
			Token::Coherent => write!(f, "coherent"),
			Token::Volatile => write!(f, "volatile"),
			Token::Restrict => write!(f, "restrict"),
			Token::Readonly => write!(f, "readonly"),
			Token::Writeonly => write!(f, "writeonly"),
			Token::Op(_) => todo!(),
			Token::Comma => write!(f, ","),
			Token::Dot => write!(f, "."),
			Token::Semi => write!(f, ";"),
			Token::Colon => write!(f, ":"),
			Token::Question => write!(f, "?"),
			Token::LParen => write!(f, "("),
			Token::RParen => write!(f, ")"),
			Token::LBracket => write!(f, "["),
			Token::RBracket => write!(f, "]"),
			Token::LBrace => write!(f, "{{"),
			Token::RBrace => write!(f, "}}"),
		}
	}
}

/// A lexer which allows stepping through a GLSL source string character by character.
///
/// This includes a lot of helper methods to make it easier to match patterns and correctly deal with things such
/// as line-continuators which a naive iteration would mess up.
struct Lexer {
	/// The string stored as a vector of characters.
	chars: Vec<char>,
	/// The index of the current character.
	cursor: usize,
}

impl Lexer {
	/// Constructs a new lexer.
	fn new(source: &str) -> Self {
		let mut lexer = Lexer {
			// Iterating over individual characters is guaranteed to produce correct behaviour because GLSL source
			// strings must use the UTF-8 encoding as per the specification.
			chars: source.chars().collect(),
			cursor: 0,
		};

		// Deal with a line-continuation character if it's the first thing in the source file. If we didn't do
		// this, the first time `peek()` is called in the first iteration of the loop it could return a `\` even
		// though it's a valid line-continuator.
		lexer.cursor = lexer.take_line_continuator(0);

		lexer
	}

	/// Returns the current character under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<char> {
		self.chars.get(self.cursor).map(|c| *c)
	}

	/// Peeks the next character without advancing the cursor; (returns the character under `cursor + 1`, taking
	/// into account a possible line continuator).
	fn lookahead_1(&self) -> Option<char> {
		let pos = self.cursor + 1 + self.take_line_continuator(self.cursor + 1);
		self.chars.get(pos).map(|c| *c)
	}

	/// Peeks the character after the next one without advancing the cursor; (returns the character under `cursor +
	/// 2`, taking into account possible line continuators).
	fn lookahead_2(&self) -> Option<char> {
		let pos = self.cursor + 1 + self.take_line_continuator(self.cursor + 1);
		let pos = pos + 1 + self.take_line_continuator(pos + 1);
		self.chars.get(pos).map(|c| *c)
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		self.cursor += 1;
		self.cursor += self.take_line_continuator(self.cursor);
	}

	/// Returns the current character under the cursor and advances the cursor by one.
	///
	/// This is equivalent to calling [`peek()`](Self::peek()) followed by [`advance()`](Self::advance()).
	fn next(&mut self) -> Option<char> {
		let c = self.peek();
		// If we are successful in getting the character, advance the cursor.
		if c.is_some() {
			self.advance();
		}
		c
	}

	/// Tries to match a pattern starting at the current character under the cursor.
	///
	/// If the match is successful, `true` is returned and the cursor is advanced to consume the pattern. If the
	/// match is unsuccessful, `false` is returned and the cursor stays in place. This method correctly deals with
	/// potential line-continuation characters within the source string that may exist within the pattern.
	fn take_pat(&mut self, pat: &str) -> bool {
		let pat = pat.chars().collect::<Vec<_>>();
		let pat_len = pat.len();
		let mut pat_count = 0;

		// Store the current position before we check the pattern, so that we can rollback to this position if the
		// match fails.
		let starting_position = self.cursor;

		// If the pattern fits within the remaining length of the string, compare.
		if self.chars.len() >= self.cursor + pat_len {
			while self.peek().is_some() {
				// If we have consumed the entire pattern, that means the pattern has matched and we can break out
				// of the loop.
				if pat_count == pat_len {
					break;
				}

				// Check that the characters match.
				if self.peek().unwrap() != pat[pat_count] {
					self.cursor = starting_position;
					return false;
				}

				self.advance();
				pat_count += 1;
			}

			return true;
		}

		false
	}

	/// Returns the position of the cursor.
	fn position(&self) -> usize {
		self.cursor
	}

	/// Returns whether this lexer has reached the end of the GLSL source string.
	fn is_done(&self) -> bool {
		// We check that the cursor is equal to the length, because that means we have gone past the last character
		// of the string, and hence, that we are done.
		self.cursor == self.chars.len()
	}

	/// Returns the cursor advancement value necessary to consume a line-continuator, if one is present.
	///
	/// This takes a cursor position as `idx`. The reason a separate parameter is needed (rather than accessing
	/// `self.cursor`) is because in the `lookahead_*()` methods the cursor can't move.
	fn take_line_continuator(&self, idx: usize) -> usize {
		let current = match self.chars.get(idx) {
			Some(c) => *c,
			None => return 0,
		};

		// Line-continuators need to begin with `\`.
		if current != '\\' {
			return 0;
		}

		if let Some(lookahead) = self.chars.get(idx + 1) {
			if *lookahead == '\n' {
				// We have a `\<\n>`.
				2
			} else if *lookahead == '\r' {
				if let Some(lookahead_2) = self.chars.get(idx + 2) {
					if *lookahead_2 == '\n' {
						// We have a `\<\r><\n>`.
						3
					} else {
						// We have a `\<\r><something>`, where `<something>` is on the next line.
						2
					}
				} else {
					// We have a `\<\r><eof>`.
					2
				}
			} else if *lookahead == '\\' {
				// We have `\\`; this is a syntax error.
				// TODO: Syntax error
				0
			} else {
				// We have a `\` followed by a non-eol character; this is a syntax error.
				// TODO: Syntax error.
				0
			}
		} else {
			// We have a `\<eof>`, so we might as well treat this is a line-continuator.
			1
		}
	}
}

/// Returns whether the character is allowed to start a word.
fn is_word_start(c: &char) -> bool {
	c.is_ascii_alphabetic() || *c == '_'
}

/// Returns whether the character is allowed to be part of a word.
fn is_word(c: &char) -> bool {
	c.is_ascii_alphanumeric() || *c == '_'
}

/// Returns whether the character is allowed to start a number.
fn is_number_start(c: &char) -> bool {
	c.is_ascii_digit() || *c == '.'
}

/// Returns whether the character is allowed to start a punctuation token.
///
/// Note that whilst the `.` is a punctuation token, it gets caught by the `is_number_start()` branch since that
/// executes first.
fn is_punctuation_start(c: &char) -> bool {
	match c {
		'=' | ',' | '.' | ';' | '(' | ')' | '[' | ']' | '{' | '}' | ':'
		| '+' | '-' | '*' | '/' | '%' | '>' | '<' | '!' | '~' | '?' | '&'
		| '|' | '^' => true,
		_ => false,
	}
}

macro_rules! match_op {
	($lexer:ident, $str:expr, $token:expr) => {
		if $lexer.take_pat($str) {
			return $token;
		}
	};
}
pub(self) use match_op;

/// Matches a punctuation symbol.
fn match_punctuation(lexer: &mut Lexer) -> Token {
	match_op!(lexer, "<<=", Token::Op(OpTy::LShiftEq));
	match_op!(lexer, ">>=", Token::Op(OpTy::RShiftEq));
	match_op!(lexer, "==", Token::Op(OpTy::EqEq));
	match_op!(lexer, "!=", Token::Op(OpTy::NotEq));
	match_op!(lexer, ">=", Token::Op(OpTy::Ge));
	match_op!(lexer, "<=", Token::Op(OpTy::Le));
	match_op!(lexer, "&&", Token::Op(OpTy::AndAnd));
	match_op!(lexer, "||", Token::Op(OpTy::OrOr));
	match_op!(lexer, "++", Token::Op(OpTy::AddAdd));
	match_op!(lexer, "--", Token::Op(OpTy::SubSub));
	match_op!(lexer, "<<", Token::Op(OpTy::LShift));
	match_op!(lexer, ">>", Token::Op(OpTy::RShift));
	match_op!(lexer, "+=", Token::Op(OpTy::AddEq));
	match_op!(lexer, "-=", Token::Op(OpTy::SubEq));
	match_op!(lexer, "*=", Token::Op(OpTy::MulEq));
	match_op!(lexer, "/=", Token::Op(OpTy::DivEq));
	match_op!(lexer, "%=", Token::Op(OpTy::RemEq));
	match_op!(lexer, "&=", Token::Op(OpTy::AndEq));
	match_op!(lexer, "|=", Token::Op(OpTy::OrEq));
	match_op!(lexer, "^^", Token::Op(OpTy::XorXor));
	match_op!(lexer, "^=", Token::Op(OpTy::XorEq));
	match_op!(lexer, "=", Token::Op(OpTy::Eq));
	match_op!(lexer, ";", Token::Semi);
	match_op!(lexer, ".", Token::Dot);
	match_op!(lexer, ",", Token::Comma);
	match_op!(lexer, "(", Token::LParen);
	match_op!(lexer, ")", Token::RParen);
	match_op!(lexer, "[", Token::LBracket);
	match_op!(lexer, "]", Token::RBracket);
	match_op!(lexer, "{", Token::LBrace);
	match_op!(lexer, "}", Token::RBrace);
	match_op!(lexer, "+", Token::Op(OpTy::Add));
	match_op!(lexer, "-", Token::Op(OpTy::Sub));
	match_op!(lexer, "*", Token::Op(OpTy::Mul));
	match_op!(lexer, "/", Token::Op(OpTy::Div));
	match_op!(lexer, ">", Token::Op(OpTy::Gt));
	match_op!(lexer, "<", Token::Op(OpTy::Lt));
	match_op!(lexer, "!", Token::Op(OpTy::Not));
	match_op!(lexer, "~", Token::Op(OpTy::Flip));
	match_op!(lexer, "?", Token::Question);
	match_op!(lexer, ":", Token::Colon);
	match_op!(lexer, "%", Token::Op(OpTy::Rem));
	match_op!(lexer, "&", Token::Op(OpTy::And));
	match_op!(lexer, "|", Token::Op(OpTy::Or));
	match_op!(lexer, "^", Token::Op(OpTy::Xor));
	unreachable!("[token::match_punctuation] Exhausted all of the patterns without matching anything!");
}

/// Matches a word to either the `true`/`false` literal, a keyword, or an identifier in that order of precedence.
fn match_word(str: String) -> Token {
	match str.as_ref() {
		// Booleans
		"true" => Token::Bool(true),
		"false" => Token::Bool(false),
		// Keywords
		"if" => Token::If,
		"else" => Token::Else,
		"for" => Token::For,
		"do" => Token::Do,
		"while" => Token::While,
		"continue" => Token::Continue,
		"switch" => Token::Switch,
		"case" => Token::Case,
		"default" => Token::Default,
		"break" => Token::Break,
		"return" => Token::Return,
		"discard" => Token::Discard,
		"struct" => Token::Struct,
		"subroutine" => Token::Subroutine,
		"const" => Token::Const,
		"in" => Token::In,
		"out" => Token::Out,
		"inout" => Token::InOut,
		"attribute" => Token::Attribute,
		"uniform" => Token::Uniform,
		"varying" => Token::Varying,
		"buffer" => Token::Buffer,
		"shared" => Token::Shared,
		"centroid" => Token::Centroid,
		"sample" => Token::Sample,
		"patch" => Token::Patch,
		"layout" => Token::Layout,
		"flat" => Token::Flat,
		"smooth" => Token::Smooth,
		"noperspective" => Token::NoPerspective,
		"highp" => Token::HighP,
		"mediump" => Token::MediumP,
		"lowp" => Token::LowP,
		"invariant" => Token::Invariant,
		"precise" => Token::Precise,
		"coherent" => Token::Coherent,
		"volatile" => Token::Volatile,
		"restrict" => Token::Restrict,
		"readonly" => Token::Readonly,
		"writeonly" => Token::Writeonly,
		// Reserved
		"common" | "partition" | "active" | "asm" | "class" | "union"
		| "enum" | "typedef" | "template" | "this" | "resource" | "goto"
		| "inline" | "noinline" | "public" | "static" | "extern"
		| "external" | "interface" | "long" | "short" | "half" | "fixed"
		| "unsigned" | "superp" | "input" | "output" | "hvec2" | "hvec3"
		| "hvec4" | "fvec2" | "fvec3" | "fvec4" | "sampler3DRect"
		| "filter" | "sizeof" | "cast" | "namespace" | "using" => {
			Token::Reserved(str)
		}
		// Identifier
		_ => Token::Ident(str),
	}
}

#[cfg(test)]
use crate::span::span;

#[test]
#[rustfmt::skip]
fn spans() {
	// Identifiers/keywords
	assert_eq!(parse_from_str("return"), vec![(Token::Return, span(0, 6))]);
	assert_eq!(parse_from_str("break "), vec![(Token::Break, span(0, 5))]);
	assert_eq!(parse_from_str("return break"), vec![(Token::Return, span(0, 6)), (Token::Break, span(7, 12))]);
	// Punctuation
	assert_eq!(parse_from_str(";"), vec![(Token::Semi, span(0, 1))]);
	assert_eq!(parse_from_str(": "), vec![(Token::Colon, span(0, 1))]);
	assert_eq!(parse_from_str("; :"), vec![(Token::Semi, span(0, 1)), (Token::Colon, span(2, 3))]);
	// Comments
	assert_eq!(parse_from_str("// comment"), vec![(Token::LineComment(" comment".into()), span(0, 10))]);
	assert_eq!(parse_from_str("/* a */"), vec![(Token::BlockComment { str: " a ".into(), contains_eof: false }, span(0, 7))]);
	assert_eq!(parse_from_str("/* a"), vec![(Token::BlockComment { str: " a".into(), contains_eof: true }, span(0, 4))]);
	// Directive
	//assert_eq!(parse_from_str("#dir"), vec![(Token::Directive("dir".into()), span(0, 4))]);
	//assert_eq!(parse_from_str("#dir a "), vec![(Token::Directive("dir a ".into()), span(0, 7))]);
	// Invalid
	assert_eq!(parse_from_str("@"), vec![(Token::Invalid('@'), span(0, 1))]);
	assert_eq!(parse_from_str("¬"), vec![(Token::Invalid('¬'), span(0, 1))]);
	assert_eq!(parse_from_str("@  ¬"), vec![(Token::Invalid('@'), span(0, 1)), (Token::Invalid('¬'), span(3, 4))]);
	// Numbers
	assert_eq!(parse_from_str("."), vec![(Token::Dot, span(0, 1))]);
	assert_eq!(parse_from_str(". "), vec![(Token::Dot, span(0, 1))]);
	assert_eq!(parse_from_str("0xF."), vec![(Token::Num { num: "F".into(), suffix: None, type_: NumType::Hex }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(parse_from_str("123u."), vec![(Token::Num { num: "123".into(), suffix: Some("u".into()), type_: NumType::Dec }, span(0, 4)), (Token::Dot, span(4, 5))]);
	assert_eq!(parse_from_str("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(parse_from_str("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(parse_from_str("1e"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2))]);
	assert_eq!(parse_from_str("123 "), vec![(Token::Num { num: "123".into(), suffix: None, type_: NumType::Dec }, span(0, 3))]);
	assert_eq!(parse_from_str("1e+="), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2)), (Token::Op(OpTy::AddEq), span(2, 4))]);
	assert_eq!(parse_from_str("1e+"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2)), (Token::Op(OpTy::Add), span(2, 3))]);
}

/// Asserts whether the token output of the `parse_from_str()` function matches the right hand side; this ignores
/// the span information.
#[cfg(test)]
macro_rules! assert_tokens {
    ($src:expr, $($token:expr),*) => {
		let output = parse_from_str($src).into_iter().map(|(t, _)| t).collect::<Vec<_>>();
        assert_eq!(output, vec![
            $(
                $token,
            )*
        ])
    };
}

#[test]
fn identifiers() {
	assert_tokens!("ident", Token::Ident("ident".into()));
	assert_tokens!("gl_something", Token::Ident("gl_something".into()));
	assert_tokens!("id_145", Token::Ident("id_145".into()));
	assert_tokens!("_9ga", Token::Ident("_9ga".into()));

	// Broken by line continuator
	assert_tokens!("my_\\\r\nident", Token::Ident("my_ident".into()));
	assert_tokens!("_\\\n9ga", Token::Ident("_9ga".into()));
}

#[test]
fn keywords() {
	assert_tokens!("true", Token::Bool(true));
	assert_tokens!("false", Token::Bool(false));
	assert_tokens!("if", Token::If);
	assert_tokens!("else", Token::Else);
	assert_tokens!("for", Token::For);
	assert_tokens!("do", Token::Do);
	assert_tokens!("while", Token::While);
	assert_tokens!("continue", Token::Continue);
	assert_tokens!("switch", Token::Switch);
	assert_tokens!("case", Token::Case);
	assert_tokens!("default", Token::Default);
	assert_tokens!("break", Token::Break);
	assert_tokens!("return", Token::Return);
	assert_tokens!("discard", Token::Discard);
	assert_tokens!("struct", Token::Struct);
	assert_tokens!("subroutine", Token::Subroutine);
	assert_tokens!("const", Token::Const);
	assert_tokens!("in", Token::In);
	assert_tokens!("out", Token::Out);
	assert_tokens!("inout", Token::InOut);
	assert_tokens!("attribute", Token::Attribute);
	assert_tokens!("uniform", Token::Uniform);
	assert_tokens!("varying", Token::Varying);
	assert_tokens!("buffer", Token::Buffer);
	assert_tokens!("shared", Token::Shared);
	assert_tokens!("centroid", Token::Centroid);
	assert_tokens!("sample", Token::Sample);
	assert_tokens!("patch", Token::Patch);
	assert_tokens!("layout", Token::Layout);
	assert_tokens!("flat", Token::Flat);
	assert_tokens!("smooth", Token::Smooth);
	assert_tokens!("noperspective", Token::NoPerspective);
	assert_tokens!("highp", Token::HighP);
	assert_tokens!("mediump", Token::MediumP);
	assert_tokens!("lowp", Token::LowP);
	assert_tokens!("invariant", Token::Invariant);
	assert_tokens!("precise", Token::Precise);
	assert_tokens!("coherent", Token::Coherent);
	assert_tokens!("volatile", Token::Volatile);
	assert_tokens!("restrict", Token::Restrict);
	assert_tokens!("readonly", Token::Readonly);
	assert_tokens!("writeonly", Token::Writeonly);
	// Reserved
	assert_tokens!("common", Token::Reserved("common".into()));
	assert_tokens!("partition", Token::Reserved("partition".into()));
	assert_tokens!("active", Token::Reserved("active".into()));
	assert_tokens!("asm", Token::Reserved("asm".into()));
	assert_tokens!("class", Token::Reserved("class".into()));
	assert_tokens!("union", Token::Reserved("union".into()));
	assert_tokens!("enum", Token::Reserved("enum".into()));
	assert_tokens!("typedef", Token::Reserved("typedef".into()));
	assert_tokens!("template", Token::Reserved("template".into()));
	assert_tokens!("this", Token::Reserved("this".into()));
	assert_tokens!("resource", Token::Reserved("resource".into()));
	assert_tokens!("goto", Token::Reserved("goto".into()));
	assert_tokens!("inline", Token::Reserved("inline".into()));
	assert_tokens!("noinline", Token::Reserved("noinline".into()));
	assert_tokens!("public", Token::Reserved("public".into()));
	assert_tokens!("static", Token::Reserved("static".into()));
	assert_tokens!("extern", Token::Reserved("extern".into()));
	assert_tokens!("external", Token::Reserved("external".into()));
	assert_tokens!("interface", Token::Reserved("interface".into()));
	assert_tokens!("long", Token::Reserved("long".into()));
	assert_tokens!("short", Token::Reserved("short".into()));
	assert_tokens!("half", Token::Reserved("half".into()));
	assert_tokens!("fixed", Token::Reserved("fixed".into()));
	assert_tokens!("unsigned", Token::Reserved("unsigned".into()));
	assert_tokens!("superp", Token::Reserved("superp".into()));
	assert_tokens!("input", Token::Reserved("input".into()));
	assert_tokens!("output", Token::Reserved("output".into()));
	assert_tokens!("hvec2", Token::Reserved("hvec2".into()));
	assert_tokens!("hvec3", Token::Reserved("hvec3".into()));
	assert_tokens!("hvec4", Token::Reserved("hvec4".into()));
	assert_tokens!("fvec2", Token::Reserved("fvec2".into()));
	assert_tokens!("fvec3", Token::Reserved("fvec3".into()));
	assert_tokens!("fvec4", Token::Reserved("fvec4".into()));
	assert_tokens!("sampler3DRect", Token::Reserved("sampler3DRect".into()));
	assert_tokens!("filter", Token::Reserved("filter".into()));
	assert_tokens!("sizeof", Token::Reserved("sizeof".into()));
	assert_tokens!("cast", Token::Reserved("cast".into()));
	assert_tokens!("namespace", Token::Reserved("namespace".into()));
	assert_tokens!("using", Token::Reserved("using".into()));

	// Broken by line continuator
	assert_tokens!("tr\\\rue", Token::Bool(true));
	assert_tokens!("dis\\\ncard", Token::Discard);
	assert_tokens!("sub\\\r\nroutine", Token::Subroutine);
}

#[test]
fn punctuation() {
	assert_tokens!(";", Token::Semi);
	assert_tokens!(".", Token::Dot);
	assert_tokens!(",", Token::Comma);
	assert_tokens!("(", Token::LParen);
	assert_tokens!(")", Token::RParen);
	assert_tokens!("[", Token::LBracket);
	assert_tokens!("]", Token::RBracket);
	assert_tokens!("{", Token::LBrace);
	assert_tokens!("}", Token::RBrace);
	assert_tokens!(":", Token::Colon);
	assert_tokens!("=", Token::Op(OpTy::Eq));
	assert_tokens!("+", Token::Op(OpTy::Add));
	assert_tokens!("-", Token::Op(OpTy::Sub));
	assert_tokens!("*", Token::Op(OpTy::Mul));
	assert_tokens!("/", Token::Op(OpTy::Div));
	assert_tokens!(">", Token::Op(OpTy::Gt));
	assert_tokens!("<", Token::Op(OpTy::Lt));
	assert_tokens!("!", Token::Op(OpTy::Not));
	assert_tokens!("~", Token::Op(OpTy::Flip));
	assert_tokens!("?", Token::Question);
	assert_tokens!("%", Token::Op(OpTy::Rem));
	assert_tokens!("&", Token::Op(OpTy::And));
	assert_tokens!("|", Token::Op(OpTy::Or));
	assert_tokens!("^", Token::Op(OpTy::Xor));
	assert_tokens!("==", Token::Op(OpTy::EqEq));
	assert_tokens!("!=", Token::Op(OpTy::NotEq));
	assert_tokens!(">=", Token::Op(OpTy::Ge));
	assert_tokens!("<=", Token::Op(OpTy::Le));
	assert_tokens!("&&", Token::Op(OpTy::AndAnd));
	assert_tokens!("||", Token::Op(OpTy::OrOr));
	assert_tokens!("^^", Token::Op(OpTy::XorXor));
	assert_tokens!("++", Token::Op(OpTy::AddAdd));
	assert_tokens!("--", Token::Op(OpTy::SubSub));
	assert_tokens!("<<", Token::Op(OpTy::LShift));
	assert_tokens!(">>", Token::Op(OpTy::RShift));
	assert_tokens!("+=", Token::Op(OpTy::AddEq));
	assert_tokens!("-=", Token::Op(OpTy::SubEq));
	assert_tokens!("*=", Token::Op(OpTy::MulEq));
	assert_tokens!("/=", Token::Op(OpTy::DivEq));
	assert_tokens!("%=", Token::Op(OpTy::RemEq));
	assert_tokens!("&=", Token::Op(OpTy::AndEq));
	assert_tokens!("|=", Token::Op(OpTy::OrEq));
	assert_tokens!("^=", Token::Op(OpTy::XorEq));
	assert_tokens!("<<=", Token::Op(OpTy::LShiftEq));
	assert_tokens!(">>=", Token::Op(OpTy::RShiftEq));

	// Broken by line continuator
	assert_tokens!("!\\\n=", Token::Op(OpTy::NotEq));
	assert_tokens!("+\\\r=", Token::Op(OpTy::AddEq));
	assert_tokens!("=\\\n=", Token::Op(OpTy::EqEq));
	assert_tokens!(">>\\\r\n=", Token::Op(OpTy::RShiftEq));
}

#[test]
#[rustfmt::skip]
fn comments() {
	// Line comments
	assert_tokens!("// a comment", Token::LineComment(" a comment".into()));
	assert_tokens!("//a comment", Token::LineComment("a comment".into()));

	// Broken by line continuator
	assert_tokens!("// a comment \\\rcontinuation", Token::LineComment(" a comment continuation".into()));
	assert_tokens!("//a comment\\\ncontinuation", Token::LineComment("a commentcontinuation".into()));
	assert_tokens!("//a comment \\\r\ncontinuation", Token::LineComment("a comment continuation".into()));
	assert_tokens!("/\\\r/ a comment", Token::LineComment(" a comment".into()));
	assert_tokens!("/\\\r\n/ a comment", Token::LineComment(" a comment".into()));
	assert_tokens!("//\\\n a comment", Token::LineComment(" a comment".into()));

	// Multi-line comments
	assert_tokens!("/* a comment */", Token::BlockComment{ str: " a comment ".into(), contains_eof: false});
	assert_tokens!("/*a comment*/", Token::BlockComment{ str: "a comment".into(), contains_eof: false});
	assert_tokens!("/* <Ll#,;#l,_!\"^$!6 */", Token::BlockComment{ str: " <Ll#,;#l,_!\"^$!6 ".into(), contains_eof: false});
	assert_tokens!("/* open-ended comment", Token::BlockComment{ str: " open-ended comment".into(), contains_eof: true});

	// Broken by line continuator
	assert_tokens!("/\\\r* a comment */", Token::BlockComment{ str: " a comment ".into(), contains_eof: false});
	assert_tokens!("/\\\n*a comment*\\\r\n/", Token::BlockComment{ str: "a comment".into(), contains_eof: false});
}

#[test]
#[rustfmt::skip]
fn integers(){
	// Zero
	assert_tokens!("0", Token::Num{num: "0".into(), suffix: None, type_: NumType::Dec});
	// Zero with suffix
	assert_tokens!("0u", Token::Num{num: "0".into(), suffix: Some("u".into()), type_: NumType::Dec});
	// Decimal
	assert_tokens!("1", Token::Num{num: "1".into(), suffix: None, type_: NumType::Dec});
	assert_tokens!("123456", Token::Num{num: "123456".into(), suffix: None, type_: NumType::Dec});
	assert_tokens!("100008", Token::Num{num: "100008".into(), suffix: None,  type_: NumType::Dec});
	// Decimal with suffix
	assert_tokens!("1u", Token::Num{num: "1".into(), suffix: Some("u".into()), type_: NumType::Dec});
	assert_tokens!("123456u", Token::Num{num: "123456".into(), suffix: Some("u".into()), type_: NumType::Dec});
	assert_tokens!("100008u", Token::Num{num: "100008".into(), suffix: Some("u".into()),  type_: NumType::Dec});
	// Octal
	assert_tokens!("00", Token::Num{num: "0".into(), suffix: None,  type_: NumType::Oct});
	assert_tokens!("01715", Token::Num{num: "1715".into(), suffix: None,  type_: NumType::Oct});
	assert_tokens!("09183", Token::Num{num: "9183".into(), suffix: None, type_: NumType::Oct});
	// Octal with suffix
	assert_tokens!("00u", Token::Num{num: "0".into(), suffix: Some("u".into()),  type_: NumType::Oct});
	assert_tokens!("01715u", Token::Num{num: "1715".into(), suffix: Some("u".into()),  type_: NumType::Oct});
	assert_tokens!("09183u", Token::Num{num: "9183".into(), suffix: Some("u".into()), type_: NumType::Oct});
	// Hexadecimal
	assert_tokens!("0x", Token::Num{num: "".into(), suffix: None, type_: NumType::Hex});
	assert_tokens!("0x91fa", Token::Num{num: "91fa".into(), suffix: None,  type_: NumType::Hex});
	assert_tokens!("0x00F", Token::Num{num: "00F".into(), suffix: None,  type_: NumType::Hex});
	// Hexadecimal with suffix
	assert_tokens!("0xu", Token::Num{num: "".into(), suffix: Some("u".into()), type_: NumType::Hex});
	assert_tokens!("0x91fau", Token::Num{num: "91fa".into(), suffix: Some("u".into()),  type_: NumType::Hex});
	assert_tokens!("0x00Fu", Token::Num{num: "00F".into(), suffix: Some("u".into()),  type_: NumType::Hex});
	
	// Broken by line continuator
	assert_tokens!("123\\\r456", Token::Num{num: "123456".into(), suffix: None, type_: NumType::Dec});
	assert_tokens!("12\\\n3456u", Token::Num{num: "123456".into(), suffix: Some("u".into()), type_: NumType::Dec});
	assert_tokens!("0171\\\n5", Token::Num{num: "1715".into(), suffix: None,  type_: NumType::Oct});
	assert_tokens!("0x91\\\r\nfa", Token::Num{num: "91fa".into(), suffix: None,  type_: NumType::Hex});
	assert_tokens!("0x\\\r91fau", Token::Num{num: "91fa".into(), suffix: Some("u".into()),  type_: NumType::Hex});
	assert_tokens!("0x\\\nu", Token::Num{num: "".into(), suffix: Some("u".into()), type_: NumType::Hex});
}

#[test]
#[rustfmt::skip]
fn floats() {
	// Zeroes
	assert_tokens!("0.0", Token::Num{num: "0.0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.", Token::Num{num: "0.".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0", Token::Num{num: ".0".into(), suffix: None, type_: NumType::Float});
	// Zeroes with suffix
	assert_tokens!("0.0lf", Token::Num{num: "0.0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.lf", Token::Num{num: "0.".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0lf", Token::Num{num: ".0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Zeroes with exponent
	assert_tokens!("0e7", Token::Num{num: "0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0e+7", Token::Num{num: "0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0e-7", Token::Num{num: "0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e7", Token::Num{num: "0.0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e+7", Token::Num{num: "0.0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e-7", Token::Num{num: "0.0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e7", Token::Num{num: "0.e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e+7", Token::Num{num: "0.e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e-7", Token::Num{num: "0.e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e7", Token::Num{num: ".0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e+7", Token::Num{num: ".0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e-7", Token::Num{num: ".0e-7".into(), suffix: None, type_: NumType::Float});
	// Zeroes with exponent and suffix
	assert_tokens!("0e7lf", Token::Num{num: "0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0e+7lf", Token::Num{num: "0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0e-7lf", Token::Num{num: "0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e7lf", Token::Num{num: "0.0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e+7lf", Token::Num{num: "0.0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e-7lf", Token::Num{num: "0.0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e7lf", Token::Num{num: "0.e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e+7lf", Token::Num{num: "0.e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e-7lf", Token::Num{num: "0.e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e7lf", Token::Num{num: ".0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e+7lf", Token::Num{num: ".0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e-7lf", Token::Num{num: ".0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Digits
	assert_tokens!("1.0", Token::Num{num: "1.0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1", Token::Num{num: "1.1".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.", Token::Num{num: "1.".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1", Token::Num{num: ".1".into(), suffix: None, type_: NumType::Float});
	// Digits with suffix
	assert_tokens!("1.0lf", Token::Num{num: "1.0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1lf", Token::Num{num: "1.1".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.lf", Token::Num{num: "1.".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1lf", Token::Num{num: ".1".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Digits with exponent
	assert_tokens!("1e7", Token::Num{num: "1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1e+7", Token::Num{num: "1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1e-7", Token::Num{num: "1e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e7", Token::Num{num: "1.0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e+7", Token::Num{num: "1.0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e-7", Token::Num{num: "1.0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e7", Token::Num{num: "1.1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e+7", Token::Num{num: "1.1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e-7", Token::Num{num: "1.1e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e7", Token::Num{num: "1.e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e+7", Token::Num{num: "1.e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e-7", Token::Num{num: "1.e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e7", Token::Num{num: ".1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e+7", Token::Num{num: ".1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e-7", Token::Num{num: ".1e-7".into(), suffix: None, type_: NumType::Float});
	// Digits with exponent and suffix
	assert_tokens!("1e7lf", Token::Num{num: "1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1e+7lf", Token::Num{num: "1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1e-7lf", Token::Num{num: "1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e7lf", Token::Num{num: "1.0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e+7lf", Token::Num{num: "1.0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e-7lf", Token::Num{num: "1.0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e7lf", Token::Num{num: "1.1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e+7lf", Token::Num{num: "1.1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e-7lf", Token::Num{num: "1.1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e7lf", Token::Num{num: "1.e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e+7lf", Token::Num{num: "1.e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e-7lf", Token::Num{num: "1.e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e7lf", Token::Num{num: ".1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e+7lf", Token::Num{num: ".1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e-7lf", Token::Num{num: ".1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	
	// Broken by line continuator
	assert_tokens!("0.\\\r0", Token::Num{num: "0.0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".\\\n0", Token::Num{num: ".0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0\\\nlf", Token::Num{num: ".0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.\\\r\nlf", Token::Num{num: "0.".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0e\\\r7", Token::Num{num: "0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0e\\\r\n-7", Token::Num{num: "0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0\\\r\ne+7", Token::Num{num: ".0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e-\\\n7lf", Token::Num{num: "1.0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1\\\re-7lf", Token::Num{num: ".1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
}

#[test]
#[rustfmt::skip]
fn illegal(){
	// Note: All of these characters will be parsed as part of a preprocessor directive string; only later once the
	// string is tokenised will any errors come up.
	assert_tokens!("@", Token::Invalid('@'));
	assert_tokens!("¬", Token::Invalid('¬'));
	assert_tokens!("`", Token::Invalid('`'));
	assert_tokens!("¦", Token::Invalid('¦'));
	assert_tokens!("'", Token::Invalid('\''));
	assert_tokens!("\"", Token::Invalid('"'));
	assert_tokens!("£", Token::Invalid('£'));
	assert_tokens!("$", Token::Invalid('$'));
	assert_tokens!("€", Token::Invalid('€'));
}
