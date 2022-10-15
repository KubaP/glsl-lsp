//! Types and functionality related to lexing preprocessor directives.
//!
//! Overview of the directives:
//! - `#version` - see [`VersionToken`],
//! - `#extension` - see [`ExtensionToken`],
//! - `#line` - see [`LineToken`],
//!
//! The `#line` directive undergoes macro expansion, so the following would be valid: `#define FOO 5 \r\n #line
//! FOO`.

use super::{is_word, is_word_start, Lexer};
use crate::{span::Spanned, token::match_op, Span};

pub fn parse_from_str(source: &str, offset: usize) -> TokenStream {
	let mut lexer = Lexer::new(source);
	let mut buffer = String::new();
	let mut kw_start = 0;
	'main: while !lexer.is_done() {
		kw_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						break 'main;
					}
				};

				// Check if it can be part of a word.
				if is_word(&current) {
					// The character can be part of an word, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of an word.
					break 'main;
				}
			}
		} else if current.is_whitespace() {
			// We ignore leading whitespace characters.
			lexer.advance();
		}
	}
	let kw_end = lexer.position();
	let kw_span = Span::new(kw_start, kw_end) + offset;

	// TODO: Pass macro names into this function.
	match buffer.as_ref() {
		"version" => parse_version(lexer, kw_span, offset),
		"extension" => parse_extension(lexer, kw_span, offset),
		"line" => parse_line(lexer, kw_span, offset, vec![]),
		"define" => parse_define(lexer, kw_span, offset),
		"undef" => parse_undef(lexer, kw_span, offset),
		"ifdef" | "ifndef" | "if" | "elif" | "else" | "endif" => {
			parse_condition(lexer, kw_span, buffer.as_ref(), offset)
		}
		"error" | "pragma" => TokenStream::Unsupported,
		_ => TokenStream::Invalid,
	}
}

/// Parse a `#version` directive.
fn parse_version(
	mut lexer: Lexer,
	kw_span: Span,
	offset: usize,
) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	'main: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							VersionToken::Word(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
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
						VersionToken::Word(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						} + offset,
					));
					break 'word;
				}
			}
		} else if current.is_ascii_digit() {
			buffer.push(current);
			lexer.advance();

			let mut invalid_num = false;
			'number: loop {
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						if invalid_num {
							tokens.push((
								VersionToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										VersionToken::Number(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										} + offset,
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									VersionToken::InvalidNumber(
										std::mem::take(&mut buffer),
									),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								)),
							}
						}
						break 'number;
					}
				};

				if current.is_ascii_digit() {
					// The character can be part of a number, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else if current.is_ascii_alphabetic() {
					// The character can't be part of a number, but it also requires separation to be valid. Hence
					// this becomes an invalid number-like token.
					invalid_num = true;
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					if invalid_num {
						tokens.push((
							VersionToken::InvalidNumber(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									VersionToken::Number(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								VersionToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							)),
						}
					}
					break 'number;
				}
			}
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				VersionToken::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		}
	}

	TokenStream::Version {
		kw: kw_span,
		tokens,
	}
}

/// Parse an `#extension` directive.
fn parse_extension(
	mut lexer: Lexer,
	kw_span: Span,
	offset: usize,
) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	'main: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							ExtensionToken::Word(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
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
						ExtensionToken::Word(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						} + offset,
					));
					break 'word;
				}
			}
		} else if current == ':' {
			lexer.advance();
			tokens.push((
				ExtensionToken::Colon,
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				ExtensionToken::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		}
	}

	TokenStream::Extension {
		kw: kw_span,
		tokens,
	}
}

/// Parse a `#line` directive.
fn parse_line(
	mut lexer: Lexer,
	kw_span: Span,
	offset: usize,
	macro_names: Vec<&'static str>,
) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	'main: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						if macro_names.contains(&buffer.as_str()) {
							// This word matches a macro name.
							tokens.push((
								LineToken::Macro(std::mem::take(&mut buffer)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						} else {
							// This word doesn't match a macro name.
							tokens.push((
								LineToken::InvalidWord(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						}
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
					if macro_names.contains(&buffer.as_str()) {
						// This word matches a macro name.
						tokens.push((
							LineToken::Macro(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					} else {
						// This word doesn't match a macro name.
						tokens.push((
							LineToken::InvalidWord(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					}
					break 'word;
				}
			}
		} else if current.is_ascii_digit() {
			buffer.push(current);
			lexer.advance();

			let mut invalid_num = false;
			'number: loop {
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						if invalid_num {
							tokens.push((
								LineToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										LineToken::Number(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										} + offset,
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									LineToken::InvalidNumber(std::mem::take(
										&mut buffer,
									)),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								)),
							}
						}
						break 'number;
					}
				};

				if current.is_ascii_digit() {
					// The character can be part of a number, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else if current.is_ascii_alphabetic() {
					// The character can't be part of a number, but it also requires separation to be valid. Hence
					// this becomes an invalid number-like token.
					invalid_num = true;
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					if invalid_num {
						tokens.push((
							LineToken::InvalidNumber(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									LineToken::Number(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								LineToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							)),
						}
					}
					break 'number;
				}
			}
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				LineToken::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		}
	}

	TokenStream::Line {
		kw: kw_span,
		tokens,
	}
}

/// Parse a `#define` directive.
fn parse_define(mut lexer: Lexer, kw_span: Span, offset: usize) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	let buffer_start = lexer.position();

	let mut current = match lexer.peek() {
		Some(c) => c,
		None => {
			return TokenStream::Define {
				kw: kw_span,
				ident_tokens: vec![],
				body_tokens: vec![],
			}
		}
	};

	if !is_word_start(&current) {
		return TokenStream::Define {
			kw: kw_span,
			ident_tokens: vec![],
			body_tokens: vec![],
		};
	}

	buffer.push(current);
	lexer.advance();
	loop {
		// Peek the current character.
		current = match lexer.peek() {
			Some(c) => c,
			None => {
				// We have reached the end of the source string, and therefore the end of this word and define
				// directive.
				return TokenStream::Define {
					kw: kw_span,
					ident_tokens: vec![(
						DefineToken::Identifier(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						} + offset,
					)],
					body_tokens: vec![],
				};
			}
		};

		if is_word(&current) {
			// The character can be part of a word, so we consume it and continue looping.
			buffer.push(current);
			lexer.advance();
		} else if current == '(' {
			// We have encountered a `(` immediately after a word. This means this directive is a function
			// macro and we now need to parse the parameter list.
			tokens.push((
				DefineToken::Identifier(std::mem::take(&mut buffer)),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
			let pos = lexer.position();
			lexer.advance();
			tokens.push((
				DefineToken::LParen,
				Span {
					start: pos,
					end: lexer.position(),
				} + offset,
			));
			break;
		} else {
			// We have reached the end of the first word, and have not encountered a `(` immediately
			// afterwards. This means this directive is an object macro and everything from here on is a
			// standard GLSL token.
			tokens.push((
				DefineToken::Identifier(std::mem::take(&mut buffer)),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));

			return TokenStream::Define {
				kw: kw_span,
				ident_tokens: tokens,
				body_tokens: vec![],
			};
		}
	}

	// We have a function macro, and now need to parse the parameter list.
	loop {
		let token_start = lexer.position();
		current = match lexer.peek() {
			Some(c) => c,
			None => {
				return TokenStream::Define {
					kw: kw_span,
					ident_tokens: tokens,
					body_tokens: vec![],
				};
			}
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							DefineToken::Identifier(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
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
						DefineToken::Identifier(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						} + offset,
					));
					break 'word;
				}
			}
		} else if current == ',' {
			lexer.advance();
			tokens.push((
				DefineToken::Comma,
				Span {
					start: token_start,
					end: lexer.position(),
				} + offset,
			));
		} else if current == ')' {
			lexer.advance();
			tokens.push((
				DefineToken::RParen,
				Span {
					start: token_start,
					end: lexer.position(),
				} + offset,
			));
			break;
		} else {
			lexer.advance();
			tokens.push((
				DefineToken::Invalid(current),
				Span {
					start: token_start,
					end: lexer.position(),
				},
			));
		}
	}

	return TokenStream::Define {
		kw: kw_span,
		ident_tokens: tokens,
		body_tokens: vec![],
	};
}

/// Parse an `#undef` directive.
fn parse_undef(mut lexer: Lexer, kw_span: Span, offset: usize) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	'main: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							UndefToken::Identifier(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
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
						UndefToken::Identifier(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						} + offset,
					));
					break 'word;
				}
			}
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				UndefToken::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		}
	}

	TokenStream::Undef {
		kw: kw_span,
		tokens,
	}
}

/// Parse a `#ifdef`/`#ifndef`/`#if`/`#elif`/`#else`/`#endif` directive.
fn parse_condition(
	mut lexer: Lexer,
	kw_span: Span,
	kw: &str,
	offset: usize,
) -> TokenStream {
	// We continue off from where the lexer previously stopped.
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	'main: while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break 'main,
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						if &buffer == "defined" {
							tokens.push((
								ConditionToken::Defined,
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
							buffer.clear();
						} else {
							tokens.push((
								ConditionToken::Identifier(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						}
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
					if &buffer == "defined" {
						tokens.push((
							ConditionToken::Defined,
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
						buffer.clear();
					} else {
						tokens.push((
							ConditionToken::Identifier(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					}
					break 'word;
				}
			}
		} else if current.is_ascii_digit() {
			buffer.push(current);
			lexer.advance();

			let mut invalid_num = false;
			'number: loop {
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						if invalid_num {
							tokens.push((
								ConditionToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										ConditionToken::Number(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										} + offset,
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									ConditionToken::InvalidNumber(
										std::mem::take(&mut buffer),
									),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								)),
							}
						}
						break 'number;
					}
				};

				if current.is_ascii_digit() {
					// The character can be part of a number, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else if current.is_ascii_alphabetic() {
					// The character can't be part of a number, but it also requires separation to be valid. Hence
					// this becomes an invalid number-like token.
					invalid_num = true;
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					if invalid_num {
						tokens.push((
							ConditionToken::InvalidNumber(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							} + offset,
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									ConditionToken::Number(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									} + offset,
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								ConditionToken::InvalidNumber(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								} + offset,
							)),
						}
					}
					break 'number;
				}
			}
		} else if is_condition_punctuation_start(&current) {
			lexer.advance();
			tokens.push((
				match_condition_punctuation(&mut lexer),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				ConditionToken::Invalid(current),
				Span {
					start: buffer_start,
					end: lexer.position(),
				} + offset,
			));
		}
	}

	match kw {
		"ifdef" => TokenStream::IfDef {
			kw: kw_span,
			tokens,
		},
		"ifndef" => TokenStream::IfNotDef {
			kw: kw_span,
			tokens,
		},
		"if" => TokenStream::If {
			kw: kw_span,
			tokens,
		},
		"elif" => TokenStream::ElseIf {
			kw: kw_span,
			tokens,
		},
		"else" => TokenStream::Else {
			kw: kw_span,
			tokens,
		},
		"endif" => TokenStream::EndIf {
			kw: kw_span,
			tokens,
		},
		_ => unreachable!(),
	}
}

/// Returns whether the character is allowed to start a punctuation token.
fn is_condition_punctuation_start(c: &char) -> bool {
	match c {
		'=' | '+' | '-' | '*' | '/' | '%' | '>' | '<' | '!' | '~' | '&'
		| '|' | '^' | '(' | ')' => true,
		_ => false,
	}
}

/// Matches a punctuation symbol.
fn match_condition_punctuation(lexer: &mut Lexer) -> ConditionToken {
	match_op!(lexer, "==", ConditionToken::EqEq);
	match_op!(lexer, "!=", ConditionToken::NotEq);
	match_op!(lexer, ">=", ConditionToken::Ge);
	match_op!(lexer, "<=", ConditionToken::Le);
	match_op!(lexer, "&&", ConditionToken::AndAnd);
	match_op!(lexer, "||", ConditionToken::OrOr);
	match_op!(lexer, "^^", ConditionToken::XorXor);
	match_op!(lexer, "<<", ConditionToken::LShift);
	match_op!(lexer, ">>", ConditionToken::RShift);
	match_op!(lexer, "(", ConditionToken::LParen);
	match_op!(lexer, ")", ConditionToken::RParen);
	match_op!(lexer, "+", ConditionToken::Add);
	match_op!(lexer, "-", ConditionToken::Sub);
	match_op!(lexer, "*", ConditionToken::Mul);
	match_op!(lexer, "/", ConditionToken::Div);
	match_op!(lexer, ">", ConditionToken::Gt);
	match_op!(lexer, "<", ConditionToken::Lt);
	match_op!(lexer, "!", ConditionToken::Not);
	match_op!(lexer, "~", ConditionToken::Flip);
	match_op!(lexer, "%", ConditionToken::Rem);
	match_op!(lexer, "&", ConditionToken::And);
	match_op!(lexer, "|", ConditionToken::Or);
	match_op!(lexer, "^", ConditionToken::Xor);
	unreachable!("[preprocessor::match_condition_punctuation] Exhausted all of the patterns without matching anything!");
}

/// A vector of tokens representing a specific preprocessor directive.
pub enum TokenStream {
	/// A directive which is not currently supported by this crate.
	Unsupported,
	/// An invalid directive, e.g. `#nonexistent`.
	Invalid,
	/// A `#version` directive.
	Version {
		kw: Span,
		tokens: Vec<Spanned<VersionToken>>,
	},
	/// An `#extension` directive.
	Extension {
		kw: Span,
		tokens: Vec<Spanned<ExtensionToken>>,
	},
	/// A `#line` directive.
	Line {
		kw: Span,
		tokens: Vec<Spanned<LineToken>>,
	},
	/// A `#define` directive.
	Define {
		kw: Span,
		ident_tokens: Vec<Spanned<DefineToken>>,
		body_tokens: Vec<Spanned<super::Token>>,
	},
	/// An `#undef` directive.
	Undef {
		kw: Span,
		tokens: Vec<Spanned<UndefToken>>,
	},
	/// An `#ifdef` directive.
	IfDef {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#ifndef` directive.
	IfNotDef {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#if` directive.
	If {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#elif` directive.
	ElseIf {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#else` directive.
	Else {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#endif` directive.
	EndIf {
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
}

/// A token representing a unit of text in a `#version` directive.
///
/// # Description of behaviour
/// The GLSL specification defines the directive to be:
/// ```text
/// #version _number_
/// #version _number_ _profile_
/// ```
/// where:
/// - `_number_` matches `[0-9]+\s`,
/// - `_profile_` matches `core|compatability|es`.
///
/// This lexer behaves as following:
/// - When the lexer comes across anything which matches the `[0-9]+` pattern it produces a
///   [`Number`](VersionToken::Number) token, even if the token doesn't match a valid GLSL version number. If the
///   number cannot be parsed into a [`usize`] it produces an [`InvalidNumber`](VersionToken::InvalidNumber) token.
///   If it matches the `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern it produces an
///   [`InvalidNumber`](VersionToken::InvalidNumber) token.
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*` pattern it
///   produces a [`Word`](VersionToken::Word) token.
/// - Anything else produces the [`Invalid`](VersionToken::Invalid) token.
///
/// Notes:
/// - There are no individual `core/compatability/es` keyword tokens; they are just a `Word`. This is to make it
///   easier to perform error recovery in the case that a word has incorrect capitalization but otherwise would
///   match, e.g. `CORE` instead of `core`.
#[derive(Debug, Clone, PartialEq)]
pub enum VersionToken {
	/// An integer number.
	Number(usize),
	/// A word.
	Word(String),
	/// An invalid number.
	InvalidNumber(String),
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in an `#extension` directive.
///
/// # Description of behaviour
/// The GLSL specification defines the directive to be:
/// ```text
/// #extension _extension-name_ : _behaviour_
/// #extension all : _behaviour_
/// ```
/// where:
/// - `_extension-name_` matches `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*`, - `_behaviour_` matches
/// `require|enable|warn|disable`.
///
/// This lexer behaves as following:
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*` pattern it
///   produces a [`Word`](ExtensionToken::Word) token.
/// - When the lexer comes across the `:` symbol it produces the [`Colon`](ExtensionToken::Colon) token.
/// - Anything else produces the [`Invalid`](ExtensionToken::Invalid) token.
///
/// Notes:
/// - There are no individual `require/enable/warn/disable/all` keyword tokens; they are just a `Word`. This is to
///   make it easier to perform error recovery in the case that a word has incorrect capitalization but otherwise
///   would match, e.g. `WARN` instead of `warn`.
#[derive(Debug, Clone, PartialEq)]
pub enum ExtensionToken {
	/// A word that matches `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*`.
	Word(String),
	/// A colon `:`.
	Colon,
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in a `#line` directive.
///
/// # Description of behaviour
/// The GLSL specification defines the directive to be:
/// ```text
/// #line _line_
/// #line _line_ _source-string-number_
/// ```
/// where `_line_` and `_source-string-number_` match either `[0-9]+\s`, or
/// `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*\s` if it also matches a macro name.
///
/// This lexer behaves as following:
/// - When the lexer comes across anything which matches the `[0-9]+` pattern it produces a
///   [`Number`](LineToken::Number) token. If the number cannot be parsed into a [`usize`] it produces an
///   [`InvalidNumber`](LineToken::InvalidNumber) token. If it matches the
///   `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern it produces an [`InvalidNumber`](LineToken::InvalidNumber)
///   token.
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*` pattern and
///   matches one of the passed-in macro names it produces a [`Macro`](LineToken::Macro) token. If it does not
///   match a macro name it produces an [`InvalidWord`](LineToken::InvalidWord) token.
/// - Anything else produces the [`Invalid`](LineToken::Invalid) token.
#[derive(Debug, Clone, PartialEq)]
pub enum LineToken {
	/// An integer number.
	Number(usize),
	/// A macro identifier.
	Macro(String),
	/// An invalid number.
	InvalidNumber(String),
	/// An identifier which does not match any valid macro name.
	InvalidWord(String),
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in the first part of a `#define` directive.
#[derive(Debug, Clone, PartialEq)]
pub enum DefineToken {
	/// An identifier
	Identifier(String),
	/// An invalid character.
	Invalid(char),
	/// An opening parenthesis `(`.
	LParen,
	/// A closing parenthesis `)`.
	RParen,
	/// A comma `,`.
	Comma,
}

/// A token representing a unit of text in an `#undef` directive.
#[derive(Debug, Clone, PartialEq)]
pub enum UndefToken {
	/// An identifier.
	Identifier(String),
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in a `#ifdef`/`#ifndef`/`#if`/`#elif`/`#else`/`#endif` directive.
///
/// # Description of behaviour
///
/// The GLSL specification defines the following valid tokens:
/// - integer literals,
/// - identifiers
/// - define keyword
/// - punctuation
#[derive(Debug, Clone, PartialEq)]
pub enum ConditionToken {
	/// An integer number.
	Number(usize),
	/// An identifier.
	Identifier(String),
	/// An invalid number.
	InvalidNumber(String),
	/// An invalid character.
	Invalid(char),
	/* KEYWORDS */
	/// The `defined` keyword.
	Defined,
	/* PUNCTUATION */
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
	/// The `~` symbol.
	Flip,
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
	/// An opening parenthesis `(`.
	LParen,
	/// A closing parenthesis `)`.
	RParen,
}
