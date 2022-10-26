//! Types related to preprocessor token streams.
//!
//! This module contains the enums use to represent tokens in the different preprocessor directives.
//!
//! The preprocessor is a single-pass algorithm. This means that a `#define` macro cannot create another
//! preprocessor directive as its output. The token concatenation operator (`##`) is only valid within the body of
//! a `#define` directive.
//!
//! # Macro expansion
//! Macro expansion within directives is limited; only the `#line` directive accepts a macro expansion instead of
//! an expected token:
//! ```c
//! #define FOO 450
//!
//! // This is valid:
//! #line FOO 7
//!
//! // But this isn't:
//! #version FOO compatability
//! ```
//!
//! The `#define` macro follows through existing macros, but it does not expand them at the definition site:
//! ```c
//! #define FOO 5
//! #define BAR FOO
//!
//! #define FOO 10
//!
//! int i = BAR; // Expands to: int i = 10;
//! ```
//! As you can see, within the `BAR` macro the `FOO` macro is evaluated, but this takes the latest value of `FOO`
//! whenever `BAR` is called. It does not, strictly speaking, expand the `FOO` macro when `BAR` is defined.
//!
//! The `#undef` and all of the conditional directives accept macro names, but they also do not expand them:
//! ```c
//! #define FOO -7
//!
//! // This is valid:
//! #if 1 * FOO
//! #endif
//!
//! // But this isn't:
//! #if 1 FOO
//! #endif
//! ```
//!
//! # Differences from the C preprocessor
//! The GLSL preprocessor is based off the C++98 preprocessor, but it:
//! - has no support for digraphs or trigraphs.
//! - has no support for string or character literals, and hence no support for the stringizing operator,
//! - has no support for universal character names (`\uXXXX` notation),
//! - has no support for any number literals other than integers (with no prefixes/suffixes),
//! - has the extra `version` and `extension` directives, and lacks the `include` directive,
//! - has different pre-defined macros, (which depend on the exact GLSL version).

use super::{is_word, is_word_start, match_op, Lexer};
use crate::{Span, Spanned};

/// A vector of tokens representing a specific preprocessor directive.
///
/// See the individual token types for an overview of the directive and the behaviour of the lexer.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenStream {
	/// An empty directive; just a `#` with nothing else on the same line.
	Empty,
	/// A directive which conforms to the `#<keyword> <content>` pattern but the keyword is not a recognized word,
	/// e.g. `#nonexistent foo bar`.
	Custom {
		/// Span of the custom keyword.
		kw: Spanned<String>,
		/// The contents of everything after the custom keyword, as a string.
		content: Option<Spanned<String>>,
	},
	/// A directive which doesn't conform to the `#<keyword> <content>` pattern.
	Invalid {
		/// The contents of everything after the beginning `#`, as a string.
		content: Spanned<String>,
	},
	/// A `#version` directive.
	Version {
		/// Span of the `version` keyword.
		kw: Span,
		tokens: Vec<Spanned<VersionToken>>,
	},
	/// An `#extension` directive.
	Extension {
		/// Span of the `extension` keyword.
		kw: Span,
		tokens: Vec<Spanned<ExtensionToken>>,
	},
	/// A `#line` directive.
	Line {
		/// Span of the `line` keyword.
		kw: Span,
		tokens: Vec<Spanned<LineToken>>,
	},
	/// A `#define` directive.
	Define {
		/// Span of the `define` keyword.
		kw: Span,
		/// Tokens of the macro identifier (and optional parameter list for a function-like macro).
		ident_tokens: Vec<Spanned<DefineToken>>,
		/// Tokens of the macro body, i.e. the GLSL tokens which replace a macro invocation.
		body_tokens: super::TokenStream,
	},
	/// An `#undef` directive.
	Undef {
		/// Span of the `undef` keyword.
		kw: Span,
		tokens: Vec<Spanned<UndefToken>>,
	},
	/// An `#ifdef` directive.
	IfDef {
		/// Span of the `ifdef` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#ifndef` directive.
	IfNotDef {
		/// Span of the `ifndef` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#if` directive.
	If {
		/// Span of the `if` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#elif` directive.
	ElseIf {
		/// Span of the `elseif` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#else` directive.
	Else {
		/// Span of the `else` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#endif` directive.
	EndIf {
		/// Span of the `endif` keyword.
		kw: Span,
		tokens: Vec<Spanned<ConditionToken>>,
	},
	/// An `#error` directive.
	Error {
		/// Span of the `error` keyword.
		kw: Span,
		/// The contents of everything after the keyword. The `#error` directive treats everything following the
		/// keyword verbatim as the error message, so no further processing is necessary.
		message: Option<Spanned<String>>,
	},
	/// A `#pragma` directive.
	Pragma {
		/// Span of the `pragma` keyword.
		kw: Span,
		/// There is no defined set of what is and isn't allowed as a compiler option; it entirely depends on the
		/// compiler, hence for maximum compatability this is just a string of everything after the keyword.
		options: Option<Spanned<String>>,
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
///   [`Num`](VersionToken::Num) token, even if the token doesn't match a valid GLSL version number. If the number
///   cannot be parsed into a [`usize`] it produces an [`InvalidNum`](VersionToken::InvalidNum) token. If it
///   matches the `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern it produces an
///   [`InvalidNum`](VersionToken::InvalidNum) token.
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
	Num(usize),
	/// A word.
	Word(String),
	/// An invalid number.
	InvalidNum(String),
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
/// - `_extension-name_` matches `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*`,
/// - `_behaviour_` matches `require|enable|warn|disable`.
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
/// where `_line_` and `_source-string-number_` match `[0-9]+\s`.
///
/// ⚠ Note that this is the only directive within which macros are a valid replacement for tokens. Therefore,
/// something like `#define FOO 5 \r\n #line FOO 7` is valid.
///
/// This lexer behaves as following:
/// - When the lexer comes across anything which matches the `[0-9]+` pattern it produces a [`Num`](LineToken::Num)
///   token. If the number cannot be parsed into a [`usize`] it produces an [`InvalidNum`](LineToken::InvalidNum)
///   token. If it matches the `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern it produces an
///   [`InvalidNum`](LineToken::InvalidNum) token.
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*` pattern it
///   produces an [`Ident`](LineToken::Ident) token. This is to support macro expansion within the directive, but
///   this **does not** check if a macro with the given name actually exists.
/// - Anything else produces the [`Invalid`](LineToken::Invalid) token.
#[derive(Debug, Clone, PartialEq)]
pub enum LineToken {
	/// An integer number.
	Num(usize),
	/// An identifier.
	Ident(String),
	/// An invalid number.
	InvalidNum(String),
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in the first part of a `#define` directive.
///
/// # Description of behaviour
/// The GLSL specification defines the directive to be:
/// ```text
/// #define _identifier_ _replacement-tokens_
/// #define _identifier() _replacement-tokens_
/// #define _identifier(_param_) _replacement-tokens_
/// #define _identifier(_param_,..., _param) _replacement-tokens_
/// ```
/// where:
/// - `_identifier_` and `_param_` match `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*\s`,
/// - `_replacement-tokens_` is zero or more standard GLSL tokens, with the expection that the `##` token
///   concatenation operator ([`Token::MacroConcat`](super::Token::MacroConcat)) is allowed to be present.
///
/// This lexer behaves as following:
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*` pattern it
///   produces an [`Ident`](DefineToken::Ident) token.
/// - When the lexer comes across `(` it produces a [`LParen`](DefineToken::LParen) token.
/// - When the lexer comes across `)` it produces a [`RParen`](DefineToken::RParen) token.
/// - When the lexer comes across `,` it produces a [`Comma`](DefineToken::Comma) token.
/// - Anything else produces the [`Invalid`](DefineToken::Invalid) token.
#[derive(Debug, Clone, PartialEq)]
pub enum DefineToken {
	/// An identifier
	Ident(String),
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
///
/// # Description of behaviour
/// The GLl specification defines the directive to be:
/// ```text
/// #undef _name_
/// ```
/// where `_name_` matches `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*\s`.
///
/// The lexer behaves as following:
/// - When the lexer comes across anything which matches the `([a-z]|[A-Z]|_)([a-z]|[A-Z]|[0-9]|_)*\s` pattern it
///   produces a [`Ident`](UndefToken::Ident) token.
/// - Anything else produces the [`Invalid`](UndefToken::Invalid) token.
#[derive(Debug, Clone, PartialEq)]
pub enum UndefToken {
	/// An identifier.
	Ident(String),
	/// An invalid character.
	Invalid(char),
}

/// A token representing a unit of text in a `#ifdef`/`#ifndef`/`#if`/`#elif`/`#else`/`#endif` directive.
///
/// # Description of behaviour
/// The GLSL specification defines the following as valid tokens:
/// - integer literals,
/// - identifiers,
/// - `defined` keyword,
/// - specified punctuation symbols.
#[derive(Debug, Clone, PartialEq)]
pub enum ConditionToken {
	/// An integer number.
	Num(usize),
	/// An identifier.
	Ident(String),
	/// An invalid number.
	InvalidNum(String),
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

/// Construct a directive with no tokens, just the keyword.
pub(super) fn construct_empty(
	lexer: &mut Lexer,
	directive_kw: String,
	directive_kw_span: Span,
) -> TokenStream {
	match directive_kw.as_ref() {
		"version" => TokenStream::Version {
			kw: directive_kw_span,
			tokens: vec![],
		},
		"extension" => TokenStream::Extension {
			kw: directive_kw_span,
			tokens: vec![],
		},
		"line" => TokenStream::Line {
			kw: directive_kw_span,
			tokens: vec![],
		},
		"define" => TokenStream::Define {
			kw: directive_kw_span,
			ident_tokens: vec![],
			body_tokens: vec![],
		},
		"undef" => TokenStream::Undef {
			kw: directive_kw_span,
			tokens: vec![],
		},
		"ifdef" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::IfDef {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"ifndef" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::IfNotDef {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"if" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::If {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"elif" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::ElseIf {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"else" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::Else {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"endif" => {
			lexer.metadata.contains_conditional_compilation = true;
			TokenStream::EndIf {
				kw: directive_kw_span,
				tokens: vec![],
			}
		}
		"error" => TokenStream::Error {
			kw: directive_kw_span,
			message: None,
		},
		"pragma" => TokenStream::Pragma {
			kw: directive_kw_span,
			options: None,
		},
		_ => TokenStream::Custom {
			kw: (directive_kw, directive_kw_span),
			content: None,
		},
	}
}

/// Parse a `#version` directive.
pub(super) fn parse_version(
	lexer: &mut Lexer,
	directive_kw_span: Span,
) -> TokenStream {
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	// We continue off from where the lexer previously stopped.
	while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of this word.
						tokens.push((
							VersionToken::Word(std::mem::take(&mut buffer)),
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
					// The character can be part of a word, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of a word, so we can produce a token and exit this loop without
					// consuming it.
					tokens.push((
						VersionToken::Word(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
								VersionToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										VersionToken::Num(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										},
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									VersionToken::InvalidNum(std::mem::take(
										&mut buffer,
									)),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
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
					// The character can't be part of a number. However it requires separation to be valid. Hence
					// this becomes an invalid "number-like" token.
					invalid_num = true;
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					if invalid_num {
						tokens.push((
							VersionToken::InvalidNum(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									VersionToken::Num(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								VersionToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
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
				},
			));
		}
	}

	TokenStream::Version {
		kw: directive_kw_span,
		tokens,
	}
}

/// Parse an `#extension` directive.
pub(super) fn parse_extension(
	lexer: &mut Lexer,
	directive_kw_span: Span,
) -> TokenStream {
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	// We continue off from where the lexer previously stopped.
	while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

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
						ExtensionToken::Word(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
				},
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
				},
			));
		}
	}

	TokenStream::Extension {
		kw: directive_kw_span,
		tokens,
	}
}

/// Parse a `#line` directive.
pub(super) fn parse_line(
	lexer: &mut Lexer,
	directive_kw_span: Span,
) -> TokenStream {
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	// We continue off from where the lexer previously stopped.
	while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

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
							LineToken::Ident(std::mem::take(&mut buffer)),
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
						LineToken::Ident(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
								LineToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										LineToken::Num(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										},
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									LineToken::InvalidNum(std::mem::take(
										&mut buffer,
									)),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
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
							LineToken::InvalidNum(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									LineToken::Num(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								LineToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
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
				},
			));
		}
	}

	TokenStream::Line {
		kw: directive_kw_span,
		tokens,
	}
}

/// Parse the identifier part of a `#define` directive.
pub(super) fn parse_define(lexer: &mut Lexer) -> Vec<Spanned<DefineToken>> {
	let mut tokens = Vec::new();
	// We continue off from where the lexer previously stopped.
	let mut current;
	// Consume whitespace since any whitespace between the `#define` and the `<identifier>` is ignored.
	loop {
		current = match lexer.peek() {
			Some(c) => c,
			None => return vec![],
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			return vec![];
		}

		if current.is_ascii_whitespace() {
			lexer.advance();
			continue;
		} else {
			break;
		}
	}

	if !is_word_start(&current) {
		return vec![];
	}

	let mut buffer = String::new();
	let buffer_start = lexer.position();
	buffer.push(current);
	lexer.advance();
	loop {
		// Peek the current character.
		current = match lexer.peek() {
			Some(c) => c,
			None => {
				// We have reached the end of the source string, and therefore the end of this word and define
				// directive.
				return vec![(
					DefineToken::Ident(std::mem::take(&mut buffer)),
					Span {
						start: buffer_start,
						end: lexer.position(),
					},
				)];
			}
		};

		if is_word(&current) {
			// The character can be part of a word, so we consume it and continue looping.
			buffer.push(current);
			lexer.advance();
		} else if current == '(' {
			// We have encountered a `(` immediately after a word. This means this directive is a function macro
			// and we now need to parse the parameter list.
			tokens.push((
				DefineToken::Ident(std::mem::take(&mut buffer)),
				Span {
					start: buffer_start,
					end: lexer.position(),
				},
			));
			let pos = lexer.position();
			lexer.advance();
			tokens.push((
				DefineToken::LParen,
				Span {
					start: pos,
					end: lexer.position(),
				},
			));
			break;
		} else {
			// We have reached the end of the first word, and have not encountered a `(` immediately afterwards.
			// This means this directive is an object macro and everything from here on is a standard GLSL token.
			return vec![(
				DefineToken::Ident(std::mem::take(&mut buffer)),
				Span {
					start: buffer_start,
					end: lexer.position(),
				},
			)];
		}
	}

	// We have a function macro, and now need to parse the parameter list.
	loop {
		let token_start = lexer.position();
		current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

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
							DefineToken::Ident(std::mem::take(&mut buffer)),
							Span {
								start: token_start,
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
						DefineToken::Ident(std::mem::take(&mut buffer)),
						Span {
							start: token_start,
							end: lexer.position(),
						},
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
				},
			));
		} else if current == ')' {
			lexer.advance();
			tokens.push((
				DefineToken::RParen,
				Span {
					start: token_start,
					end: lexer.position(),
				},
			));
			break;
		} else if current.is_whitespace() {
			// We ignore whitespace characters.
			lexer.advance();
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

	tokens
}

/// Parse an `#undef` directive.
pub(super) fn parse_undef(
	lexer: &mut Lexer,
	directive_kw_span: Span,
) -> TokenStream {
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	// We continue off from where the lexer previously stopped.
	while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

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
							UndefToken::Ident(std::mem::take(&mut buffer)),
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
						UndefToken::Ident(std::mem::take(&mut buffer)),
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
				},
			));
		}
	}

	TokenStream::Undef {
		kw: directive_kw_span,
		tokens,
	}
}

/// Parse a `#ifdef`/`#ifndef`/`#if`/`#elif`/`#else`/`#endif` directive.
pub(super) fn parse_condition(
	lexer: &mut Lexer,
	directive_kw: &str,
	directive_kw_span: Span,
) -> TokenStream {
	let mut tokens = Vec::new();
	let mut buffer = String::new();
	// We continue off from where the lexer previously stopped.
	while !lexer.is_done() {
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
			Some(c) => c,
			None => break,
		};

		if current == '\r' || current == '\n' {
			// We have reached the end of this directive.
			break;
		}

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
								},
							));
							buffer.clear();
						} else {
							tokens.push((
								ConditionToken::Ident(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
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
							},
						));
						buffer.clear();
					} else {
						tokens.push((
							ConditionToken::Ident(std::mem::take(&mut buffer)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
								ConditionToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
							));
						} else {
							match usize::from_str_radix(&buffer, 10) {
								Ok(num) => {
									tokens.push((
										ConditionToken::Num(num),
										Span {
											start: buffer_start,
											end: lexer.position(),
										},
									));
									buffer.clear();
								}
								Err(_) => tokens.push((
									ConditionToken::InvalidNum(std::mem::take(
										&mut buffer,
									)),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
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
							ConditionToken::InvalidNum(std::mem::take(
								&mut buffer,
							)),
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
					} else {
						match usize::from_str_radix(&buffer, 10) {
							Ok(num) => {
								tokens.push((
									ConditionToken::Num(num),
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
								));
								buffer.clear();
							}
							Err(_) => tokens.push((
								ConditionToken::InvalidNum(std::mem::take(
									&mut buffer,
								)),
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
							)),
						}
					}
					break 'number;
				}
			}
		} else if is_condition_punctuation_start(&current) {
			tokens.push((
				match_condition_punctuation(lexer),
				Span {
					start: buffer_start,
					end: lexer.position(),
				},
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
				},
			));
		}
	}

	match directive_kw {
		"ifdef" => TokenStream::IfDef {
			kw: directive_kw_span,
			tokens,
		},
		"ifndef" => TokenStream::IfNotDef {
			kw: directive_kw_span,
			tokens,
		},
		"if" => TokenStream::If {
			kw: directive_kw_span,
			tokens,
		},
		"elif" => TokenStream::ElseIf {
			kw: directive_kw_span,
			tokens,
		},
		"else" => TokenStream::Else {
			kw: directive_kw_span,
			tokens,
		},
		"endif" => TokenStream::EndIf {
			kw: directive_kw_span,
			tokens,
		},
		_ => unreachable!("Only one of the above `&str` values should be passed into this function!"),
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

/// Perform token concatenation on the given token stream.
pub(crate) fn concat_object_macro_body(
	walker: &mut crate::parser::Walker,
	tokens: super::TokenStream,
) -> super::TokenStream {
	use crate::diag::{PreprocDefineDiag, Syntax};

	let mut stack = Vec::new();

	let mut tokens = tokens.into_iter();
	while let Some(token) = tokens.next() {
		if token.0 == super::Token::MacroConcat {
			let previous = stack.pop();
			let next = tokens.next();

			match (previous, next) {
				(Some(prev), Some(next)) => {
					if next.0 == super::Token::MacroConcat {
						// We have something like `foobar ## ##`. We cannot concatenate two concat operators, so we
						// just emit the tokens as-is.
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::TokenConcatMissingRHS(token.1),
						));
						stack.push(prev);
						stack.push((
							super::Token::Invalid('#'),
							token.1.first_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							token.1.last_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							next.1.first_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							next.1.last_char(),
						));
					} else {
						// Panic: The `Token::to_string()` method panics with a directive, however `tokens` is a
						// replacement-list of tokens in a macro and it will never contain any directive tokens
						// within.
						let mut new_string = prev.0.to_string();
						new_string.push_str(&next.0.to_string());
						let mut lexer = Lexer::new(&new_string);
						let mut result = super::parse_tokens(&mut lexer, true);
						stack.append(&mut result);
					}
				}
				(Some(prev), None) => {
					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingRHS(token.1),
					));
					stack.push(prev);
				}
				(None, Some(next)) => {
					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingLHS(token.1),
					));
					if next.0 == super::Token::MacroConcat {
						// We begin the replacement-list with `## ##`. We cannot concatenate two concat operators,
						// so we just emit the tokens as-is.
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::TokenConcatMissingRHS(token.1),
						));
						stack.push((
							super::Token::Invalid('#'),
							token.1.first_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							token.1.last_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							next.1.first_char(),
						));
						stack.push((
							super::Token::Invalid('#'),
							next.1.last_char(),
						));
					}
					stack.push(next);
				}
				(None, None) => {
					// The entire replacement-list is just `##`.
					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingLHS(token.1),
					));
					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingRHS(token.1),
					));
					stack.push((
						super::Token::Invalid('#'),
						token.1.first_char(),
					));
					stack.push((
						super::Token::Invalid('#'),
						token.1.last_char(),
					));
				}
			}
		} else {
			stack.push(token);
		}
	}

	stack
}
