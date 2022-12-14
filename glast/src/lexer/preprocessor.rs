//! Types related to preprocessor token streams.
//!
//! This module contains the enums use to represent tokens in the different preprocessor directives.
//!
//! The preprocessor is a single-pass algorithm. This means that a `#define` macro cannot create another
//! preprocessor directive as its output. The token concatenation operator (`##`) is only valid within the macro
//! body of a `#define` directive.
//!
//! # Macro expansion
//! Macros are expanded within the `#line`/`#if` and `#elif` directives only:
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
//! The `#define` macro can nest already-defined macros, but it does not expand them at the definition site:
//! ```c
//! #define FOO 5
//! #define BAR FOO
//!
//! #define FOO 10
//!
//! int i = BAR; // Expands to: int i = 10;
//! ```
//! As you can see, within the `BAR` macro, the `FOO` macro is evaluated but this takes the latest value of `FOO`
//! whenever `BAR` is called. It does not, strictly speaking, expand the `FOO` macro when `BAR` is defined.
//!
//! # Differences from the C preprocessor
//! The GLSL preprocessor is based off the C++98 preprocessor, but it:
//! - Has no support for digraphs or trigraphs.
//! - Has no support for string or character literals, and hence no support for the stringizing operator.
//! - Has no support for universal character names (`\uXXXX` notation).
//! - Has no support for any number literals other than integers, (with no prefixes/suffixes).
//! - Has the extra `version` and `extension` directives, and lacks the `include` directive.
//! - Has a different `line` directive, since GLSL has no concept of filenames.
//! - Has different pre-defined macros, (which depend on the exact GLSL version).

use super::{is_word, is_word_start, Lexer};
use crate::{GlslVersion, Span, Spanned};

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
///   matches the `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern (i.e. a number immediately followed by a word)
///   it produces an [`InvalidNum`](VersionToken::InvalidNum) token.
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
///   token. If it matches the `[0-9]+([a-z]|[A-Z])+([a-z]|[A-Z]|[0-9])*` pattern (i.e. a number immediately
///   followed by a word) it produces an [`InvalidNum`](LineToken::InvalidNum) token.
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
/// - specified punctuation symbols,
/// - comments.
// TODO: Improve the documentation for this.
#[derive(Debug, Clone, PartialEq)]
pub enum ConditionToken {
	/// An integer number.
	Num(usize),
	/// An identifier.
	Ident(String),
	/// A line comment, e.g. `// comment`.
	LineComment(String),
	/// A block comment, e.g. `/* comment */`.
	BlockComment {
		str: String,
		/// Only `true` if this comment is missing the closing delimiter.
		contains_eof: bool,
	},
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
	/// An opening parenthesis `(`.
	LParen,
	/// A closing parenthesis `)`.
	RParen,
	/// A comma `,`.
	Comma,
}

impl ConditionToken {
	/// Produces a syntax token corresponding to the type of this conditional token. This performs simple,
	/// non-semantically-aware colouring.
	pub fn non_semantic_colour(&self) -> crate::parser::SyntaxType {
		use crate::parser::SyntaxType;
		match self {
			ConditionToken::Num(_) => SyntaxType::Number,
			ConditionToken::Ident(_) => SyntaxType::Ident,
			ConditionToken::LineComment(_)
			| ConditionToken::BlockComment { .. } => SyntaxType::Comment,
			ConditionToken::InvalidNum(_) => SyntaxType::Invalid,
			ConditionToken::Invalid(_) => SyntaxType::Invalid,
			ConditionToken::Defined => SyntaxType::Keyword,
			ConditionToken::Add
			| ConditionToken::Sub
			| ConditionToken::Mul
			| ConditionToken::Div
			| ConditionToken::Rem
			| ConditionToken::And
			| ConditionToken::Or
			| ConditionToken::Xor
			| ConditionToken::LShift
			| ConditionToken::RShift
			| ConditionToken::Flip
			| ConditionToken::EqEq
			| ConditionToken::NotEq
			| ConditionToken::Not
			| ConditionToken::Gt
			| ConditionToken::Lt
			| ConditionToken::Ge
			| ConditionToken::Le
			| ConditionToken::AndAnd
			| ConditionToken::OrOr => SyntaxType::Operator,
			ConditionToken::LParen => SyntaxType::Punctuation,
			ConditionToken::RParen => SyntaxType::Punctuation,
			ConditionToken::Comma => SyntaxType::Punctuation,
		}
	}

	/* pub fn from_normal_token(
		   (token, span): &Spanned<super::Token>,
		   new_tokens: &mut Vec<Spanned<Self>>,
	   ) {
		   match token {
			   super::Token::Num { type_, num, suffix } => todo!(),
			   super::Token::Bool(b) => {
				   new_tokens.push((Self::Ident(b.to_string()), *span))
			   }
			   super::Token::Ident(s) => match s.as_ref() {
				   "defined" => new_tokens.push((Self::Defined, *span)),
				   _ => new_tokens.push((Self::Ident(s.clone()), *span)),
			   },
			   super::Token::Directive(d) => unreachable!(),
			   super::Token::MacroConcat => {
				   new_tokens.push((Self::Invalid('#'), span.first_char()));
				   new_tokens.push((Self::Invalid('#'), span.last_char()));
			   }
			   super::Token::LineComment(c) => {
				   new_tokens.push((Self::LineComment(*c), *span))
			   }
			   super::Token::BlockComment { str, contains_eof } => {
				   new_tokens.push((
					   Self::BlockComment {
						   str: *str,
						   contains_eof: *contains_eof,
					   },
					   *span,
				   ));
			   }
			   super::Token::Invalid(c) => {
				   new_tokens.push((Self::Invalid(*c), *span))
			   }
			   super::Token::If
			   | super::Token::Else
			   | super::Token::For
			   | super::Token::Do
			   | super::Token::While
			   | super::Token::Continue
			   | super::Token::Switch
			   | super::Token::Case
			   | super::Token::Default
			   | super::Token::Break
			   | super::Token::Return
			   | super::Token::Discard
			   | super::Token::Struct
			   | super::Token::Subroutine
			   | super::Token::Reserved(_)
			   | super::Token::Const
			   | super::Token::In
			   | super::Token::Out
			   | super::Token::InOut
			   | super::Token::Attribute
			   | super::Token::Uniform
			   | super::Token::Varying
			   | super::Token::Buffer
			   | super::Token::Shared
			   | super::Token::Centroid
			   | super::Token::Sample
			   | super::Token::Patch
			   | super::Token::Layout
			   | super::Token::Flat
			   | super::Token::Smooth
			   | super::Token::NoPerspective
			   | super::Token::HighP
			   | super::Token::MediumP
			   | super::Token::LowP
			   | super::Token::Invariant
			   | super::Token::Precise
			   | super::Token::Coherent
			   | super::Token::Volatile
			   | super::Token::Restrict
			   | super::Token::Readonly
			   | super::Token::Writeonly => {
				   new_tokens.push((Self::Ident(token.to_string()), *span))
			   }
			   super::Token::Op(op) => match op {
				   super::OpTy::Add => new_tokens.push((Self::Add, *span)),
				   super::OpTy::Sub => new_tokens.push((Self::Sub, *span)),
				   super::OpTy::Mul => new_tokens.push((Self::Mul, *span)),
				   super::OpTy::Div => new_tokens.push((Self::Div, *span)),
				   super::OpTy::Rem => new_tokens.push((Self::Rem, *span)),
				   super::OpTy::And => new_tokens.push((Self::And, *span)),
				   super::OpTy::Or => new_tokens.push((Self::Or, *span)),
				   super::OpTy::Xor => new_tokens.push((Self::Xor, *span)),
				   super::OpTy::LShift => new_tokens.push((Self::LShift, *span)),
				   super::OpTy::RShift => new_tokens.push((Self::RShift, *span)),
				   super::OpTy::Flip => new_tokens.push((Self::Flip, *span)),
				   super::OpTy::EqEq => new_tokens.push((Self::EqEq, *span)),
				   super::OpTy::NotEq => new_tokens.push((Self::NotEq, *span)),
				   super::OpTy::Not => new_tokens.push((Self::Not, *span)),
				   super::OpTy::Gt => new_tokens.push((Self::Gt, *span)),
				   super::OpTy::Lt => new_tokens.push((Self::Lt, *span)),
				   super::OpTy::Ge => new_tokens.push((Self::Ge, *span)),
				   super::OpTy::Le => new_tokens.push((Self::Le, *span)),
				   super::OpTy::AndAnd => new_tokens.push((Self::AndAnd, *span)),
				   super::OpTy::OrOr => new_tokens.push((Self::OrOr, *span)),
				   super::OpTy::XorXor => new_tokens.push((Self::XorXor, *span)),
				   super::OpTy::Eq => new_tokens.push((Self::Invalid('='), *span)),
				   super::OpTy::AddAdd => {
					   new_tokens.push((Self::Add, span.first_char()));
					   new_tokens.push((Self::Add, span.last_char()));
				   }
				   super::OpTy::SubSub => {
					   new_tokens.push((Self::Sub, span.first_char()));
					   new_tokens.push((Self::Sub, span.last_char()));
				   }
				   super::OpTy::AddEq => {
					   new_tokens.push((Self::Add, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::SubEq => {
					   new_tokens.push((Self::Sub, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::MulEq => {
					   new_tokens.push((Self::Mul, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::DivEq => {
					   new_tokens.push((Self::Div, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::RemEq => {
					   new_tokens.push((Self::Rem, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::AndEq => {
					   new_tokens.push((Self::And, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::OrEq => {
					   new_tokens.push((Self::Or, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::XorEq => {
					   new_tokens.push((Self::Xor, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::LShiftEq => {
					   new_tokens.push((Self::LShift, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
				   super::OpTy::RShiftEq => {
					   new_tokens.push((Self::RShift, span.first_char()));
					   new_tokens.push((Self::Invalid('='), span.last_char()));
				   }
			   },
			   super::Token::Comma => new_tokens.push((Self::Comma, *span)),
			   super::Token::LParen => new_tokens.push((Self::LParen, *span)),
			   super::Token::RParen => new_tokens.push((Self::RParen, *span)),
			   super::Token::Dot => new_tokens.push((Self::Invalid('.'), *span)),
			   super::Token::Semi => new_tokens.push((Self::Invalid(';'), *span)),
			   super::Token::Colon => new_tokens.push((Self::Invalid(':'), *span)),
			   super::Token::Question => {
				   new_tokens.push((Self::Invalid('?'), *span))
			   }
			   super::Token::LBracket => {
				   new_tokens.push((Self::Invalid('['), *span))
			   }
			   super::Token::RBracket => {
				   new_tokens.push((Self::Invalid(']'), *span))
			   }
			   super::Token::LBrace => {
				   new_tokens.push((Self::Invalid('{'), *span))
			   }
			   super::Token::RBrace => {
				   new_tokens.push((Self::Invalid('}'), *span))
			   }
		   }
	   }
	*/

	/// Converts this token to a standard lexer [`Token`](super::Token) type.
	pub fn to_normal_token(
		(token, span): Spanned<Self>,
	) -> Spanned<super::Token> {
		(
			match token {
				ConditionToken::Num(n) => super::Token::Num {
					type_: super::NumType::Dec,
					num: n.to_string(),
					suffix: None,
				},
				ConditionToken::Ident(s) => super::Token::Ident(s),
				ConditionToken::LineComment(s) => super::Token::LineComment(s),
				ConditionToken::BlockComment { str, contains_eof } => {
					super::Token::BlockComment { str, contains_eof }
				}
				ConditionToken::InvalidNum(s) => {
					// Split the string into the first part that contains any numbers, and the second part that
					// contains anything afterwards.
					let mut num = String::new();
					let mut chars = s.chars();
					for char in chars.next() {
						if char.is_ascii_digit() {
							num.push(char);
						} else {
							break;
						}
					}
					super::Token::Num {
						type_: super::NumType::Dec,
						num,
						suffix: Some(chars.collect()),
					}
				}
				ConditionToken::Invalid(c) => super::Token::Invalid(c),
				ConditionToken::Defined => {
					super::Token::Ident("defined".into())
				}
				ConditionToken::Add => super::Token::Op(super::OpTy::Add),
				ConditionToken::Sub => super::Token::Op(super::OpTy::Sub),
				ConditionToken::Mul => super::Token::Op(super::OpTy::Mul),
				ConditionToken::Div => super::Token::Op(super::OpTy::Div),
				ConditionToken::Rem => super::Token::Op(super::OpTy::Rem),
				ConditionToken::And => super::Token::Op(super::OpTy::And),
				ConditionToken::Or => super::Token::Op(super::OpTy::Or),
				ConditionToken::Xor => super::Token::Op(super::OpTy::Xor),
				ConditionToken::LShift => super::Token::Op(super::OpTy::LShift),
				ConditionToken::RShift => super::Token::Op(super::OpTy::RShift),
				ConditionToken::Flip => super::Token::Op(super::OpTy::Flip),
				ConditionToken::EqEq => super::Token::Op(super::OpTy::EqEq),
				ConditionToken::NotEq => super::Token::Op(super::OpTy::NotEq),
				ConditionToken::Not => super::Token::Op(super::OpTy::Not),
				ConditionToken::Gt => super::Token::Op(super::OpTy::Gt),
				ConditionToken::Lt => super::Token::Op(super::OpTy::Lt),
				ConditionToken::Ge => super::Token::Op(super::OpTy::Ge),
				ConditionToken::Le => super::Token::Op(super::OpTy::Le),
				ConditionToken::AndAnd => super::Token::Op(super::OpTy::AndAnd),
				ConditionToken::OrOr => super::Token::Op(super::OpTy::OrOr),
				ConditionToken::LParen => super::Token::LParen,
				ConditionToken::RParen => super::Token::RParen,
				ConditionToken::Comma => super::Token::Comma,
			},
			span,
		)
	}
}

/// Constructs a directive with no tokens, just the keyword.
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

/// Parses a `#version` directive.
pub(super) fn parse_version(
	lexer: &mut Lexer,
	directive_kw_span: Span,
	is_first_non_comment_token: bool,
) -> (TokenStream, Option<GlslVersion>) {
	let mut tokens = Vec::new();
	let mut buffer = String::new();

	// Whether we are parsing the first number token of this version directive's content.
	let mut first_number = true;
	// This value is returned to the main lexer, which in turn can dynamically set it's own version number if the
	// appropriate circumstances are met.
	let mut version = None;

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
									// This number is the first token after the `#version` keyword. If this
									// directive is also the first non-comment token in the parent lexer, that
									// means this version number (assuming it's a valid GLSL version) should be
									// set.
									if is_first_non_comment_token
										&& first_number
									{
										version = GlslVersion::parse(num);
										first_number = false;
									}

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
								// This number is the first token after the `#version` keyword. If this directive
								// is also the first non-comment token in the parent lexer, that means this version
								// number (assuming it's a valid GLSL version) should be set.
								if is_first_non_comment_token && first_number {
									version = GlslVersion::parse(num);
									first_number = false;
								}

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

	(
		TokenStream::Version {
			kw: directive_kw_span,
			tokens,
		},
		version,
	)
}

/// Parses an `#extension` directive.
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

/// Parses a `#line` directive.
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

/// Parses the identifier part of a `#define` directive.
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

/// Parses an `#undef` directive.
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

/// Parses a `#ifdef`/`#ifndef`/`#if`/`#elif`/`#else`/`#endif` directive.
pub(super) fn parse_condition(
	lexer: &mut Lexer,
	directive_kw: &str,
	directive_kw_span: Span,
) -> TokenStream {
	let tokens = parse_condition_tokens(lexer);
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

/// Parses conditional directive tokens.
pub(crate) fn parse_condition_tokens(
	lexer: &mut Lexer,
) -> Vec<Spanned<ConditionToken>> {
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
		} else if is_conditional_punctuation_start(&current) {
			if lexer.take_pat("//") {
				// If we have a `//`, that means this is a comment until the EOL.
				'line_comment: loop {
					// Peek the current character.
					current = match lexer.peek() {
						Some(c) => c,
						None => {
							// We have reached the end of the source string, and therefore the end of the comment.
							tokens.push((
								ConditionToken::LineComment(std::mem::take(
									&mut buffer,
								)),
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
							ConditionToken::LineComment(std::mem::take(
								&mut buffer,
							)),
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
							ConditionToken::BlockComment {
								str: std::mem::take(&mut buffer),
								contains_eof: false,
							},
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'comment;
					}

					match lexer.peek() {
						Some(current) => {
							if current == '\r' || current == '\n' {
								// We have reached the end of the line, and hence the end of the conditional
								// directive, and therefore the end of the comment. This comment however therefore
								// contains the EOF and hence is not valid.
								tokens.push((
									ConditionToken::BlockComment {
										str: std::mem::take(&mut buffer),
										contains_eof: true,
									},
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
								));
								break 'comment;
							} else {
								buffer.push(current);
								lexer.advance();
							}
						}
						None => {
							// We have reached the end of the source string, and therefore the end of the comment.
							// This comment however therefore contains the EOF and hence is not valid.
							tokens.push((
								ConditionToken::BlockComment {
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
				}
			} else {
				match match_conditional_punctuation(lexer) {
					Some(t) => tokens.push((
						t,
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					)),
					None => {
						// We could have a single `=`, which isn't a valid operator, (unlike in the main lexer).
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
			}
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
	tokens
}

/// Returns whether the character is allowed to start a punctuation token within a conditional directive.
fn is_conditional_punctuation_start(c: &char) -> bool {
	match c {
		'=' | '+' | '-' | '*' | '/' | '%' | '>' | '<' | '!' | '~' | '&'
		| '|' | '^' | '(' | ')' | ',' => true,
		_ => false,
	}
}

macro_rules! match_op {
	($lexer:ident, $str:expr, $token:expr) => {
		if $lexer.take_pat($str) {
			return Some($token);
		}
	};
}

/// Matches a punctuation symbol.
fn match_conditional_punctuation(lexer: &mut Lexer) -> Option<ConditionToken> {
	match_op!(lexer, "==", ConditionToken::EqEq);
	match_op!(lexer, "!=", ConditionToken::NotEq);
	match_op!(lexer, ">=", ConditionToken::Ge);
	match_op!(lexer, "<=", ConditionToken::Le);
	match_op!(lexer, "&&", ConditionToken::AndAnd);
	match_op!(lexer, "||", ConditionToken::OrOr);
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
	match_op!(lexer, ",", ConditionToken::Comma);
	None
}

/// Performs token concatenation on the given token stream.
pub(crate) fn concat_macro_body(
	tokens: super::TokenStream,
) -> (
	super::TokenStream,
	Vec<crate::diag::Syntax>,
	Vec<crate::diag::Semantic>,
) {
	use crate::diag::{PreprocDefineDiag, Semantic, Syntax};

	let mut stack = Vec::new();
	let mut syntax_diags = Vec::new();
	let mut semantic_diags = Vec::new();

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
						syntax_diags.push(Syntax::PreprocDefine(
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
						let mut new_string = prev.0.to_string();
						new_string.push_str(&next.0.to_string());
						let mut lexer = Lexer::new(&new_string);
						let mut result =
							super::parse_tokens(&mut lexer, true, false);
						if result.len() == 1 {
							// We have successfully concatenated. Since the lexer starts off at 0, we need to
							// modify the span to be correct.
							let (token, _) = result.remove(0);
							stack.push((
								token,
								Span::new(prev.1.start, next.1.end),
							));
						} else {
							// We had two tokens which didn't concatenate, so we can just push them back into the
							// stack as-is.
							semantic_diags.push(
								Semantic::TokenConcatUnnecessary(token.1),
							);
							stack.push(prev);
							stack.push(next);
						}
					}
				}
				(Some(prev), None) => {
					syntax_diags.push(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingRHS(token.1),
					));
					stack.push(prev);
				}
				(None, Some(next)) => {
					syntax_diags.push(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingLHS(token.1),
					));
					if next.0 == super::Token::MacroConcat {
						// We begin the replacement-list with `## ##`. We cannot concatenate two concat operators,
						// so we just emit the tokens as-is.
						syntax_diags.push(Syntax::PreprocDefine(
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
					syntax_diags.push(Syntax::PreprocDefine(
						PreprocDefineDiag::TokenConcatMissingLHS(token.1),
					));
					syntax_diags.push(Syntax::PreprocDefine(
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

	(stack, syntax_diags, semantic_diags)
}
