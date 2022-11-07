//! *glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.
//!
//! ⚠ This crate is still heavily **work-in-progress**. It can't correctly deal with all GLSL 4.50/4.60 language
//! constructs yet. ⚠
//!
//! This crate is split into modules representing the different stages of parsing/manipulation:
//! - [`lexer`] - All things related to the lexer.
//! - [`parser`] - All things related to the parser.
//! - `analyzer` - AST analysis, such as name resolution (⚠ Currently unimplemented).
//!
//! You can invoke a specific parsing stage individually, such as calling
//! [`glast::lexer::parse_from_str()`](crate::lexer::parse_from_str()) or
//! [`glast::parser::parse_from_token_stream()`](crate::parser::parse_from_token_stream()) and chaining them
//! however you need, or you can invoke all of the necessary stages automatically by calling a function such as
//! [`glast::parser::parse_from_str()`](crate::parser::parse_from_str()).
//!
//! ## The parsing pipeline
//! This crate breaks up the individual parsing steps into separate modules which can be invoked individually. The
//! modules are self-contained so if you're for example working with the parser, you only need to concern yourself
//! with the `glast::parser` module.
//!
//! This crate operates only on [`str`] inputs because the GLSL specification states that GLSL source strings must
//! use the UTF-8 encoding (so if the source can be parsed into a valid Rust [`str`] then it must be valid), hence
//! no support for `[u8]` inputs is provided.
//!
//! ### Source String
//! We start with a string of characters that makes up the glsl source file. We will use the following example to
//! illustrate the pipeline:
//! ```c
//! // Comment
//! int i = 5.0+1;
//! ```
//!
//! ### Lexer
//! This is the first transformation in the parsing pipeline, and it converts a string of characters into a stream
//! of tokens. The source string would become (in pseudocode):
//! ```text
//! (comment " Comment") (ident "int") (ident "i") (op "=") (float "5.0") (op "+") (int "1") (punct ";")
//! ```
//!
//! ### Parser
//! This is the next transformation in the parsing pipeline, and it converts the tokenstream into a tree that only
//! contains semantic information, loosing things like irrelevant punctuation symbols or comments. The tokenstream
//! would become (in pseudocode):
//! ```text
//! VariableDeclaration {
//!     type: Primitive.Int,
//!     ident: Identifier("i"),
//!     value: BinaryExpression {
//!         left: Float(5.0),
//!         op: Addition,
//!         right: Int(1),
//!     }
//! }
//! ```

pub mod diag;
pub mod lexer;
pub mod parser;
mod span;

pub use span::*;

/// Holds either one or the other value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}

/// Logs a message to the screen.
#[cfg(feature = "logging")]
macro_rules! log {
	($($rest:tt)*) => {
		::std::println!($($rest)*)
	};
}

/// Logs a message to the screen, (current disabled without the `logging` feature).
#[cfg(not(feature = "logging"))]
macro_rules! log {
	($($tts:tt)*) => {{}};
}

pub(crate) use log;
