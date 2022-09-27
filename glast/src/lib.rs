//! *glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.
//!
//! ⚠ This crate is still heavily **work-in-progress**. It can't correctly deal with all glsl 4.50/4.60 language
//! constructs yet, and the `ast` module is mostly empty. ⚠
//!
//! This crate is split into modules representing the different stages of parsing:
//! - `token` - token stream produced by the lexer,
//! - `cst` - concrete syntax tree produced as an intermediate step of the parser,
//! - `ast` - abstract syntax tree produced as the final output of the parser.
//!
//! You can invoke a specific parsing stage individually, such as calling
//! [`glast::token::parse_from_str()`](self::token::parse_from_str()) or
//! [`glast::cst::parse_from_token_stream()`](self::cst::parse_from_token_stream()) and chaining them however you
//! need, or you can invoke all of the stages automatically by calling a function such as
//! [`glast::cst::parse_from_str()`](self::cst::parse_from_str()).
//!
//! ## The parsing pipeline
//! This crate breaks up the individual parsing steps into separate modules which can be invoked individually. The
//! modules are self-contained so if you're for example working with the abstract syntax tree, you only need to
//! concern yourself with the `glast::ast` module.
//!
//! ### Source String
//! We start with a string of characters that makes up the glsl source file. We will use the following example to
//! illustrate the pipeline:
//! ```c
//! // Comment
//! int i = 5.0+1;
//! ```
//!
//! ### Token Stream
//! This is the first transformation in the parsing pipeline, and it converts a string of characters into a list of
//! tokens. The source string would become (in pseudocode):
//! ```text
//! (comment " Comment") (ident "int") (ident "i") (op "=") (float "5.0") (op "+") (int "1") (punct ";")
//! ```
//!
//! ### Concrete Syntax Tree
//! This is the second transformation in the parsing pipeline, and it converts a list of tokens into a structured
//! tree that still preserves all of the syntactical information. The token stream would become (in pseudocode):
//! ```text
//! VariableDeclaration {
//!     comment_before: " Comment",
//!     type: "int",
//!     ident: "i",
//!     eq: "=",
//!     value: BinaryExpression {
//!         left: "5.0",
//!         op: "+",
//!         right: "1"
//!     },
//!     semi: ";"
//! }
//! ```
//!
//! ### Abstract Syntax Tree
//! This is the final transformation in the parsing pipeline, and it converts a concrete syntax tree into a tree
//! that only contains semantic information, loosing things like irrelevant punctuation symbols or comments. The
//! concrete syntax tree would become (in pseudocode):
//! ```text
//! VariableDeclaration {
//!     type: Primitive.Int,
//!     ident: IdentifierHandle, // points to some lookup hashmap of symbol names
//!     value: BinaryExpression {
//!         left: Float(5.0),
//!         op: Addition,
//!         right: Int(1),
//!     }
//! }
//! ```

pub mod ast;
pub mod cst;
pub mod error;
mod span;
pub mod token;

pub use span::*;

/// Holds either one or the other value.
#[derive(Debug, Clone, PartialEq)]
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
