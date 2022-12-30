//! *glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.
//!
//! ⚠ This crate is still heavily **work-in-progress**. The main functionality & API of the lexer and parser are
//! roughly finalized, but small changes and tweaks are still to be expected and other features are not implemented
//! yet.
//!
//! This crate is split into modules representing the different stages of parsing/manipulation:
//! - [`lexer`] - Lexer and the token stream.
//! - [`parser`] - Parser and the abstract syntax tree.
//! - `analyzer` - High intermediate representation & analysis, such as name resolution.
//!
//! Only GLSL 450 & 460 are currently supported, but there are plans to support many more versions, not limited to
//! but including 110 (default), 130, 330, 400, 410, and 100 (es), 300 es & 320 es.
//!
//! This crate is part of a larger effort to provide a high-quality LSP implementation for GLSL. Hence, this crate
//! exposes more than just the basic lexing and parsing functionality found in other crates or libraries for other
//! languages:
//! - The lexer changes the grammar depending on an encountered version directive, in line with the specification.
//! - Lexing and parsing functions produce useful metadata about their inputs.
//! - The parser produces not only an AST, but also syntax and (some) semantic diagnostics, as well as syntax
//!   highlighting information.
//! - The parser correctly expands arbitrarily-complex macros anywhere that it should, in line with the
//!   specification.
//! - The parser correctly handles all conditional compilation, no matter how convoluted. Full control over which
//!   conditional branches to include/exclude is provided, include the ability to evaluate conditional directives
//!   on-the-fly.
//!
//! # The parsing pipeline
//! This crate breaks up the individual parsing steps into separate modules that can be invoked individually. The
//! modules are self-contained so if you're, for example, working with the parser, you only need to concern
//! yourself with the `glast::parser` module.
//!
//! This crate operates only on [`str`] inputs because the GLSL specification states that GLSL source strings must
//! use the UTF-8 encoding (hence if the source can be parsed into a valid Rust [`str`] then it must be valid), so
//! no support for `[u8]` inputs is provided.
//!
//! ## Source String
//! We start with a string of characters that makes up the glsl source file. We will use the following example to
//! illustrate the pipeline:
//! ```c
//! // Comment
//! int i = 5.0+1;
//! ```
//!
//! ## Lexer
//! This is the first transformation in the parsing pipeline, and it converts a string of characters into a stream
//! of tokens. The source string would become (in pseudocode):
//! ```text
//! (comment " Comment") (ident "int") (ident "i") (op "=") (float "5.0") (op "+") (int "1") (punct ";")
//! ```
//!
//! ## Parser
//! This is the next transformation in the parsing pipeline, and it converts the token stream into a tree that only
//! contains semantic information, loosing things like irrelevant punctuation symbols or comments.
//!
//! Firstly, conditional compilation is applied to the token stream. Then, the resulting token stream is parsed,
//! expanding any macros in the process.
//!
//! The token stream would become (in pseudocode):
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
//!
//! ## Analyzer
//! This is the final stage of the parsing pipeline, and includes actions such as name resolution and
//! type-checking.
//!
//! ⚠ This module is **not implemented yet**.
//!
//! # Diagnostics
//! The parser produces syntax errors when it encounters invalid syntax. It also produces semantic diagnostics in
//! relation to macros. All other semantic diagnostics are currently waiting on the `analyzer` module to be
//! implemented.
//!
//! For more details, see the [`diag`] module.
//!
//! # Syntax Highlighting
//! The parser produces syntax highlighting tokens as part of the parsing process. These tokens correctly highlight
//! all text that has been parsed, but they are not semantically-aware; this is because the parser only creates an
//! abstract syntax tree, it does not perform name-resolution. This means that currently most identifiers are of
//! the `UncheckedIdent` variant. Once the `analyzer` module has been implemented to include name-resolution
//! functionality, these syntax tokens can be converted into more specific variable/type/function identifiers,
//! which would result in fully semantically-aware highlighting information.
//!
//! For more details, see the [`syntax`] module.
//!
//! # Performance & Testing
//! Currently, this crate has not been particularly optimized for performance; there is a lot of `clone()`-ing. The
//! general internal structure is well suited for optimization, but the work has not yet been done because the
//! internals have undergone numerous large-scale refactors and re-writes whilst the functionality and public api
//! have matured. Unless any massive oversights have occurred, the current structure is the one that will go
//! forward, and once this crate has been given a bit of use to iron out any remaining minor bugs, it will be
//! optimized to minimize data copying/cloning and memory allocations.
//!
//! Currently, this crate does not have extensive testing. Some parts of the crate have good unit test coverage,
//! but other parts lack any tests completely and there are no integration tests yet. This is an important goal
//! which is being progressively worked towards.

pub mod diag;
pub mod lexer;
pub mod parser;
mod span;
pub mod syntax;

pub use span::*;

/// Describes a GLSL version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum GlslVersion {
	/// OpenGL 4.5
	_450,
	/// OpenGL 4.6
	_460,
	/// A GLSL version unsupported by the crate.
	#[default]
	// TODO: The default GLSL version in reality is 110, but we currently don't support that.
	Unsupported,
}

impl GlslVersion {
	/// Parses a number into a GLSL version.
	fn parse(num: usize) -> Option<Self> {
		match num {
			450 => Some(Self::_450),
			460 => Some(Self::_460),
			_ => None,
		}
	}
}

/// Holds either one or the other value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}

/// Holds one of 3 possible values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Either3<A, B, C> {
	A(A),
	B(B),
	C(C),
}
