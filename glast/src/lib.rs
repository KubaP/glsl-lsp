//! *glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.
//!
//! ⚠ This crate is still heavily **work-in-progress**. The main functionality/API of the lexer and parser are
//! roughly finalized, but small changes/tweaks are to be expected and other features are not implemented yet. ⚠
//!
//! This crate is split into modules representing the different stages of parsing/manipulation:
//! - [`lexer`] - Lexer and the token stream.
//! - [`parser`] - Parser and the abstract syntax tree.
//! - `analyzer` - HIR conversion & analysis, such as name resolution (⚠ Currently unimplemented).
//!
//! Only GLSL 450 is currently supported. There are plans to support many more versions, not limited to but
//! including 110 (default), 130, 330, 400, 410, 460 and 100 (es), 300 es & 320 es.
//!
//! This crate is part of a larger effort to provide a high-quality LSP implementation for GLSL. Hence, this crate
//! exposes more than just the basic lexing and parsing functionality found in other crates or libraries for other
//! languages:
//! - The lexer changes the grammar depending on an encountered version directive, in line with the specification.
//! - Lexing/parsing functions produce useful metadata about their inputs.
//! - The parser produces not only an AST, but also syntactical and (some) semantic diagnostics as well as syntax
//!   highlighting information.
//! - The parser correctly expands arbitrarily-complex macros anywhere that it should, in line with the
//!   specification.
//! - The parser is able to correctly deal with all sorts of messed-up-but-technically-valid conditional
//!   compilation. This includes support for optional on-the-fly conditional directive evaluation when selecting
//!   branches.
//!
//! # The parsing pipeline
//! This crate breaks up the individual parsing steps into separate modules that can be invoked individually. The
//! modules are self-contained so if you're, for example, working with the parser, you only need to concern
//! yourself with the `glast::parser` module.
//!
//! This crate operates only on [`str`] inputs because the GLSL specification states that GLSL source strings must
//! use the UTF-8 encoding (hence if the source can be parsed into a valid Rust [`str`] then it must be valid),
//! so no support for `[u8]` inputs is provided.
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
//! This is the next transformation in the parsing pipeline, and it converts the tokenstream into a tree that only
//! contains semantic information, loosing things like irrelevant punctuation symbols or comments.
//!
//! Firstly, conditional compilation is applied to the token stream. Then, the resulting tokenstream is parsed,
//! expanding any macros in the process.
//!
//! The tokenstream would become (in pseudocode):
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
//! type-checking. ⚠ This module is NOT YET IMPLEMENTED
//!
//! # Performance & Testing
//! Currently, this crate has not been particularly optimized for performance; (there is currently a lot of
//! `clone()`-ing). The general internal structure is well suited for optimization, but the work has not currently
//! been done because the internals have undergone numerous large-scale refactors and re-writes whilst the
//! functionality/public api matured. Unless any massive oversights have occurred, the current structure will go
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

pub use span::*;

/// Describes the GLSL version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum GlslVersion {
	/// GLSL 4.50
	_450,
	/// An GLSL version unsupported by the crate.
	#[default]
	// TODO: The default GLSL version in reality is 110, but we currently don't support that.
	Unsupported,
}

impl GlslVersion {
	/// Parses a number into a GLSL version.
	fn parse(num: usize) -> Option<Self> {
		match num {
			450 => Some(Self::_450),
			_ => None,
		}
	}
}

/// Holds either one or the other value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}

/// Holds one of 3 possible values.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Either3<A, B, C> {
	A(A),
	B(B),
	C(C),
}
