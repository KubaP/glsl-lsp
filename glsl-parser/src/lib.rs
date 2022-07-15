pub mod ast;
pub mod error;
pub mod expression;
pub mod lexer;
pub mod parser;
pub mod span;

/// Holds either one or the other value.
#[derive(Debug, Clone, PartialEq)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}
