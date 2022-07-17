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
