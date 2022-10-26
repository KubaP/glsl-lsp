//! All diagnostic types.
//!
//! Diagnostics are split across two main types:
//! - [`Syntax`] for all syntax/grammar related diagnostics,
//! - [`Semantic`] for all semantic related diagnostics.
//!
//! All diagnostic types have a `get_severity()` method which returns the [`Severity`] of that given diagnostic.

use crate::Span;

/// The severity of a diagnostic.
#[derive(Debug)]
pub enum Severity {
	Error,
	Warning,
}

/// All semantic diagnostics.
pub enum Semantic {
	/// WARNING - Found a macro call site, but the macro contains no replacement tokens.
	///
	/// - `0` - The span of the call site.
	EmptyMacroCallSite(Span),
}

impl Semantic {
	pub fn get_severity(&self) -> Severity {
		match self {
			Semantic::EmptyMacroCallSite(_) => Severity::Warning,
		}
	}
}

/// All syntax diagnostics.
#[derive(Debug)]
#[non_exhaustive]
pub enum Syntax {
	/// Diagnostics for statement.
	Stmt(StmtDiag),

	/// Diagnostics for the `#define` and `#undef` directives.
	PreprocDefine(PreprocDefineDiag),
	/// ERROR - Found trailing tokens in a directive.
	///
	/// - `0` - The span of the tokens.
	PreprocTrailingTokens(Span),
}

impl Syntax {
	pub fn get_severity(&self) -> Severity {
		match self {
			Syntax::Stmt(s) => s.get_severity(),
			Syntax::PreprocDefine(d) => d.get_severity(),
			Syntax::PreprocTrailingTokens(_) => Severity::Error,
		}
	}
}

/// Syntax diagnostics for statement.
#[derive(Debug)]
#[non_exhaustive]
pub enum StmtDiag {
	/// ERROR - Did not find a semi-colon after the `break` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	ExpectedSemiAfterBreakKw(Span),
	/// ERROR - Did not find a semi-colon after the `continue` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	ExpectedSemiAfterContinueKw(Span),
	/// ERROR - Did not find a semi-colon after the `discar` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	ExpectedSemiAfterDiscardKw(Span),
	/// ERROR - Did not find a semi-colon or an expression after the `return` keyword.
	///
	/// - `0` - The span where the semi-colon or expression is expected.
	ExpectedSemiOrExprAfterReturnKw(Span),
	/// ERROR - Did not find a semi-colon after the `return` expression.
	///
	/// - `0` - The span where the semi-colon is expected.
	ExpectedSemiAfterReturnExpr(Span),
}

impl StmtDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			StmtDiag::ExpectedSemiAfterBreakKw(_) => Severity::Error,
			StmtDiag::ExpectedSemiAfterContinueKw(_) => Severity::Error,
			StmtDiag::ExpectedSemiAfterDiscardKw(_) => Severity::Error,
			StmtDiag::ExpectedSemiOrExprAfterReturnKw(_) => Severity::Error,
			StmtDiag::ExpectedSemiAfterReturnExpr(_) => Severity::Error,
		}
	}
}

/// Syntax diagnostics for the `#define` and `#undef` directives.
#[derive(Debug)]
#[non_exhaustive]
pub enum PreprocDefineDiag {
	/* DEFINE */
	/// ERROR - Did not find an identifier token after the `define` keyword.
	///
	/// - `0` - The span where the macro name is expected.
	DefineExpectedMacroName(Span),

	/* TOKEN CONCAT */
	/// ERROR - Found a token concatenator (`##`) with no valid token on the left-hand side. E.g.
	/// ```c
	/// #define FOO ## 0
	/// ```
	/// - `0` - The span of the operator.
	TokenConcatMissingLHS(Span),
	/// ERROR - Found a token concatenator (`##`) with no valid token on the right-hand side. E.g.
	/// ```c
	/// #define FOO 500 ##
	/// #define FOO 90 ## ## 00
	/// ```
	/// - `0` - The span of the operator.
	TokenConcatMissingRHS(Span),

	/* UNDEF */
	/// WARNING - The macro identifier in an undef directive could not be resolved.
	///
	/// - `0` - The span of the identifier.
	UndefMacroNameUnresolved(Span),
	/// ERROR - Did not find an identifier token after the `undef` keyword.
	///
	/// - `0` - The span where the macro name is expected.
	UndefExpectedMacroName(Span),
}

impl PreprocDefineDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			PreprocDefineDiag::DefineExpectedMacroName(_) => Severity::Error,
			PreprocDefineDiag::TokenConcatMissingLHS(_) => Severity::Error,
			PreprocDefineDiag::TokenConcatMissingRHS(_) => Severity::Error,
			PreprocDefineDiag::UndefMacroNameUnresolved(_) => Severity::Warning,
			PreprocDefineDiag::UndefExpectedMacroName(_) => Severity::Error,
		}
	}
}
