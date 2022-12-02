use crate::Span;
use bitflags::bitflags;

/// A syntax highlighting token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyntaxToken {
	/// The syntax token type.
	pub ty: SyntaxType,
	/// Any optional modifiers. If there are none, `modifiers.is_empty()` will return `true`.
	pub modifiers: SyntaxModifiers,
	/// The span.
	pub span: Span,
}

/// The type of syntax highlighting token.
///
/// For semantic highlighting, any [`UncheckedIdent`](SyntaxToken::UncheckedIdent) tokens must be name-resolved
/// into a more concrete token type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxType {
	/// A keyword.
	Keyword,
	/// A punctuation symbol.
	Punctuation,
	/// An operator symbol.
	Operator,
	/// A function or function-like macro parameter.
	Parameter,
	/// A valid layout qualifier identifier.
	LayoutQualifier,
	/// A number.
	Number,
	/// A boolean.
	Boolean,
	/// A comment.
	Comment,
	/// An identifier which has not gone through name resolution.
	UncheckedIdent,
	/// An unresolved identifier. This could be an unresolved variable ident, an unresolved type name, or an
	/// illegal layout ident.
	UnresolvedIdent,
	/// An invalid character.
	Invalid,
	/* PREPROCESSOR */
	/// An object-like macro identifier. This is used at the macro definition site, and at any call sites.
	ObjectMacro,
	/// A function-like macro identifier. This is used at the macro definition site, and at any call sites.
	FunctionMacro,
	/// An identifier which has not gone through name resolution and never will. This token is only used for any
	/// identifiers within macro bodies.
	Ident,
	/// A general bit of text in a directive.
	Directive,
	/// The macro concatenation operator.
	DirectiveConcat,
	/// The hash `#` symbol in a directive.
	DirectiveHash,
	/// The name of the directive, e.g. `version` or `ifdef`.
	DirectiveName,
	/// The GLSL version in a `#version` directive.
	DirectiveVersion,
	/// The GLSL profile in a `#version` directive.
	DirectiveProfile,
	/// The extension name in a `#extension` directive.
	DirectiveExtName,
	/// The extension behaviour in a `#extension` directive.
	DirectiveExtBehaviour,
	/// The line number in a `#line` directive.
	DirectiveLineNumber,
	/// The message in an `#error` directive.
	DirectiveError,
}

bitflags! {
	/// The syntax highlighting modifiers.
	///
	/// This is a `bitflag`.
	pub struct SyntaxModifiers: u32 {
		/// Tokens within the macro definition, e.g. `BAR(A, B)`
		const MACRO_DEFINITION = 0b00000001;
		/// Tokens within the macro body (replacement token list).
		const MACRO_BODY = 0b00000010;
		/// Tokens within the `#undef` directive.
		const UNDEFINE = 0b00000100;
		/// Tokens within a conditional directive.
		const CONDITIONAL = 0b00001000;
	}
}
