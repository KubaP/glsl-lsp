//! Syntax highlighting types.

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
/// For semantic highlighting purposes, any [`UncheckedIdent`](SyntaxToken::UncheckedIdent) tokens must be
/// name-resolved into a more concrete identifier type. This functionality is currently waiting on the `analyzer`
/// module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxType {
	/// A keyword.
	Keyword,
	/// A punctuation symbol.
	Punctuation,
	/// An operator symbol.
	Operator,
	/// A number.
	Number,
	/// A boolean.
	Boolean,
	//String,
	/// A comment.
	Comment,
	/// A primitive type.
	Primitive,
	/// A struct.
	Struct,
	/// A function.
	Function,
	/// A subroutine.
	Subroutine,
	/// A variable.
	Variable,
	/// A struct member.
	Member,
	/// A function or function-like macro parameter.
	Parameter,
	/// A valid layout qualifier name.
	LayoutQualifier,
	/// An identifier which has not gone through name resolution and never will. This token is only used for any
	/// identifiers within macro bodies.
	Ident,
	/// An unresolved identifier. This could be an unresolved variable name, an unresolved type name, an
	/// invalid layout qualifier name, etc.
	UnresolvedIdent,
	/// An invalid character.
	Invalid,
	/* PREPROCESSOR */
	///// A line-continuator character (`\`).
	//LineContinuator,
	/// An object-like macro identifier. This is used at the macro definition, and at any call sites.
	ObjectMacro,
	/// A function-like macro identifier. This is used at the macro definition, and at any call sites.
	FunctionMacro,
	/// A general bit of text in a directive.
	Directive,
	/// The macro concatenation operator (`##`).
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
	/// The compiler option in a `#pragma` directive.
	DirectivePragma,
}

bitflags! {
	/// The modifiers of a syntax highlighting token.
	///
	/// This is a `bitflag`. It contains:
	/// - `MACRO_SIGNATURE` = `1`,
	/// - `MACRO_BODY` = `2`,
	/// - `UNDEFINE` = `4`,
	/// - `CONDITIONAL` = `8`.
	pub struct SyntaxModifiers: u32 {
		/// Tokens within the macro signature, e.g. the `BAR(A, B)` within `#define BAR(A, B) foo`.
		const MACRO_SIGNATURE = 0b00000001;
		/// Tokens within the macro body, e.g. the `foo + bar` within `#define FOO foo + bar`.
		const MACRO_BODY = 0b00000010;
		/// Tokens within the `#undef` directive; not applied to the `#undef` part.
		const UNDEFINE = 0b00000100;
		/// Tokens within a conditional directive; not applied to the `#if`/`#elif`/etc. part.
		const CONDITIONAL = 0b00001000;
	}
}
