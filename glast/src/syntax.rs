//! Syntax highlighting types.
//! TODO: rename module to `highlight`, and remove syntax references to not confuse with other syntax meaning

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
	/// A subroutine type name.
	SubroutineType,
	/// An interface block name. **This is not** the name of an instance of an interface block, but of the block
	/// itself.
	InterfaceBlock,
	/// A function.
	Function,
	/// A subroutine.
	Subroutine,
	/// A variable.
	Variable,
	/// A struct field.
	Field,
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
	/// An object-like macro name. This is used at the macro definition and at call sites.
	ObjectMacro,
	/// A function-like macro name. This is used at the macro definition and at call sites.
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
	String,
}

bitflags! {
	/// The modifiers for a syntax highlighting token.
	///
	/// For a more detailed breakdown of where modifiers are used, see: TODO (document)
	///
	/// This is a `bitflag`. It contains: TODO
	pub struct SyntaxModifiers: u32 {
		/* === PREPROCESSOR === */
		/// Tokens within the `#version` directive, apart from the `#version` part.
		const VERSION = 1;
		/// Tokens within the `#extension` directive, apart from the `#extension` part.
		const EXTENSION = 2;
		/// Tokens within the `#line` directive, apart from the `#line` part.
		const LINE = 4;
		/// Tokens within the macro signature within a `#define` directive, e.g. the `BAR(A, B)` within `#define
		/// BAR(A, B) foo`.
		const MACRO_SIGNATURE = 8;
		/// Tokens within the macro body within a `#define` directive, e.g. the `foo + bar` within `#define FOO foo
		/// + bar`.
		const MACRO_BODY = 16;
		/// Tokens within a macro call site.
		const MACRO_CALLSITE = 32;
		/// Tokens within the `#undef` directive, apart from the `#undef` part.
		const UNDEF = 64;
		/// Tokens within the `#error` directive, apart from the `#error` part.
		const ERROR = 128;
		/// Tokens within the `#pragma` directive, apart from the `#pragma` part.
		const PRAGMA = 256;
		/// Tokens within a conditional directive, apart from the `#if`/`#elif`/etc. part.
		const CONDITIONAL = 0;
		/* === GENERAL === */
		const DECLARATION = 0;
		const DEFINITION = 0;
	}
}
