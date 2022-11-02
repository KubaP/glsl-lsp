/// A syntax highlighting token.
///
/// For semantic highlighting, any [`UncheckedIdent`](SyntaxToken::UncheckedIdent) tokens must be name-resolved
/// into a more concrete identifier token type.
#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxToken {
	/// A number.
	Number,
	/// A boolean.
	Boolean,
	/// An identifier which has not gone through name resolution.
	UncheckedIdent,
	/// A valid layout identifier.
	LayoutIdent,
	/// An unresolved identifier. This could be an unresolved variable ident, an unresolved type name, or an
	/// illegal layout ident.
	UnresolvedIdent,
	/// A keyword.
	Keyword,
	/// A punctuation symbol.
	Punctuation,
	/// An operator symbol.
	Operator,
	/// A comment.
	Comment,
	/// An invalid character.
	Invalid,
	/* PREPROCESSOR */
	/// A directive.
	Directive,
	/// An object-like macro identifier. This is used at the macro definition site, and at any call sites.
	ObjectMacro,
	/// A function-like macro identifier. This is used at the macro definition site, and at any call sites.
	FunctionMacro,
	/// An identifier which has not gone through name resolution and never will. This token is only used for any
	/// identifiers within macro bodies.
	Ident,
	/// The macro concatenation operator.
	MacroConcat,
}
