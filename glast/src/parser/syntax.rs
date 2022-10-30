/// A syntax highlighting token.
///
/// This type represents a context-free categorization, i.e. any identifier is given `Ident` and is not checked
/// whether it's valid. For semantic highlighting, name resolution must be done.
#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxToken {
	/// A number.
	Number,
	/// A boolean.
	Boolean,
	/// An identifier that has not gone through name resolution.
	Ident,
	/// An unresolved identifier.
	Unresolved,
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
	/// The macro concatenation operator.
	MacroConcat,
}
