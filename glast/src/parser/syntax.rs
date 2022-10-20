/// A syntax highlighting token.
#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxToken {
	/// A number.
	Num,
	/// A boolean.
	Bool,
	/// An identifier.
	Ident,
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
	/// An object-like macro identifier. This is used at the macro definition site, and at any instances.
	ObjectMacro,
	/// A function-like macro identifier. This is used at the macro definition site, and at any instances.
	FunctionMacro,
	/// The macro concatenation operator.
	MacroConcat,
}
