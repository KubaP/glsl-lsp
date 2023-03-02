//! All diagnostic types.
//!
//! Diagnostics are split across two main types:
//! - [`Syntax`] for all syntax/grammar-related diagnostics,
//! - [`Semantic`] for all semantics-related diagnostics.
//!
//! All diagnostic types are marked `#[non_exhaustive]` to allow for new diagnostics to be introduced without a
//! breaking change. All diagnostic types have a `get_severity()` method which returns the [`Severity`] of that
//! given diagnostic. Syntax diagnostics only return `Severity::Error`.
//!
//! There are a *lot* of individual syntax diagnostics for all sorts of edge cases. This approach was chosen in
//! order to provide very specific and precise diagnostics without having to hardcode `&'static` strings
//! everywhere. In order to make the amount more managable, most diagnostics are split into nested enums.

use crate::{parser::ast, Span, Spanned};

/// The severity of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
	Error,
	Warning,
}

/// All semantic diagnostics.
///
/// Error diagnostics also have an associated error code.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Semantic {
	/* NAME RESOLUTION */
	/// E??? - When registering a new function symbol, we found a name that is a built-in function. You cannot
	/// overload built-in functions.
	CannotOverloadBuiltInFn { name: ast::Ident },
	/// E003 - A typename could not be found.
	UnresolvedType {
		ty: Spanned<String>,
		/// TODO:
		later_match: Option<Span>,
	},
	/// E003 - A subroutine typename could not be found.
	UnresolvedSubroutineType {
		ty: Spanned<String>,
		/// TODO:
		later_match: Option<String>,
	},
	/// E003 - A variable name could not be found.
	UnresolvedVariable {
		/// The variable, part of an expression.
		var: Spanned<String>,
		/// The span of the later variable definition statement.
		later_match: Option<Span>,
	},
	/// E003 - A function name could not be found. A function name is checked against existing functions, structs,
	/// or subroutine uniforms.
	UnresolvedFunction {
		/// The function, part of an expression.
		fn_: Spanned<String>,
		/// The span of the later function definition statement.
		later_match: Option<Span>,
	},
	/// E003 - A struct field name could not be found.
	UnresolvedStructField {
		/// The field, part of an expression.
		field: Spanned<String>,
		/// The name of the struct.
		struct_name: String,
		/// The span of the definition node.
		struct_def: Span,
	},
	/// E004 - A name is already in use and cannot shadow an existing item. Note that this excludes
	/// primitive typenames; for those the [`Syntax2::ExpectedNameFoundPrimitive`] error is emitted instead.
	NameAlreadyInUse {
		name: String,
		/// The new name (the span is of the name in the new declaration/definition).
		new: (NameTy, Span),
		/// The existing name (the span is of the name in the existing declaration/definition).
		existing: (NameTy, Span),
	},
	/// E006 - Found a dot-operator on a primitive type that doesn't support it. The only primitive types that
	/// support dot-operator access are vector types, that allow swizzling.
	InvalidFieldAccessOnPrimitive {
		/// The field trying to be accessed.
		field: Spanned<String>,
		/// The type of the LHS expression of the dot-operator.
		typename: String,
	},
	/// E007 - Found an invalid vector swizzle. This is for fields that aren't even valid swizzles.
	InvalidFieldAccessOnVector {
		/// The field trying to be accessed.
		field: Spanned<String>,
		/// The type of the vector.
		typename: String,
	},
	/// E007 - Found an invalid vector swizzle. This is for swizzles that use dimensions that do not exist on the
	/// vector type.
	VectorSwizzleInvalidDim {
		/// The swizzle.
		swizzle: Spanned<String>,
		/// The type of the vector.
		typename: String,
		/// The dimension number of the invalid component.
		component_dim: usize,
		/// The invalid dimension component.
		invalid_component: char,
	},
	/// E007 - Found an invalid vector swizzle. This is for swizzles that have too many components.
	VectorSwizzleTooLarge {
		/// The swizzle.
		swizzle: Spanned<String>,
		/// The number of components in the swizzle.
		size: usize,
	},
	/// E007 - Found an invalid vector swizzle. This is for swizzles that mix-and-match notations. Note that if all
	/// three notations are used, only the mismatch between the last two will be reported.
	VectorSwizzleMixedNotation {
		/// The swizzle.
		swizzle: Spanned<String>,
		first_notation: &'static str,
		second_notation: &'static str,
	},
	/// E - Found a method call. Methods, apart from a handful of built-in exemptions, are not a language
	/// feature.
	InvalidMethod(Span),
	/// E - Found a `length()` method call on a type that does not support it.
	LengthMethodNotOnValidType(Span),
	/* SUBROUTINES */
	/// E005 - A subroutine uniform variable was found in an expression without parenthesis. Subroutine uniforms,
	/// whilst defined like variables, are treated like functions and need to be called.
	SubUniformTreatedAsVariable {
		/// The variable, part of an expression.
		var: Spanned<String>,
	},
	/// E - Found a normal type specifier in a subroutine uniform definition.
	SubUniformFoundNormalType(Span),
	/// E - Found a subroutine type specifier in a subroutine type declaration.
	SubTypeFoundSubType(Span),
	/// E - Found a subroutine type specifier in an associated subroutine function definition.
	SubFnFoundSubType(Span),
	/* PREPROCESSOR */
	/// WARNING - Found an empty preprocessor directive.
	///
	/// - `0` - The span of the line containing the directive.
	EmptyDirective(Span),
	/* MACROS */
	/// WARNING - A macro call site was found to expand to nothing.
	///
	/// Note that the reason we don't check for empty macro definitions is because an empty macro may be used
	/// within a conditional directive, and that should not be a warning.
	EmptyMacroCallSite { call_site: Span },
	/// E001 - A mismatch was found between the number of arguments in a function-like macro call and the number of
	/// parameters in the macro definition.
	FunctionMacroMismatchedArgCount {
		/// The span of the macro call site.
		call_site: Span,
		/// The number of arguments.
		no_of_args: usize,
		/// The number of expected parameters.
		no_of_params: usize,
		/// The span of the macro's signature.
		def: Span,
	},
	/// WARNING - Found a token concatenation operator that is unnecessary.
	UnnecessaryTokenConcat { op: Span },
	/// WARNING - The macro name within an `#undef` directive could not be found.
	UndefMacroNameUnresolved { name: Spanned<String> },
}

impl Semantic {
	/// Returns the severity of a diagnostic.
	pub fn severity(&self) -> Severity {
		match self {
			/* NAME RESOLUTION */
			Self::UnresolvedType { .. } => Severity::Error,
			Self::UnresolvedSubroutineType { .. } => Severity::Error,
			Self::UnresolvedVariable { .. } => Severity::Error,
			Self::UnresolvedFunction { .. } => Severity::Error,
			Self::UnresolvedStructField { .. } => Severity::Error,
			Self::NameAlreadyInUse { .. } => Severity::Error,
			Self::InvalidFieldAccessOnPrimitive { .. } => Severity::Error,
			Self::InvalidFieldAccessOnVector { .. } => Severity::Error,
			Self::VectorSwizzleInvalidDim { .. } => Severity::Error,
			Self::VectorSwizzleTooLarge { .. } => Severity::Error,
			Self::VectorSwizzleMixedNotation { .. } => Severity::Error,
			/* SUBROUTINES */
			Self::SubUniformTreatedAsVariable { .. } => Severity::Error,
			Self::SubUniformFoundNormalType(_) => Severity::Error,
			Self::SubTypeFoundSubType(_) => Severity::Error,
			Self::SubFnFoundSubType(_) => Severity::Error,
			/* PREPROCESSOR */
			Self::EmptyDirective(_) => Severity::Warning,
			/* MACROS */
			Self::EmptyMacroCallSite { .. } => Severity::Warning,
			Self::FunctionMacroMismatchedArgCount { .. } => Severity::Error,
			Self::UnnecessaryTokenConcat { .. } => Severity::Warning,
			Self::UndefMacroNameUnresolved { .. } => Severity::Warning,
			_ => Severity::Error,
		}
	}

	/// Returns an error code of a diagnostic. Only error diagnostics will return `Some`.
	pub fn error_code(&self) -> Option<&'static str> {
		match self {
			/* NAME RESOLUTION */
			Self::UnresolvedType { .. }
			| Self::UnresolvedSubroutineType { .. }
			| Self::UnresolvedVariable { .. }
			| Self::UnresolvedFunction { .. }
			| Self::UnresolvedStructField { .. } => Some("E003"),
			Self::NameAlreadyInUse { .. } => Some("E004"),
			Self::InvalidFieldAccessOnPrimitive { .. } => Some("E006"),
			Self::InvalidFieldAccessOnVector { .. }
			| Self::VectorSwizzleInvalidDim { .. }
			| Self::VectorSwizzleTooLarge { .. }
			| Self::VectorSwizzleMixedNotation { .. } => Some("E007"),
			/* SUBROUTINES */
			Self::SubUniformTreatedAsVariable { .. } => Some("E005"),
			/* MACROS */
			Self::FunctionMacroMismatchedArgCount { .. } => Some("E001"),
			_ => None,
		}
	}
}

/// The type of a name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameTy {
	Struct,
	InterfaceBlock,
	Function,
	SubroutineType,
	SubroutineUniform,
	Variable,
}

/// A syntax error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Syntax2 {
	/// Missing a punctuation symbol that would make a grammar item fully valid. For the purposes of
	/// parsing, this punctuation symbol has been infered and the relevant grammar item parsed. Some examples:
	/// ```text
	/// foo + bar
	///          ^ missing `;` to make this a valid expression statement
	///
	/// void foo(int bar ;
	///                 ^ missing `)` to make this a valid parameter list
	///
	/// void foo(int i float);
	///               ^ missing a `,` to make this a valid parameter list
	/// ```
	MissingPunct {
		/// The missing character.
		char: char,
		/// The position where it should be inserted at.
		pos: usize,
		/// The parser context.
		ctx: DiagCtx,
	},
	/// Found a piece of grammar that needs removal to make a grammar item fully valid. For the purposes of
	/// parsing, this piece of grammar has been assumed to not exist in order to parse a "closest-match" grammar
	/// item. Some examples:
	/// ```text
	/// in subroutine from_vert { vec4 color; };
	///    ~~~~~~~~~~ removing makes this a valid interface block definition
	///
	/// void foo(int i + 7, float f);
	///              ~~~~~ removing makes this a valid parameter list
	/// ```
	ForRemoval {
		/// The item to remove.
		item: ForRemoval,
		/// The span of the text.
		span: Span,
		/// The parser context.
		ctx: DiagCtx,
	},
	/// Missing some grammar to make a valid grammar item. The missing piece of grammar may be one of a few
	/// possibilities if the flexiblity allows for multiple possible grammar items. For the purposes of aprsing,
	/// this piece of grammar has **not** been assumed to exist because it's not obvious what it should be, and
	/// parsing of that grammar item has been aborted. Some examples:
	/// ```text
	/// subroutine
	///           ^ there are 3 options for missing grammar that could result in
	///             a subroutine type declaration, subroutine function definition,
	///             or a subroutine uniform definition
	///
	/// subroutine uniform
	///                   ^ there is only one option that makes sense,
	///                     a type specifier for the uniform definition
	///
	/// void foo(int i, , float f);
	///                ^ expected a type specifier for a parameter
	/// ```
	ExpectedGrammar {
		/// The expected grammar.
		item: ExpectedGrammar,
		/// The position where the item should be inserted at.
		/// MAYBE: Allow for a span for slightly nicer error squiggles in certain cases?
		pos: usize,
	},
	/// Found a piece of grammar that is in an incorrect order.
	IncorrectOrder {
		/// TODO: Once we have a better idea of how often this case crops up, we can consider a typed enum.
		msg: &'static str,
		/// The span of the text that needs to be moved.
		span: Span,
		// MAYBE: Store position text should be moved to?
	},
	/// Found a statement that can only appear in the top-level scope. Some examples:
	/// ```text
	/// void main() {
	///     subroutine uniform my_condition condition;
	///     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
	///       not allowed in nested scope
	/// }
	/// ```
	NotAllowedInNestedScope {
		/// The type of statement.
		stmt: StmtType,
		/// The span of the statement.
		span: Span,
	},
	ExpectedNameFoundPrimitive(Span),
	/// Expression-related syntax diagnostics.
	Expr(ExprDiag),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagCtx {
	/// The parser is within a standalone expression statement.
	ExprStmt,
	/// The parser is within an interface block definition.
	InterfaceBlockDef,
	/// The parser is analyzing an interface field definition.
	InterfaceField,
	/// The parser is within a parameter list.
	ParamList,
	/// The parser is within an association list.
	AssociationList,
	/// The parser is within a variable definition.
	VarDef,
	/// The parser is within a function declaration.
	FnDecl,
	/// The parser is looking for something subroutine related, but what exactly it's not certain yet.
	Subroutine,
	/// The parser is within a subroutine uniform definition.
	SubroutineUniform,
	/// The parser is within a subroutine type declaration.
	SubroutineType,
	/// The parser is within an associated subroutine function.
	SubroutineAssociatedFn,
	/// The parser is within a struct definition.
	StructDef,
	/// The parser is analyzing a struct field definition.
	StructField,
	/// The parser is within an fuction macro argument list.
	FunctionMacroArgList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForRemoval {
	/// We need to remove something that isn't a well-defined grammar item. This is sometimes generated when
	/// searching for a landmark.
	Something,
	/// A singular keyword.
	Keyword(&'static str),
	/// A subroutine association list.
	AssociationList,
	/// An expression.
	Expr,
	/// The initialization part of a variable specifier.
	VarInitialization,
	/// The `[second..=last]` variable specifiers in the situation that there is more than one.
	MultipleVarSpecifiers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedGrammar {
	/// A keyword.
	Keyword(&'static str),
	/// Something after qualifiers. Could be one of:
	/// - a type specifier for a variable definition or function declaration/definition,
	/// - a semi-colon for just a set of qualifiers on their own.
	AfterQualifiers,
	/// Something after a type specifier. Could be one of:
	/// - a new variable specifier for a variable definition,
	/// - an identifier and opening parenthesis for a function declaration or definition.
	/// - a semi-colon for just a type specifier on its own.
	AfterType,
	/// Something after subroutine qualifiers. Could be one of:
	/// - a type specifier for a subroutine type declaration or an associated function definition,
	/// - a subroutine type specifier for a subroutine uniform definition.
	AfterSubroutineQualifiers,
	/// Something after a type specifier in a subroutine-related statement. Could be one of:
	/// - a new variable specifier for a subroutine uniform,
	/// - an identifier and opening parenthesis for a subroutine type declaration or an  associated function
	///   definition.
	AfterSubroutineType,
	/// A struct name after the `struct` keyword.
	AfterStructKw,
	/// A new variable specifier after a (subroutine) type specifier.
	NewVarSpecifier,
	/// A parameter.
	Parameter,
	/// A struct field.
	StructField,
	/// An interface field.
	InterfaceField,
	/// A subroutine association list.
	AssociationList,
	/// A subroutine typename, **not specifier**.
	SubroutineTypename,
	/// One or more specific qualifiers before an interface block definition.
	QualifierBeforeInterfaceBlock,
	/// The end punctuation of a block comment (`*/`).
	BlockCommentEnd,
	/// Something on the LHS of a token concatenator.
	TokenConcatLHS,
	/// Something on the RHS of a token concatenator.
	TokenConcatRHS,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StmtType {
	/// A function declaration.
	FnDecl,
	/// A function definition.
	FnDef,
	/// A struct definition.
	Struct,
	/// An interface block definition.
	Interface,
	/// A subroutine type declaration.
	SubType,
	/// A subroutine uniform definition.
	SubUniform,
}

/// All syntax diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Syntax {
	/// Diagnostics for expressions.
	Expr(ExprDiag),
	/// Diagnostics for statement.
	Stmt(StmtDiag),
	/// ERROR - Found an illegal character that is not part of the GLSL character set.
	///
	/// - `0` - The span of the character.
	/// - `1` - The character.
	FoundIllegalChar(Span, char),
	/// ERROR - Found a reserved keyword.
	///
	/// - `0` - The span of the keyword.
	/// - `1` - The keyword as a string.
	FoundReservedKw(Span, String),
	/// ERROR - Found a trailing closing brace that doesn't match-up with an opening brace.
	///
	/// - `0` - The span of the closing brace.
	FoundUnmatchedRBrace(Span),
	/// ERROR - Found an `else` keyword outside of an if statement.
	///
	/// - `0` - The span of the keyword.
	FoundLonelyElseKw(Span),
	/// ERROR - Found a `case` keyword outside of a switch statement.
	///
	/// - `0` - The span of the keyword.
	FoundLonelyCaseKw(Span),
	/// ERROR - Found a `default` keyword outside of a switch statement.
	///
	/// - `0` - The span of the keyword.
	FoundLonelyDefaultKw(Span),
	/// ERROR - Found a block comment that is missing the closing tag (`*/`).
	///
	/// - `0` - The position where the closing tag is expected.
	BlockCommentMissingEnd(Span),
	/// Diagnostics for the `#version` directive.
	PreprocVersion(PreprocVersionDiag),
	/// Diagnostics for the `#extension` directive.
	PreprocExt(PreprocExtDiag),
	/// Diagnostics for the `#line` directive.
	PreprocLine(PreprocLineDiag),
	/// Diagnostics for the `#define` and `#undef` directives.
	PreprocDefine(PreprocDefineDiag),
	/// Diagnostics for the conditional directives.
	PreprocConditional(PreprocConditionalDiag),
	/// ERROR - Found trailing tokens in a directive.
	///
	/// - `0` - The span of the tokens.
	PreprocTrailingTokens(Span),
	/// ERROR - Found an illegal preprocessor directive.
	///
	/// - `0` - The span of the directive.
	/// - `1` - The initial keyword and its span, if there is one.
	FoundIllegalPreproc(Span, Option<Spanned<String>>),
}

/// Syntax diagnostics for expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExprDiag {
	/* LITERALS */
	/// Found a number that has a prefix/suffix but no content. Some examples:
	/// ```text
	/// 0xu
	///   ^ nothing between the prefix `0x` and suffix `u`
	/// ```
	EmptyNumber(Span),
	/// Found a number that has an invalid suffix.
	/// ```text
	/// 500p
	/// 1.0ab
	/// .f
	/// ```
	InvalidNumberSuffix(Span),
	/// Found a number that could not be parsed into an `i64`/`u64`.
	/// ```text
	/// 18_446_744_073_709_551_616
	/// ```
	UnparsableNumber(Span),

	/* COMPOUND EXPRESSIONS */
	/// ERROR - In the position that either a binary or postfix operator or the end-of-expression were expected to
	/// occur, we found an operand. E.g.
	/// - `foo bar`
	/// - `5 10`
	///
	/// Note that this error is not produced if we are within a delimited arity group, e.g. `fn(foo bar)`. In such
	/// cases [`ExpectedCommaAfterArg`](Self::ExpectedCommaAfterArg) is produced instead.
	///
	/// - `0` - The span of the previous operand.
	/// - `1` - The span of the current operand.
	FoundOperandAfterOperand(Span, Span),
	/// ERROR - In the position that a prefix operator or an operand were expected to occur, we found an operator
	/// which is not a valid prefix operator. E.g.
	/// - `foo + *bar`
	/// - `foo + %bar`
	///
	/// Layout:
	/// - `0` - The span of the operator.
	InvalidPrefixOperator(Span),
	/// ERROR - In the position that either a binary or postfix operator or the end-of-expression were expected
	/// to occur, we found an operator which is only valid as a prefix. E.g.
	/// - `foo!`
	/// - `foo~`
	///
	/// Layout:
	/// - `0` - The span of the operator.
	InvalidBinOrPostOperator(Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a dot.
	/// E.g.
	/// - `foo + .`
	/// - `foo.bar(). .`
	/// - `.`
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a dot.
	///
	/// - `0` - The span of the previous operator, if there is one.
	/// - `1` - The span of the dot.
	FoundDotInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a comma.
	/// E.g. `foo + ,`.
	///
	/// - `0` - The span of the previous operator.
	/// - `1` - The span of the current comma.
	FoundCommaInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a
	/// question mark. E.g. `foo + ?`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a
	/// question mark.
	///
	/// - `0` - The span of the previous operator, if there is one.
	/// - `1` - The span of the current question mark.
	FoundQuestionInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a colon.
	/// E.g. `foo ? bar + :`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a colon.
	///
	/// - `0` - The span of the previous operator, if there is one.
	/// - `1` - The span of the current colon.
	FoundColonInsteadOfOperand(Option<Span>, Span),
	/// ERROR - Found a [`Token`](crate::lexer::Token) which cannot be part of an expression. E.g. `@`.
	///
	/// - `0` - The span of the token.
	FoundInvalidToken(Span),

	/* GROUPS */
	/// ERROR - Found a set of parenthesis that contains no expression. E.g. `()`.
	///
	/// - `0` - The span where the expression is expected.
	FoundEmptyParens(Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found the
	/// start of an index operator (`[`). E.g. `foo + [`.
	///
	/// - `0` - The span of the previous operator, if there is one.
	/// - `1` - The span of the opening bracket.
	FoundLBracketInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing parenthesis (`)`). E.g.
	/// - `(foo + )`
	/// - `fn(bar - )`
	///
	/// Note that this error is not generated if the first token encountered when parsing a new expression is the
	/// closing parenthesis.
	///
	/// - `0` - The span of the previous operator.
	/// - `1` - The span on the closing parenthesis.
	FoundRParenInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing bracket (`]`). E.g. `i[5 + ]`.
	///
	/// Note that this error is not generated if the first token encountered when parsing a new expression is the
	/// closing bracket.
	///
	/// - `0` - The span of the previous operator.
	/// - `1` - The span of the closing parenthesis.
	FoundRBracketInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing brace (`}`). E.g. `{foo + }`.
	///
	/// Note that this error is not generated if the first token encountered when parsing a new expression is the
	/// closing brace.
	///
	/// - `0` - The span of the previous operator.
	/// - `1` - The span on the closing brace.
	FoundRBraceInsteadOfOperand(Span, Span),

	/* ARITY */
	/// ERROR - Did not find a comma after an argument expression in a delimited arity group. E.g.
	/// - `fn(foo bar`
	/// - `{foo bar`
	///
	/// Layout:
	/// - `0` - The span where the comma is expected.
	ExpectedCommaAfterArg(Span),
	/// ERROR - Did not find an argument expression after a comma in a delimited arity group. E.g.
	/// - `fn(foo, `
	/// - `{foo, `
	///
	/// Layout:
	/// - `0` - The span where the argument is expected.
	ExpectedArgAfterComma(Span),
	/// ERROR - Did not find an argument between the opening parenthesis and the comma. E.g. `fn( , bar`.
	///
	/// - `0` - The span where the argument is expected.
	ExpectedArgBetweenParenComma(Span),
	/// ERROR - Did not find an argument between the opening brace and the comma. E.g. `{ , bar`.
	///
	/// - `0` The span where the argument is expected.
	ExpectedArgBetweenBraceComma(Span),
	/// ERROR - Did not find a comma after an expression in a list. E.g. `foo bar`.
	///
	/// - `0` - The span where the comma is expected.
	ExpectedCommaAfterExpr(Span),
	/// ERROR - Did not find an expression after a comma in a list. E.g. `foo, `.
	///
	/// - `0 - The span where the expression is expected.
	ExpectedExprAfterComma(Span),
	/// ERROR - Did not find an expression before the first comma in a list. E.g. `, bar`.
	///
	/// - `0` - The span where the expression is expected.
	ExpectedExprBeforeComma(Span),

	/* UNCLOSED GROUPS */
	/// ERROR - Found an unclosed set of parenthesis. E.g. `(...`.
	///
	/// - `0` - The span of the opening `(`.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedParens(Span, Span),
	/// ERROR - Found an unclosed index operator. E.g. `i[...`.
	///
	/// - `0` - The span of the opening `[`.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedIndexOperator(Span, Span),
	/// ERROR - Found an unclosed function call. E.g. `fn(...`.
	///
	/// - `0` - The span of the opening `(`.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedFunctionCall(Span, Span),
	/// ERROR - Found an unclosed initializer list. E.g. `{...`.
	///
	/// - `0` - The span of the opening `{`.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedInitializerList(Span, Span),
	/// ERROR - Found an unclosed array constructor. E.g. `int[](...`.
	///
	/// - `0` - The span of the opening `(`.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedArrayConstructor(Span, Span),

	/* DEFINED OPERATOR - ONLY PRESENT WITHIN EXPRESSIONS IN CONDITIONAL DIRECTIVES */
	/// ERROR - Did not find an identifier or an opening parenthesis after the `defined` keyword.
	///
	/// - `0` - The position where the ident or opening parenthesis is expected.
	ExpectedIdentOrLParenAfterDefinedOp(Span),
	/// ERROR - Did not find an identifier after the opening parenthesis after the `defined` keyword.
	///
	/// - `0` - The position where the ident is expected.
	ExpectedIdentAfterDefineOpLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the identifier in a `define` operator.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	ExpectedRParenAfterDefineOpIdent(Span),

	/*  */
	ExpectedIdentOnLhsOfDot(Span),
}

/// Syntax diagnostics for statement.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StmtDiag {
	/// ERROR - Did not find a semi-colon after an expression, (to make it into a valid expression statement).
	///
	/// - `0` - The position where the semi-colon is expected.
	ExprStmtExpectedSemiAfterExpr(Span),
	/// ERROR - Did not find a closing brace to finish a scope.
	///
	/// - `0` - The span of the scope's opening brace.
	/// - `1` - The position where the closing brace is expected.
	ScopeMissingRBrace(Span, Span),
	/// ERROR - Found one or more qualifiers before a statement which cannot be preceded by qualifiers. E.g. `const
	/// return;`.
	///
	/// - `0` - The span of the qualifier(s).
	FoundQualifiersBeforeStmt(Span),
	/// ERROR - Did not find one or more identifiers after a type specifier, (this could be for a variable,
	/// function, etc.). E.g. `mat4[2] ;`.
	///
	/// - `0` - The position where the identifier(s) are expected.
	TypeExpectedIdentsAfterType(Span),

	/* SCOPING */
	/// ERROR - Found a subroutine uniform definition statement within a nested scope; only valid in the top-level
	/// scope.
	///
	/// - `0` - The span of the statement.
	FoundSubUniformInNestedScope(Span),

	/* QUALIFIERS */
	/// ERROR - Did not find an opening parenthesis after the `layout` keyword.
	///
	/// - `0` - The span where the opening parenthesis is expected.
	LayoutExpectedLParenAfterKw(Span),
	/// ERROR - Found a token which is not a valid layout. E.g. `layout(foobar)`.
	///
	/// - `0` - The span of the ident.
	LayoutInvalidIdent(Span),
	/// ERROR - Did not find an equals-sign after an ident which expects a value. E.g. `layout(location)`.
	///
	/// - `0` - The span where the equals-sign is expected.
	LayoutExpectedEqAfterIdent(Span),
	/// ERROR - Did not find an expression after an equals-sign. E.g. `layout(location =)`.
	///
	/// - `0` - The span where the expression is expected.
	LayoutExpectedExprAfterEq(Span),
	/// ERROR - Did not find a closing parenthesis when parsing a layout qualifier.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	LayoutMissingRParen(Span),
	/// ERROR - Did not find a comma after a layout in a layout list. E.g. `layout(std140 std430)`.
	///
	/// - `0` - The span where the comma is expected.
	LayoutExpectedCommaAfterLayout(Span),
	/// ERROR - Did not find a layout after a comma in a layout list. E.g. `layout(std140, )`.
	///
	/// - `0` - The span where the layout is expected.
	LayoutExpectedLayoutAfterComma(Span),
	/// ERROR - Did not find a layout between the opening parenthesis and the comma. E.g. `layout( , std430)`.
	///
	/// - `0` - The span where the layout is expected.
	LayoutExpectedLayoutBetweenParenComma(Span),

	/* VARIABLES */
	/// ERROR - Did not find a semi-colon or an equals-sign after the identifiers in a variable definition.
	///
	/// - `0` - The position where the semi-colon or equals-sign is expected.
	VarDefExpectedSemiOrEqAfterIdents(Span),
	/// ERROR - Did not find a value expression after the equals-sign in a variable definition with initialization.
	///
	/// - `0` - The position where the expression is expected.
	VarDefInitExpectedValueAfterEq(Span),
	/// ERROR - Did not find a semi-colon after the value expression in a variable definition with initialization.
	///
	/// - `0` - The position where the semi-colon is expected.
	VarDefInitExpectedSemiAfterValue(Span),

	/* INTERFACE BLOCKS */
	/// ERROR - Found a statement within the interface body that is invalid. E.g. `out V { return; };`.
	///
	/// - `0` - The span of the statement.
	InterfaceInvalidStmtInBody(Span),
	/// ERROR - Found an interface bod`y that has no statements. E.g. `out V { };`.
	///
	/// - `0` - The span of the body.
	InterfaceExpectedAtLeastOneStmtInBody(Span),
	/// ERROR - Did not find an instance identifier or a semi-colon after the interface body. E.g. `out V { int i;
	/// }`.
	///
	/// - `0` - The span of the invalid token(s), or the position where the semi-colon should be inserted.
	InterfaceExpectedInstanceOrSemiAfterBody(Span),
	/// ERROR - Did not find a semi-colon after the interface's instance ident. E.g. `out V { int i;
	/// } foo_bar`.
	///
	/// - `0` - The position where the semi-colon should be inserted.
	InterfaceExpectedSemiAfterInstance(Span),

	/* FUNCTIONS */
	/// ERROR - Did not find a comma after a parameter in a function's parameter list. E.g. `void fn(foo bar)`.
	///
	/// - `0` - The position where the comma is expected.
	ParamsExpectedCommaAfterParam(Span),
	/// ERROR - Did not find a paramater after a comma in a function's parameter list. E.g. `void fn(foo, )`.
	///
	/// - `0` - The span where the parameter is expected.
	ParamsExpectedParamAfterComma(Span),
	/// ERROR - Did not find a parameter between the opening parenthesis and the comma. E.g. `void fn( , bar)`.
	///
	/// - `0` - The span where the parameter is expected.
	ParamsExpectedParamBetweenParenComma(Span),
	/// ERROR - Found a token which could not be parsed as a type. E.g. `void fn(500)`.
	///
	/// - `0` - The span of the expression.
	ParamsInvalidTypeExpr(Span),
	/// ERROR - Found a token which could not be parsed as an identifier. E.g. `void fn(int 55)`.
	///
	/// - `0` - The span of the expression.
	ParamsInvalidIdentExpr(Span),
	/// ERROR - Did not find a closing parenthesis before a semi-colon or opening brace. E.g. `void fn(bar ;`.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	ParamsExpectedRParen(Span),
	/// ERROR - Did not find either a semi-colon or an opening brace after the parameter list. E.g. `void fn()`.
	///
	/// - `0` - The position where the semi-colon or opening brace is expected.
	FnExpectedSemiOrLBraceAfterParams(Span),

	/* SUBROUTINES */
	/// ERROR - Did not find a subroutine type declaration, an associated-function definition, or a subroutine
	/// uniform definition after a set of qualifiers including the subroutine keyword.
	///
	/// - `0` - The position where the rest of the statement is expected.
	SubExpectedAfterKw(Span),
	/// ERROR - Did not find a subroutine type declaration, an associated-function definition, or a subroutine
	/// uniform definition after the qualifiers containing the subroutine keyword.
	///
	/// - `0` - The position where either of the options are expected.
	SubExpectedTypeFnOrUniformAfterQualifiers(Span),
	/// ERROR - Did not find a uniform keyword in a statement that contains the subroutine keyword and a variable
	/// definition. The closest valid statement is a subroutine uniform definition, so that's what we assume.
	///
	/// - `0` - The position, after all qualifiers, where the uniform keyword is expected.
	SubUniformExpectedUniformKw(Span),
	/// ERROR - Found the uniform keyword before the subroutine keyword. E.g. `uniform subroutine foo f;`.
	///
	/// - `0` - The span of the keyword.
	SubUniformFoundUniformKwBeforeSubKw(Span),
	/// ERROR - Found an association list in a subroutine uniform definition. E.g. `subroutine(foo) uniform foo
	/// my_foo;`.
	///
	/// - `0` - The span of the association list.
	SubUniformFoundAssociationList(Span),
	/// ERROR - Found a normal type specifier rather than a subroutine type specifier in a subroutine uniform
	/// definition. E.g. `subroutine uniform int my_int;`.
	///
	/// - `0` - The span of the normal type specifier.
	SubUniformExpectedSubroutineType(Span),
	/// ERROR - Did not find a semi-colon after the new variable specifier(s) in a subroutine uniform definition.
	///
	/// - `0` - The position where the semi-colon is expected.
	SubUniformExpectedSemiAfterVars(Span),
	/// ERROR - Found an initialization in a new variable specifier in a subroutine uniform definition. E.g.
	/// `subroutine uniform foo f = 1;`.
	///
	/// - `0` - The span of the initialization part of the new variable specifier.
	SubUniformFoundInit(Span),

	/// ERROR - Found an association list in a subroutine type declaration. E.g. `subroutine(foo) void foo();`.
	///
	/// - `0` - The span of the association list.
	SubTypeDeclFoundAssociationList(Span),
	/// ERROR - Found the `uniform` keyword in a subroutine type declaration. E.g. `subroutine uniform void
	/// foo();`.
	///
	/// - `0` - The span of the uniform keyword.
	SubTypeDeclFoundUniformKw(Span),
	/// ERROR - Found a subroutine type specifier rather than a normal type specifier for the return value in a
	/// subroutine type declaration. E.g. `subroutine my_sub foo();`.
	///
	/// - `0` - The span of the subroutine type specifier.
	SubTypeDeclExpectedNormalType(Span),

	/// ERROR - Did not find an association list in a subroutine associated-function definition. E.g. `subroutine
	/// foo f1() {}`.
	///
	/// - `0` - The position where the association list is expected.
	SubFnDefExpectedAssociationList(Span),
	/// ERROR - Found the `uniform` keyword in a subroutine associated-function definition. E.g. `subroutine
	/// uniform void f1() { }`.
	///
	/// - `0` - The span of the uniform keyword.
	SubFnDefFoundUniformKw(Span),
	/// ERROR - Found a subroutine type specifier rather than a normal type specifier for the return value in a
	/// subroutine associated-function definition. E.g. `subroutine(foo) foo f1() { }`.
	///
	/// - `0` - The span of the subroutine type specifier.
	SubFnDefExpectedNormalType(Span),

	/// ERROR - Did not find a variable definition after the `uniform` keyword in a subroutine definition. E.g.
	/// `subroutine uniform struct;`.
	///
	/// - `0` - The position where the variable definition is expected.
	SubroutineUniformExpectedVarDefAfterQualifiers(Span),
	/// ERROR - Did not find either a subroutine type declaration, an associated function definition, or a uniform
	/// definition after the `subroutine` keyword. E.g. `subroutine struct Bar...`.
	///
	/// - `0` - The position where either of the options is expected.
	SubroutineExpectedTypeFuncUniformAfterKw(Span),
	/// ERROR - Did not find a comma after an ident in a subroutine's associated list. E.g. `subroutine(foo bar)`.
	///
	/// - `0` - The position where the comma is expected.
	SubroutineAssociatedListExpectedCommaAfterIdent(Span),
	/// ERROR - Did not find an ident after a comma in a subroutines's associated list. E.g. `subroutine(foo, )`.
	///
	/// - `0` - The span where the ident is expected.
	SubroutineAssociatedListExpectedIdentAfterComma(Span),
	/// ERROR - Did not find an ident between the opening parenthesis and the comma. E.g. `subroutine( , bar)`.
	///
	/// - `0` - The span where the ident is expected.
	SubroutineAssociatedListExpectedIdentBetweenParenComma(Span),
	/// ERROR - Did not find a closing parenthesis to close the associated subroutines list. E.g. `subroutine(foo`.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	SubroutineAssociatedListExpectedRParen(Span),
	/// ERROR - Did not find a function definition after an associated subroutines list. E.g. `subroutine(foo,
	/// bar) struct`.
	///
	/// - `0` - The span where the function definition is expected.
	SubroutineExpectedFnDefAfterAssociatedList(Span),
	/// ERROR - Found a function declaration after an associated subroutines list instead of a function definition.
	/// E.g. `subroutine(foo, bar) int foo_1(int i);`.
	///
	/// - `0` - The span of the function declaration.
	SubroutineExpectedFnDefAfterAssociatedListFoundDecl(Span),
	/// ERROR - Did not find a list of associations in a subroutine associated function definition. E.g.
	/// `subroutine int foo_1(int i) {}`.
	///
	/// - `0` - The span where the associated-list are expected.
	SubroutineMissingAssociationsForFnDef(Span),
	/// ERROR - Did not find the `uniform` keyword in a subroutine uniform definition. E.g. `subroutine foo
	/// my_foo;`.
	///
	/// - `0` - The span where the keyword is expected.
	SubroutineMissingUniformKwForUniformDef(Span),

	/* STRUCTS */
	/// ERROR - Did not find a name after the `struct` keyword. E.g. `struct foo - 3`.
	///
	/// - `0` - The span of the invalid token(s) or the position where the ident should be inserted.
	StructExpectedNameAfterKw(Span),
	/// ERROR - Did not find an opening brace after the name. E.g. `struct Foo [`.
	///
	/// - `0` - The position where the opening brace should be inserted.
	StructExpectedLBraceAfterName(Span),
	/// ERROR - Found a statement within the struct body that is invalid. E.g. `struct Foo { return; };`.
	///
	/// - `0` - The span of the statement.
	StructInvalidStmtInBody(Span),
	/// ERROR - Found a member definition within the struct body that has an initializer. E.g. `struct Foo { int i
	/// = 5; };
	///
	/// - `0` - The span of the member.
	StructMemberCannotBeInitialized(Span),
	/// ERROR - Found a struct body that has no members. E.g. `struct Foo { };`.
	///
	/// - `0` - The span of the body.
	StructExpectedAtLeastOneMemberInBody(Span),
	/// ERROR - Did not find an instance identifier or a semi-colon after the struct body. E.g. `struct Foo { int
	/// i; } }`.
	///
	/// - `0` - The span of the invalid token(s), or the position where the semi-colon should be inserted.
	StructExpectedInstanceOrSemiAfterBody(Span),
	/// ERROR - Did not find a semi-colon after the struct's instance ident. E.g. `struct Foo { int i; } foobar`.
	///
	/// - `0` - The position where the semi-colon should be inserted.
	StructExpectedSemiAfterInstance(Span),
	/// ERROR - Found a struct declaration, which is not a legal GLSL statement. E.g. `struct Foo;`.
	///
	/// - `0` - The span of the declaration.
	StructDeclIsIllegal(Span),

	/* IF STATEMENTS */
	/// ERROR - Did not find an opening parenthesis after the `if` keyword.
	///
	/// - `0` - The position where the opening parenthesis is expected.
	IfExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The position where the expression is expected.
	IfExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	IfExpectedRParenAfterExpr(Span),
	/// ERROR - Did not find an opening brace or a statement after the if/else-if-condition header.
	///
	/// - `0` - The position where the opening brace or statement is expected.
	IfExpectedLBraceOrStmtAfterRParen(Span),
	/// ERROR - Did not find the `if` keyword or an opening brace or a statement after the `else` keyword.
	///
	/// - `0` - The position where the keyword or opening brace or statement is expected.
	IfExpectedIfOrLBraceOrStmtAfterElseKw(Span),

	/* SWITCH STATEMENTS */
	/// ERROR - Did not find an opening parenthesis after the `switch` keyword.
	///
	/// - `0` - The position where the opening parenthesis is expected.
	SwitchExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The position where the expression is expected.
	SwitchExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	SwitchExpectedRParenAfterExpr(Span),
	/// ERROR - Did not find an opening brace after the switch condition.
	///
	/// - `0` - The position where the opening brace is expected.
	SwitchExpectedLBraceAfterCond(Span),
	/// ERROR - Found a switch body which is empty.
	///
	/// - `0` - The span of the body.
	SwitchFoundEmptyBody(Span),
	/// ERROR - Found a token that is not the `case`/`default` keyword nor a closing brace.
	///
	/// - `0` - The span of tokens until a `case`/`default` keyword or closing brace.
	SwitchExpectedCaseOrDefaultKwOrEnd(Span),
	/// ERROR - Did not find an expression after the `case` keyword.
	///
	/// - `0` - The position where the expression is expected.
	SwitchExpectedExprAfterCaseKw(Span),
	/// ERROR - Did not find a colon after the case expression.
	///
	/// - `0` - The position where the colon is expected.
	SwitchExpectedColonAfterCaseExpr(Span),
	/// ERROR - Did not find a colon after the `default` keyword.
	///
	/// - `0` - The position where the colon is expected.
	SwitchExpectedColonAfterDefaultKw(Span),
	/// ERROR - Did not find a closing brace at the end of the body.
	///
	/// - `0` - The position where the brace is expected.
	SwitchExpectedRBrace(Span),

	/* FOR LOOPS */
	/// ERROR - Did not find an opening parenthesis after the `for` keyword.
	///
	/// - `0` - The position where the opening parenthesis is expected.
	ForExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an initialization statement after the opening parenthesis.
	///
	/// - `0` - The position where the statement is expected.
	ForExpectedInitStmt(Span),
	/// ERROR - Did not find a conditional statement after the opening parenthesis.
	///
	/// - `0` - The position where the statement is expected.
	ForExpectedCondStmt(Span),
	/// ERROR - Did not find an increment statement after the opening parenthesis.
	///
	/// - `0` - The position where the statement is expected.
	ForExpectedIncStmt(Span),
	/// ERROR - Did not find 3 statements before reaching the closing parenthesis.
	///
	/// - `0` - The span of the early closing parenthesis.
	ForExpected3Stmts(Span),
	/// ERROR - Did not find a closing parenthesis after the 3 statements.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	ForExpectedRParenAfterStmts(Span),
	/// ERROR - Did not find an opening brace after the for-loop header.
	///
	/// - `0` - The position where the opening brace is expected.
	ForExpectedLBraceAfterHeader(Span),

	/* WHILE/DO-WHILE LOOPS */
	/// ERROR - Did not find an opening parenthesis after the `while` keyword.
	///
	/// - `0` - The position where the opening parenthesis is expected.
	WhileExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The position where the expression is expected.
	WhileExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The position where the closing parenthesis is expected.
	WhileExpectedRParenAfterExpr(Span),
	/// ERROR - Did not find an opening brace after the while-loop condition.
	///
	/// - `0` - The position where the opening brace is expected.
	WhileExpectedLBraceAfterCond(Span),
	/// ERROR - Did not find an opening brace after the `do` keyword.
	///
	/// - `0` - The position where the opening brace is expected.
	DoWhileExpectedLBraceAfterKw(Span),
	/// ERROR - Did not find the `while` keyword after the body of a do-while loop.
	///
	/// - `0` - The position where the keyword is expected.
	DoWhileExpectedWhileAfterBody(Span),
	/// ERROR - Did not find a semi-colon after the do-while-loop.
	///
	/// - `0` - The position where the semi-colon is expected.
	DoWhileExpectedSemiAfterRParen(Span),

	/* SINGLE-KEYWORD CONTROL FLOW */
	/// ERROR - Did not find a semi-colon after the `break` keyword.
	///
	/// - `0` - The position where the semi-colon is expected.
	BreakExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `continue` keyword.
	///
	/// - `0` - The position where the semi-colon is expected.
	ContinueExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `discar` keyword.
	///
	/// - `0` - The position where the semi-colon is expected.
	DiscardExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon or an expression after the `return` keyword.
	///
	/// - `0` - The position where the semi-colon or expression is expected.
	ReturnExpectedSemiOrExprAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `return` expression.
	///
	/// - `0` - The position where the semi-colon is expected.
	ReturnExpectedSemiAfterExpr(Span),
}

/// Syntax diagnostics for the `#version` directive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocVersionDiag {
	/// ERROR - Did not find a number after the `version` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the number is expected.
	ExpectedNumber(Span),
	/// ERROR - Did not find a number after the `version` keyword, but did find a profile. E.g. `#version core`.
	///
	/// - `0` - The span between the keyword and profile.
	MissingNumberBetweenKwAndProfile(Span),
	/// ERROR - Found a number-like token that can't be successfully parsed as a version number. E.g. `#version
	/// 1961752700000000000`.
	///
	/// - `0` - The span of the number-like token.
	InvalidNumber(Span),
	/// ERROR - Found a number that can't be parsed as a valid GLSL version. E.g. `#version 480`.
	///
	/// - `0` - The span of the number.
	/// - `1` - The number.
	InvalidVersion(Span, usize),
	/// ERROR - Found a GLSL version number that is not currently supported by this crate. E.g. `#version 300`.
	///
	/// - `0` - The span of the number.
	/// - `1` - The number.
	UnsupportedVersion(Span, usize),
	/// ERROR - Did not find a profile after the version number.
	///
	/// - `0` - The span of the incorrect token or the position where the profile is expected.
	ExpectedProfile(Span),
	/// ERROR - Found a word that can't be parsed as a valid profile. E.g. `#version 450 foobar`.
	///
	/// - `0` - The span of the word.
	InvalidProfile(Span),
	/// ERROR - Found a word that would be a valid profile with the correct capitalization. E.g. `#version
	/// 450 CoRe`.
	///
	/// - `0` - The span of the word.
	/// - `1` - The corrected spelling.
	InvalidProfileCasing(Span, &'static str),
}

/// Syntax diagnostics for the `#extension` directive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocExtDiag {
	/// ERROR - Did not find a name after the `extension` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the name is expected.
	ExpectedName(Span),
	/// ERROR - Did not find a name after the `extension` keyword, but did find a colon. E.g. `#extension :
	/// enable`.
	///
	/// - `0` - The span between the keyword and colon.
	MissingNameBetweenKwAndColon(Span),
	/// ERROR - Did not find a name after the `extension` keyword, but did find a behaviour. E.g. `#extension
	/// enable`.
	///
	/// - `0` - The span between the keyword and behaviour.
	MissingNameBetweenKwAndBehaviour(Span),
	/// ERROR - Did not find a colon after the name, but did find a behaviour. E.g. `#extension foobar enable`.
	///
	/// - `0` - The span between the name and behaviour.
	MissingColonBetweenNameAndBehaviour(Span),
	/// ERROR - Did not find a colon after the extension name.
	///
	/// - `0` - The span of the incorrect token or the position where the colon is expected.
	ExpectedColon(Span),
	/// ERROR - Did not find a behaviour after the colon.
	///
	/// - `0` - The span of the incorrect token or the position where the behaviour is expected.
	ExpectedBehaviour(Span),
	/// ERROR - Found a word that can't be parsed as a valid behaviour. E.g. `#extension all : foobar`.
	///
	/// - `0` - The span of the word.
	InvalidBehaviour(Span),
	/// ERROR - Found a word that would be a valid behaviour with the correct capitalization. E.g.
	/// `#extension all : EnAbLe`.
	///
	/// - `0` - The span of the word.
	/// - `1` - The corrected spelling.
	InvalidBehaviourCasing(Span, &'static str),
}

/// Syntax diagnostics for the `#line` directive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocLineDiag {
	/// ERROR - Did not find a number after the `line` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the number is expected.
	ExpectedNumber(Span),
	/// ERROR - Found a number-like token that can't be successfully parsed as a line number. E.g.
	/// `#line 100000000000000000000`.
	///
	/// - `0` - The span of the number-like token.
	InvalidNumber(Span),
}

/// Syntax diagnostics for the `#define` and `#undef` directives.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocDefineDiag {
	/* DEFINE */
	/// ERROR - Did not find an identifier token after the `define` keyword.
	///
	/// - `0` - The position where the macro name is expected.
	DefineExpectedMacroName(Span),
	/// ERROR - Did not find a parameter.
	///
	/// - `0` - The span of the invalid token.
	ParamsExpectedParam(Span),
	/// ERROR - Did not find a comma after a parameter in a macro's parameter list. E.g. `#define fn(foo bar)`.
	///
	/// - `0` - The position where the comma is expected.
	ParamsExpectedCommaAfterParam(Span),
	/// ERROR - Did not find a paramater after a comma in a macro's parameter list. E.g. `#define fn(foo, )`.
	///
	/// - `0` - The span where the parameter is expected.
	ParamsExpectedParamAfterComma(Span),
	/// ERROR - Did not find a parameter between the opening parenthesis and the comma in a macro's parameter list.
	/// E.g. `#define fn( , bar)`.
	///
	/// - `0` - The span where the parameter is expected.
	ParamsExpectedParamBetweenParenComma(Span),
	/// ERROR - Did not find a closing parenthesis to a macro's parameter list. E.g. `#define fn(bar, baz `.
	///
	/// `0` - The position where the closing parenthesis is expected.
	ParamsExpectedRParen(Span),

	/* TOKEN CONCAT */
	/// ERROR - Found a token concatenation operator (`##`) with no valid token on the left-hand side. E.g.
	/// ```c
	/// #define FOO ## 0
	/// ```
	///
	/// - `0` - The span of the operator.
	TokenConcatMissingLHS(Span),
	/// ERROR - Found a token concatenation operator (`##`) with no valid token on the right-hand side. E.g.
	/// ```c
	/// #define FOO 500 ##
	/// #define FOO 90 ## ## 00
	/// ```
	///
	/// - `0` - The span of the operator.
	TokenConcatMissingRHS(Span),

	/* UNDEF */
	/// ERROR - Did not find an identifier token after the `undef` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the macro name should be inserted.
	UndefExpectedMacroName(Span),
}

/// Syntax diagnostics for the conditional directives.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocConditionalDiag {
	/// ERROR - Did not find an identifier token after the `ifdef` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the macro name should be inserted.
	ExpectedNameAfterIfDef(Span),
	/// ERROR - Did not find an identifier token after the `ifndef` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the macro name should be inserted.
	ExpectedNameAfterIfNotDef(Span),
	/// ERROR - Did not find an expression after the `if` keyword.
	///
	/// - `0` - The position where the expression should be inserted.
	ExpectedExprAfterIf(Span),
	/// ERROR - Did not find an expression after the `elseif` keyword.
	///
	/// - `0` - The position where the expression should be inserted.
	ExpectedExprAfterElseIf(Span),
	/// ERROR - Did not find an `#endif` directive to close a conditional block.
	///
	/// - `0` - The span of the opening `#ifdef`/`#ifndef`/`#if` directive.
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedBlock(Span, Span),
	/// ERROR - Found an unmatched `#elif` directive.
	///
	/// - `0` - The span of the directive.
	UnmatchedElseIf(Span),
	/// ERROR - Found an unmatched `#else` directive.
	///
	/// - `0` - The span of the directive.
	UnmatchedElse(Span),
	/// ERROR - Found an unmatched `#endif` directive.
	///
	/// - `0` - The span of the directive.
	UnmatchedEndIf(Span),
}

impl Syntax {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl ExprDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl StmtDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl PreprocVersionDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl PreprocExtDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl PreprocLineDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl PreprocDefineDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

impl PreprocConditionalDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}
