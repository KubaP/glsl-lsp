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
#[derive(Debug)]
#[non_exhaustive]
pub enum Semantic {
	/* MACROS */
	/// WARNING - Found a macro call site, but the macro contains no replacement tokens.
	///
	/// - `0` - The span of the call site.
	EmptyMacroCallSite(Span),
	/// WARNING - The macro name in an undef directive could not be resolved.
	///
	/// - `0` - The span of the name.
	UndefMacroNameUnresolved(Span),
}

impl Semantic {
	pub fn get_severity(&self) -> Severity {
		match self {
			/* MACROS */
			Semantic::EmptyMacroCallSite(_) => Severity::Warning,
			Semantic::UndefMacroNameUnresolved(_) => Severity::Warning,
		}
	}
}

/// All syntax diagnostics.
#[derive(Debug)]
#[non_exhaustive]
pub enum Syntax {
	/// Diagnostics for expressions.
	Expr(ExprDiag),
	/// Diagnostics for statement.
	Stmt(StmtDiag),

	/// Diagnostics for the `#define` and `#undef` directives.
	PreprocDefine(PreprocDefineDiag),
	/// Diagnostics for the conditional directives.
	PreprocConditional(PreprocConditionalDiag),
	/// ERROR - Found trailing tokens in a directive.
	///
	/// - `0` - The span of the tokens.
	PreprocTrailingTokens(Span),

	/// ERROR - Found a block comment that is missing the closing tag.
	///
	/// - `0` - The span where the closing tag is expected.
	BlockCommentMissingEnd(Span),
}

impl Syntax {
	pub fn get_severity(&self) -> Severity {
		match self {
			Syntax::Expr(e) => e.get_severity(),
			Syntax::Stmt(s) => s.get_severity(),
			Syntax::PreprocDefine(d) => d.get_severity(),
			Syntax::PreprocConditional(d) => d.get_severity(),
			Syntax::PreprocTrailingTokens(_) => Severity::Error,
			Syntax::BlockCommentMissingEnd(_) => Severity::Error,
		}
	}
}

/// Syntax diagnostics for expressions.
#[derive(Debug)]
#[non_exhaustive]
pub enum ExprDiag {
	// TODO: Track the spans of the suffixes and generate errors when a suffix mismatches the number type.

	/* LITERALS */
	/// ERROR - Found a number literal that has an invalid suffix.
	///
	/// - `0` - The span of the number.
	InvalidNumber(Span),
	/// ERROR - Found a number literal that has no digits, e.g. `0xu` or `.f`.
	///
	/// - `0` - The span of the number.
	EmptyNumber(Span),
	/// ERROR - Found a number literal that could not be parsed.
	///
	/// - `0` - The span of the number.
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
	/// - `0` - The span of the previous operand,
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
	/// ERROR - In the position that either a binary or postfix operator, or the end-of-expression, were expected
	/// to occur, we found an operator which is only valid as a prefix. E.g.
	/// - `foo!`
	/// - `foo~`
	///
	/// Layout:
	/// - `0` - The span of the operator.
	InvalidBinOrPostOperator(Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a dot
	/// (`.`). E.g.
	/// - `foo + .`
	/// - `foo.bar(). .`
	/// - `.`
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a dot.
	///
	/// - `0` - The span of the previous operator (if there is one),
	/// - `1` - The span of the dot.
	FoundDotInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a comma.
	/// E.g. `foo + ,`.
	///
	/// - `0` - The span of the previous operator,
	/// - `1` - The span of the current comma.
	FoundCommaInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a
	/// question mark. E.g. `foo + ?`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a
	/// question mark.
	///
	/// - `0` - The span of the previous operator,
	/// - `1` - The span of the current question mark.
	FoundQuestionInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or operand were expected to occur, we found a colon.
	/// E.g. `foo ? bar + :`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a colon
	/// mark.
	///
	/// - `0` - The span of the previous operator,
	/// - `1` - The span of the current colon.
	FoundColonInsteadOfOperand(Option<Span>, Span),
	/// ERROR - Found a [`Token`](crate::lexer::Token) which cannot be part of an expression. E.g. `;`.
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
	/// - `0` - The span of the previous operator (if there is one),
	/// - `1` - The span of the opening bracket.
	FoundLBracketInsteadOfOperand(Option<Span>, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing parenthesis (`)`). E.g.
	/// - `(foo + )`
	/// - `fn(bar - )`
	///
	/// Note: This error is not generated if the first token encountered when parsing a new expression is the
	/// closing parenthesis.
	///
	/// - `0` - The span of the previous operator,
	/// - `1` - The span on the closing parenthesis.
	FoundRParenInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing bracket (`]`). E.g. `i[5 + ]`.
	///
	/// Note: This error is not generated if the first token encountered when parsing a new expression is the
	/// closing bracket.
	///
	/// - `0` - The span of the previous operator,
	/// - `1` - The span of the closing parenthesis.
	FoundRBracketInsteadOfOperand(Span, Span),
	/// ERROR - In the position that either a prefix operator or an operand were expected to occur, we found a
	/// closing brace (`}`). E.g. `{foo + }`.
	///
	/// Note: This error is not generated if the first token encountered when parsing a new expression is the
	/// closing brace.
	///
	/// - `0` - The span of the previous operator,
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
	/// ERROR - Found an unclosed set of parenthesis, e.g. `(...`.
	///
	/// - `0` - The span of the opening `(`,
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedParens(Span, Span),
	/// ERROR - Found an unclosed index operator, e.g. `i[...`.
	///
	/// - `0` - The span of the opening `[`,
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedIndexOperator(Span, Span),
	/// ERROR - Found an unclosed function call, e.g. `fn(...`.
	///
	/// - `0` - The span of the opening `(`,
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedFunctionCall(Span, Span),
	/// ERROR - Found an unclosed initializer list, e.g. `{...`.
	///
	/// - `0` - The span of the opening `{`,
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedInitializerList(Span, Span),
	/// ERROR - Found an unclosed array constructor, e.g. `int[](...`.
	///
	/// - `0` - The span of the opening `(`,
	/// - `1` - The zero-width span at the end of the expression.
	UnclosedArrayConstructor(Span, Span),
}

impl ExprDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			/* LITERALS */
			ExprDiag::InvalidNumber(_) => Severity::Error,
			ExprDiag::EmptyNumber(_) => Severity::Error,
			ExprDiag::UnparsableNumber(_) => Severity::Error,
			/* COMPOUND EXPRESSIONS */
			ExprDiag::FoundOperandAfterOperand(_, _) => Severity::Error,
			ExprDiag::InvalidPrefixOperator(_) => Severity::Error,
			ExprDiag::InvalidBinOrPostOperator(_) => Severity::Error,
			ExprDiag::FoundDotInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundCommaInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundQuestionInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundColonInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundInvalidToken(_) => Severity::Error,
			/* GROUPS */
			ExprDiag::FoundEmptyParens(_) => Severity::Error,
			ExprDiag::FoundLBracketInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundRParenInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundRBracketInsteadOfOperand(_, _) => Severity::Error,
			ExprDiag::FoundRBraceInsteadOfOperand(_, _) => Severity::Error,
			/* ARITY */
			ExprDiag::ExpectedCommaAfterArg(_) => Severity::Error,
			ExprDiag::ExpectedArgAfterComma(_) => Severity::Error,
			ExprDiag::ExpectedArgBetweenParenComma(_) => Severity::Error,
			ExprDiag::ExpectedArgBetweenBraceComma(_) => Severity::Error,
			ExprDiag::ExpectedCommaAfterExpr(_) => Severity::Error,
			ExprDiag::ExpectedExprAfterComma(_) => Severity::Error,
			ExprDiag::ExpectedExprBeforeComma(_) => Severity::Error,
			/* UNCLOSED GROUPS */
			ExprDiag::UnclosedParens(_, _) => Severity::Error,
			ExprDiag::UnclosedIndexOperator(_, _) => Severity::Error,
			ExprDiag::UnclosedFunctionCall(_, _) => Severity::Error,
			ExprDiag::UnclosedInitializerList(_, _) => Severity::Error,
			ExprDiag::UnclosedArrayConstructor(_, _) => Severity::Error,
		}
	}
}

/// Syntax diagnostics for statement.
#[derive(Debug)]
#[non_exhaustive]
pub enum StmtDiag {
	/// ERROR - Did not find a semi-colon after an expression (to make it into a valid expression statement).
	///
	/// - `0` - The span where the semi-colon is expected.
	ExprStmtExpectedSemiAfterExpr(Span),
	/// ERROR - Did not find a closing brace to finish a scope.
	///
	/// - `0` - The span of the scope's opening brace.
	/// - `1` - The span where the closing brace is expected.
	ScopeMissingRBrace(Span, Span),
	/// ERROR - Found one or more qualifiers before a statement which cannot be preceded by qualifiers. E.g. `const
	/// return;`.
	///
	/// - `0` - The span of the qualifiers.
	FoundQualifiersBeforeStmt(Span),

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
	/// - `0` - The span where the semi-colon or equals-sign is expected.
	VarDefExpectedSemiOrEqAfterIdents(Span),
	/// ERROR - Did not find a value expression after the equals-sign in a variable declaration.
	///
	/// - `0` - The span where the expression is expected.
	VarDeclExpectedValueAfterEq(Span),
	/// ERROR - Did not find a semi-colon after the value expression in a variable declaration.
	///
	/// - `0` - The span where the semi-colon is expected.
	VarDeclExpectedSemiAfterValue(Span),

	/* FUNCTIONS */
	/// ERROR - Did not find a comma after a parameter in a function's parameter list. E.g. `void fn(foo bar)`.
	///
	/// - `0` - The span where the comma is expected.
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
	/// - `0` - The span where the semi-colon or opening brace is expected.
	FnExpectedSemiOrLBraceAfterParams(Span),

	/* STRUCTS */
	/// ERROR - Did not find an identifier after the `struct` keyword. E.g. `struct;`.
	///
	/// - `0` - The span where the ident is expected.
	StructExpectedIdentAfterKw(Span),
	/// ERROR - Did not find an opening brace after the ident. E.g. `struct Foo`.
	///
	/// - `0` - The span where the opening brace is expected.
	StructExpectedLBraceAfterIdent(Span),
	/// ERROR - Found a statement within the struct body that is invalid. E.g. `struct Foo { return; };`.
	///
	/// - `0` - The span of the statement.
	StructInvalidStmtInBody(Span),
	/// ERROR - Did not find an instance ident or a semi-colon after the struct body. E.g. `struct Foo { int i; }`.
	///
	/// - `0` - The span where the instance ident or semi-colon is expected.
	StructExpectedInstanceOrSemiAfterBody(Span),
	/// ERROR - Did not find a semi-colon after the struct body or optional instance ident. E.g. `struct Foo {}`.
	///
	/// - `0` - The span where the semi-colon is expected.
	StructExpectedSemiAfterBodyOrInstance(Span),
	/// ERROR - Found a struct definition which is not a valid GLSL statement. E.g. `struct Foo;`.
	///
	/// - `0` - The span of the definition.
	StructDefIsInvalid(Span),

	/* SINGLE-KEYWORD CONTROL FLOW */
	/// ERROR - Did not find a semi-colon after the `break` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	BreakExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `continue` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	ContinueExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `discar` keyword.
	///
	/// - `0` - The span where the semi-colon is expected.
	DiscardExpectedSemiAfterKw(Span),
	/// ERROR - Did not find a semi-colon or an expression after the `return` keyword.
	///
	/// - `0` - The span where the semi-colon or expression is expected.
	ReturnExpectedSemiOrExprAfterKw(Span),
	/// ERROR - Did not find a semi-colon after the `return` expression.
	///
	/// - `0` - The span where the semi-colon is expected.
	ReturnExpectedSemiAfterExpr(Span),
}

impl StmtDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			StmtDiag::ExprStmtExpectedSemiAfterExpr(_) => Severity::Error,
			StmtDiag::ScopeMissingRBrace(_, _) => Severity::Error,
			StmtDiag::FoundQualifiersBeforeStmt(_) => Severity::Error,
			/* QUALIFIERS */
			StmtDiag::LayoutExpectedLParenAfterKw(_) => Severity::Error,
			StmtDiag::LayoutInvalidIdent(_) => Severity::Error,
			StmtDiag::LayoutExpectedEqAfterIdent(_) => Severity::Error,
			StmtDiag::LayoutExpectedExprAfterEq(_) => Severity::Error,
			StmtDiag::LayoutMissingRParen(_) => Severity::Error,
			StmtDiag::LayoutExpectedCommaAfterLayout(_) => Severity::Error,
			StmtDiag::LayoutExpectedLayoutAfterComma(_) => Severity::Error,
			StmtDiag::LayoutExpectedLayoutBetweenParenComma(_) => {
				Severity::Error
			}
			/* VARIABLES */
			StmtDiag::VarDefExpectedSemiOrEqAfterIdents(_) => Severity::Error,
			StmtDiag::VarDeclExpectedSemiAfterValue(_) => Severity::Error,
			StmtDiag::VarDeclExpectedValueAfterEq(_) => Severity::Error,
			/* FUNCTIONS */
			StmtDiag::ParamsExpectedCommaAfterParam(_) => Severity::Error,
			StmtDiag::ParamsExpectedParamAfterComma(_) => Severity::Error,
			StmtDiag::ParamsExpectedParamBetweenParenComma(_) => {
				Severity::Error
			}
			StmtDiag::ParamsInvalidTypeExpr(_) => Severity::Error,
			StmtDiag::ParamsInvalidIdentExpr(_) => Severity::Error,
			StmtDiag::ParamsExpectedRParen(_) => Severity::Error,
			StmtDiag::FnExpectedSemiOrLBraceAfterParams(_) => Severity::Error,
			/* STRUCTS */
			StmtDiag::StructInvalidStmtInBody(_) => Severity::Error,
			StmtDiag::StructExpectedIdentAfterKw(_) => Severity::Error,
			StmtDiag::StructExpectedLBraceAfterIdent(_) => Severity::Error,
			StmtDiag::StructExpectedInstanceOrSemiAfterBody(_) => {
				Severity::Error
			}
			StmtDiag::StructExpectedSemiAfterBodyOrInstance(_) => {
				Severity::Error
			}
			StmtDiag::StructDefIsInvalid(_) => Severity::Error,
			/* SINGLE-KEYWORD CONTROL FLOW */
			StmtDiag::BreakExpectedSemiAfterKw(_) => Severity::Error,
			StmtDiag::ContinueExpectedSemiAfterKw(_) => Severity::Error,
			StmtDiag::DiscardExpectedSemiAfterKw(_) => Severity::Error,
			StmtDiag::ReturnExpectedSemiOrExprAfterKw(_) => Severity::Error,
			StmtDiag::ReturnExpectedSemiAfterExpr(_) => Severity::Error,
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
	/// ERROR - Did not find an identifier token after the `undef` keyword.
	///
	/// - `0` - The span where the macro name is expected.
	UndefExpectedMacroName(Span),
}

impl PreprocDefineDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			/* DEFINE */
			PreprocDefineDiag::DefineExpectedMacroName(_) => Severity::Error,
			/* TOKEN CONCAT */
			PreprocDefineDiag::TokenConcatMissingLHS(_) => Severity::Error,
			PreprocDefineDiag::TokenConcatMissingRHS(_) => Severity::Error,
			/* UNDEF */
			PreprocDefineDiag::UndefExpectedMacroName(_) => Severity::Error,
		}
	}
}

/// Syntax diagnostics for the conditional directives.
#[derive(Debug)]
#[non_exhaustive]
pub enum PreprocConditionalDiag {
	/// ERROR - Found an unmatched `#elif` directive.
	UnmatchedElseIf(Span),
	/// ERROR - Found an unmatched `#else` directive.
	UnmatchedElse(Span),
	/// ERROR - Found an unmatched `#endif` directive.
	UnmatchedEndIf(Span),
}

impl PreprocConditionalDiag {
	pub fn get_severity(&self) -> Severity {
		match self {
			PreprocConditionalDiag::UnmatchedElseIf(_) => Severity::Error,
			PreprocConditionalDiag::UnmatchedElse(_) => Severity::Error,
			PreprocConditionalDiag::UnmatchedEndIf(_) => Severity::Error,
		}
	}
}
