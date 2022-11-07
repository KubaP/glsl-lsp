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
//! order to provide very specific diagnostics without having to hardcode `&'static` strings everywhere. In order
//! to make the amount more managable, most diagnostics are split into nested enums.

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
	/// ERROR - Found an illegal character.
	///
	/// - `0` - The span of the character,
	/// - `1` - The character.
	FoundIllegalChar(Span, char),
	/// ERROR - Found a reserved keyword.
	///
	/// - `0` - The span of the keyword,
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

	/// ERROR - Found a block comment that is missing the closing tag.
	///
	/// - `0` - The span where the closing tag is expected.
	BlockCommentMissingEnd(Span),
}

impl Syntax {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
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
		Severity::Error
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

	/* IF */
	/// ERROR - Did not find an opening parenthesis after the `if` keyword.
	///
	/// - `0` - The span where the opening parenthesis is expected.
	IfExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The span where the expression is expected.
	IfExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	IfExpectedRParenAfterExpr(Span),
	// ERROR - Did not find an opening brace after the if condition.
	///
	/// - `0` - The span where the opening brace is expected.
	IfExpectedLBraceOrExprAfterCond(Span),

	/* SWITCH */
	/// ERROR - Did not find an opening parenthesis after the `switch` keyword.
	///
	/// - `0` - The span where the opening parenthesis is expected.
	SwitchExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The span where the expression is expected.
	SwitchExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	SwitchExpectedRParenAfterExpr(Span),
	/// ERROR - Did not find an opening brace after the switch condition.
	///
	/// - `0` - The span where the opening brace is expected.
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
	/// - `0` - The span where the expression is expected.
	SwitchExpectedExprAfterCaseKw(Span),
	/// ERROR - Did not find a colon after the case expression.
	///
	/// - `0` - The span where the colon is expected.
	SwitchExpectedColonAfterCaseExpr(Span),
	/// ERROR - Did not find a colon after the `default` keyword.
	///
	/// - `0` - The span where the colon is expected.
	SwitchExpectedColonAfterDefaultKw(Span),
	/// ERROR - Did not find a closing brace at the end of the body.
	///
	/// - `0` - The span where the brace is expected.
	SwitchExpectedRBrace(Span),

	/* FOR LOOPS */
	/// ERROR - Did not find an opening parenthesis after the `for` keyword.
	///
	/// - `0` - The span where the opening parenthesis is expected.
	ForExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an initialization statement after the opening parenthesis.
	///
	/// - `0` - The span where the statement is expected.
	ForExpectedInitStmt(Span),
	/// ERROR - Did not find a conditional statement after the opening parenthesis.
	///
	/// - `0` - The span where the statement is expected.
	ForExpectedCondStmt(Span),
	/// ERROR - Did not find an increment statement after the opening parenthesis.
	///
	/// - `0` - The span where the statement is expected.
	ForExpectedIncStmt(Span),
	/// ERROR - Did not find all 3 statements before reaching the closing parenthesis.
	///
	/// - `0` - The span where the statements were expected.
	ForExpected3Stmts(Span),
	/// ERROR - Did not find a closing parenthesis after the 3 statements.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	ForExpectedRParenAfterStmts(Span),
	/// ERROR - Did not find an opening brace after the for header.
	///
	/// - `0` - The span where the opening brace is expected.
	ForExpectedLBraceAfterHeader(Span),

	/* DO/WHILE LOOPS */
	/// ERROR - Did not find an opening parenthesis after the `while` keyword.
	///
	/// - `0` - The span where the opening parenthesis is expected.
	WhileExpectedLParenAfterKw(Span),
	/// ERROR - Did not find an expression after the opening parenthesis.
	///
	/// - `0` - The span where the expression is expected.
	WhileExpectedExprAfterLParen(Span),
	/// ERROR - Did not find a closing parenthesis after the expression.
	///
	/// - `0` - The span where the closing parenthesis is expected.
	WhileExpectedRParenAfterExpr(Span),
	/// ERROR - Did not find an opening brace after the while-loop condition.
	///
	/// - `0` - The span where the opening brace is expected.
	WhileExpectedLBraceAfterCond(Span),
	/// ERROR - Did not find an opening brace after the `do` keyword.
	///
	/// - `0` - The span where the opening brace is expected.
	DoWhileExpectedLBraceAfterKw(Span),
	/// ERROR - Did not find the `while` keyword after the body of a do-while loop.
	///
	/// - `0` - The span where the keyword is expected.
	DoWhileExpectedWhileAfterBody(Span),
	/// ERROR - Did not find a semi-colon after the do-while-loop condition.
	///
	/// - `0` - The span where the semi-colon is expected.
	DoWhileExpectedSemiAfterRParen(Span),

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
		Severity::Error
	}
}

/// Syntax diagnostics for the `#version` directive.
#[derive(Debug)]
#[non_exhaustive]
pub enum PreprocVersionDiag {
	/// ERROR - Did not find a number after the `version` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the number should be inserted.
	ExpectedNumber(Span),
	/// ERROR - Did not find a number after the `version` keyword, but did find a profile. E.g. `#version core`.
	///
	/// - `0` - The span between the keyword and profile.
	MissingNumberBetweenKwAndProfile(Span),
	/// ERROR - Found a number-like token which can't be successfully parsed as a number for the version. E.g.
	/// `#version 19617527`.
	///
	/// - `0` - The span of the number-like token.
	InvalidNumber(Span),
	/// ERROR - Found a version number that is not a valid GLSL version. E.g. `#version 480`.
	///
	/// - `0` - The span of the nubmer,
	/// - `1` - The number.
	InvalidVersion(Span, usize),
	/// ERROR - Found a version number that is not currently supported by this crate. E.g. `#version 300`.
	///
	/// - `0` - The span of the number,
	/// - `1` - The number.
	UnsupportedVersion(Span, usize),
	/// ERROR - Did not find a profile after the version number.
	///
	/// - `0` - The span of the incorrect token or the position where the profile should be inserted.
	ExpectedProfile(Span),
	/// ERROR - Found a word token that isn't a valid profile. E.g. `#version 450 foobar`.
	///
	/// - `0` - The span of the word.
	InvalidProfile(Span),
	/// ERROR - Found a word token that would be a valid profile with the correct capitalization. E.g. `#version
	/// 450 CoRe`.
	///
	/// - `0` - The span of the word,
	/// - `1` - The corrected spelling.
	InvalidProfileCasing(Span, &'static str),
}

impl PreprocVersionDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

/// Syntax diagnostics for the `#extension` directive.
#[derive(Debug)]
#[non_exhaustive]
pub enum PreprocExtDiag {
	/// ERROR - Did not find an extension name after the `extension` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the name should be inserted.
	ExpectedName(Span),
	/// ERROR - Did not find a name after the `extension` keyword, but did find a colon. E.g. `#extension :
	/// enable`.
	///
	/// - `0` - The span between the keyword and colon.
	MissingNameBetweenKwAndColon(Span),
	/// ERROR - Did not find a number after the `extension` keyword, but did find a behaviour. E.g. `#extension
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
	/// - `0` - The span of the incorrect token or the position where the colon should be inserted.
	ExpectedColon(Span),
	/// ERROR - Did not find a behaviour after the colon.
	///
	/// - `0` - The span of the incorrect token or the position where the behaviour should be inserted.
	ExpectedBehaviour(Span),
	/// ERROR - Found a word token that isn't a valid behaviour. E.g. `#extension all : foobar`.
	///
	/// - `0` - The span of the word.
	InvalidBehaviour(Span),
	/// ERROR - Found a word token that would be a valid behaviour with the correct capitalization. E.g. `#extension
	/// all : EnAbLe`.
	///
	/// - `0` - The span of the word,
	/// - `1` - The corrected spelling.
	InvalidBehaviourCasing(Span, &'static str),
}

impl PreprocExtDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
	}
}

/// Syntax diagnostics for the `#line` directive.
#[derive(Debug)]
#[non_exhaustive]
pub enum PreprocLineDiag {
	/// ERROR - Did not find a number after the `line` keyword.
	///
	/// - `0` - The span of the incorrect token or the position where the number should be inserted.
	ExpectedNumber(Span),
	/// ERROR - Found a number-like token which can't be successfully parsed as a line number. E.g.
	/// `#line 100000000000000000000`.
	///
	/// - `0` - The span of the number-like token.
	InvalidNumber(Span),
}

impl PreprocLineDiag {
	pub fn get_severity(&self) -> Severity {
		Severity::Error
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
		Severity::Error
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
		Severity::Error
	}
}
