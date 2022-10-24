//! All error types that can be emitted.

use crate::Span;

/// A syntactical/gramatical error.
///
/// This enum contains all the possible syntax errors that are emitted by the parser.
#[derive(Debug)]
#[non_exhaustive]
pub enum Diag {
	/* EXPRESSIONS */
	/// In the position that either a binary or postfix operator or the end-of-expression were expected to occur,
	/// we found an operand. E.g.
	/// - `foo bar`
	/// - `5 10`
	///
	/// Note that this error is not produced if we are within a delimited arity group, e.g. `fn(foo bar)`. In such
	/// cases [`Self::ExprExpectedCommaAfterArg`] is produced instead.
	///
	/// - `0` - the span of the previous operand,
	/// - `1` - the span of the current operand.
	ExprFoundOperandAfterOperand(Span, Span),
	/// In the position that a prefix operator or an operand were expected to occur, we found an operator which is
	/// not a valid prefix operator. E.g.
	/// - `foo + *bar`
	/// - `foo + %bar`
	///
	/// Layout:
	/// - `0` - the span of the operator.
	ExprInvalidPrefixOperator(Span),
	/// In the position that either a binary or postfix operator, or the end-of-expression, were expected to occur,
	/// we found an operator which is only valid as a prefix. E.g.
	/// - `foo!`
	/// - `foo~`
	///
	/// Layout:
	/// - `0` - the span of the operator.
	ExprInvalidBinOrPostOperator(Span),
	/// In the position that either a prefix operator or an operand were expected to occur, we found a dot (`.`).
	/// E.g.
	/// - `foo + .`
	/// - `foo.bar(). .`
	/// - `.`
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a dot.
	///
	/// - `0` - the span of the previous operator (if there is one),
	/// - `1` - the span of the dot.
	ExprFoundDotInsteadOfOperand(Option<Span>, Span),
	/// In the position that either a prefix operator or operand were expected to occur, we found a comma. E.g.
	/// `foo + ,`.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current comma.
	ExprFoundCommaInsteadOfOperand(Span, Span),
	/// In the position that either a prefix operator or operand were expected to occur, we found a question mark.
	/// E.g. `foo + ?`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a
	/// question mark.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current question mark.
	ExprFoundQuestionInsteadOfOperand(Option<Span>, Span),
	/// In the position that either a prefix operator or operand were expected to occur, we found a colon.
	/// E.g. `foo ? bar + :`.
	///
	/// Note that this error is generated if the first token encountered when parsing a new expression is a
	/// colon mark.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current colon.
	ExprFoundColonInsteadOfOperand(Option<Span>, Span),
	/// Found a [`Token`](crate::lexer::Token) which cannot be part of an expression. E.g. `;`.
	///
	/// - `0` - the span of the token.
	ExprFoundInvalidToken(Span),
	/* EXPRESSIONS - GROUPS */
	/// Found a parenthesis group that contains no expression. E.g. `()`.
	///
	/// - `0` - the span where the expression should be inserted.
	ExprFoundEmptyParenGroup(Span),
	/// Found an initializer list that contains no expression. E.g. `{}`.
	///
	/// - `0` - the span where the expression should be inserted.
	ExprFoundEmptyInitializerGroup(Span),
	/// In the position that either a prefix operator or an operand were expected to occur, we found the start of
	/// an index operator (`[`). E.g. `foo + [`.
	///
	/// - `0` - the span of the previous operator (if there is one),
	/// - `1` - the span of the opening bracket.
	ExprFoundLBracketInsteadOfOperand(Option<Span>, Span),
	/// In the position that either a prefix operator or an operand were expected to occur, we found a closing
	/// parenthesis (`)`). E.g.
	/// - `(foo + )`
	/// - `fn(bar - )`
	///
	/// Note: this error is not generated if the first token encountered when parsing a new expression is the
	/// closing parenthesis.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span on the closing parenthesis.
	ExprFoundRParenInsteadOfOperand(Span, Span),
	/// In the position that either a prefix operator or an operand were expected to occur, we found a closing
	/// bracket (`]`). E.g. `i[5 + ]`.
	///
	/// Note: this error is not generated if the first token encountered when parsing a new expression is the
	/// closing bracket.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the closing parenthesis.
	ExprFoundRBracketInsteadOfOperand(Span, Span),
	/// In the position that either a prefix operator or an operand were expected to occur, we found a closing
	/// brace (`}`). E.g. `{foo + }`.
	///
	/// Note: this error is not generated if the first token encountered when parsing a new expression is the
	/// closing brace.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span on the closing brace.
	ExprFoundRBraceInsteadOfOperand(Span, Span),
	/* EXPRESSIONS - ARITY */
	/// Did not find a comma after an argument expression in a delimited arity group. E.g.
	/// - `fn(foo bar`
	/// - `{foo bar`
	///
	/// Layout:
	/// - `0` - the span where the comma should be inserted.
	ExprExpectedCommaAfterArg(Span),
	/// Did not find an argument expression after a comma in a delimited arity group. E.g.
	/// - `fn(foo, `
	/// - `{foo, `
	///
	/// Layout:
	/// - `0` - the span where the argument should be inserted.
	ExprExpectedArgAfterComma(Span),
	/// Did not find an argument between the opening parenthesis and the comma. E.g.  `fn( , bar`.
	///
	/// - `0` - the span where the argument should be inserted.
	ExprExpectedArgBetweenParenComma(Span),
	/// Did not find an argument between the opening brace and the comma. E.g. `{ , bar`.
	///
	/// - `0` the span where the argument should be inserted.
	ExprExpectedArgBetweenBraceComma(Span),
	/// Did not find a comma after an expression in a list. E.g. `foo bar`.
	///
	/// - `0` - the span where the comma should be inserted.
	ExprExpectedCommaAfterExpr(Span),
	/// Did not find an expression after a comma in a list. E.g. `foo, `.
	///
	/// - `0 - the span where the expression should be inserted.
	ExprExpectedExprAfterComma(Span),
	/// Did not find an expression before the first comma in a list. E.g. `, bar`.
	///
	/// - `0` - the span where the expression should be inserted.
	ExprExpectedExprBeforeComma(Span),
	/* EXPRESSIONS - UNCLOSED */
	/// Found an unclosed parenthesis group, e.g. `(...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	ExprUnclosedParenthesis(Span, Span),
	/// Found an unclosed index operator, e.g. `[...`.
	///
	/// - `0` - the span of the opening `[`,
	/// - `1` - the zero-width span at the end of the expression.
	ExprUnclosedIndexOperator(Span, Span),
	/// Found an unclosed function call, e.g. `fn(...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	ExprUnclosedFunctionCall(Span, Span),
	/// Found an unclosed initializer list, e.g. `{...`.
	///
	/// - `0` - the span of the opening `{`,
	/// - `1` - the zero-width span at the end of the expression.
	ExprUnclosedInitializerList(Span, Span),
	/// Found an unclosed array constructor, e.g. `int[](...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	ExprUnclosedArrayConstructor(Span, Span),

	/* LAYOUT QUALIFIER */
	/// Did not find an opening parenthesis (`(`) after the `layout` keyword. E.g. in `layout int`, we are missing
	/// the parenthesis like so `layout(... int`
	///
	/// - `0` - the span where the opening parenthesis should be inserted.
	ExpectedParenAfterLayoutKw(Span),
	/// Did not find a closing parenthesis (`)`) after the layout contents. E.g. in `layout(location = 0`, we are
	/// missing the closing parenthesis like so `layout(location = 0)`.
	///
	/// - `0` - the span of the opening parenthesis,
	/// - `1` - the span where the closing parenthesis should be inserted.
	ExpectedParenAtEndOfLayout(Span, Span),
	/// Did not find a layout identifier after the opening parenthesis (`(`). E.g. in `layout( )`, we are missing
	/// an identifier like so `layout(std140)`.
	///
	/// - `0` - the span where the identifier should be inserted.
	ExpectedLayoutIdentAfterParen(Span),
	/// Did not find a layout identifier after a comma. E.g. in `layout(std140, )`, we are missing an identifier
	/// like so `layout(std140, std430)`.
	///
	/// - `0` - the span where the identifier should be inserted.
	ExpectedLayoutIdentAfterComma(Span),
	/// Did not find a comma (`,`) after a layout identifier/expression. E.g. in `layout(std140 std430)`, we are
	/// missing a comma like so `layout(std140, std430)`.
	///
	/// - `0` - the span where the comma should be inserted.
	ExpectedCommaAfterLayoutIdentOrExpr(Span),
	/// Found a token which is not a valid layout identifier. E.g. `my_ident` is not a valid layout identifier.
	///
	/// - `0` - the span of the token.
	InvalidLayoutIdentifier(Span),
	/// Did not find an equals sign (`=`) after a layout identifier that takes a value expression. E.g. in
	/// `location`, we are missing the equals sign like so `location =`.
	///
	/// - `0` - the span where the equals sign should be inserted.
	ExpectedEqAfterLayoutIdent(Span),
	/// Did not find an expression after an equal sign after a layout identifier that takes a value expression.
	/// E.g. in `location = `, we are missing the value like so `location = 5`.
	///
	/// - `0` - the span where the expression should be inserted.
	ExpectedExprAfterLayoutEq(Span),

	/* GENERAL */
	/// Did not find a token which is a valid type identifier. E.g. in `fn(if,`, the `if` is not a valid type.
	///
	/// - `0` - the span of the token/expression which is not a type identifier.
	ExpectedType(Span),
	/// Did not find a token which is a valid identifier. E.g. in `fn(int if)`, the `if` is not a valid identifier.
	///
	/// - `0` - the span of the token/expression which is not an identifier.
	ExpectedIdent(Span),
	/// Did not find a closing brace (`}`) to end an open scope. E.g. in `fn(){ int a;`, we are missing a closing
	/// brace like so `fn(){ int a; }`.
	///
	/// - `0` - the span of the opening brace,
	/// - `1` - the span where the closing brace should be.
	ExpectedBraceScopeEnd(Span, Span),
	/// Found a sole expression without a semi-colon (`;`) afterwards. E.g. `int` is an expression which is not a
	/// valid statement, but `int;` is.
	///
	/// - `0` - the span of the expression.
	ExpectedStmtFoundExpr(Span),

	/* CONTROL FLOW */
	/// Did not find an opening parenthesis (`(`) after a `if`/`switch`/`for`/`while` keyword. E.g. in
	/// `if true...`, we are missing a parenthesis like so `if (true...`.
	///
	/// - `0` - the span where the opening parenthesis should be.
	ExpectedParenAfterControlFlowKw(Span),
	/// Did not find a closing parenthesis (`)`) after a control flow expression. E.g. in `if (true {`, we are
	/// missing a parenthesis like so `if (true) {`.
	///
	/// - `0` - the span of the opening parenthesis if it exists,
	/// - `1` - the span where the closing parenthesis should be.
	ExpectedParenAfterControlFlowExpr(Option<Span>, Span),
	/// Did not find an opening brace (`{`) after a control flow expression. E.g. in `if (true) ...`, we are
	/// missing an opening brace like so `if (true) {...`.
	///
	/// - `0` - the span where the opening brace should be.
	ExpectedScopeAfterControlFlowExpr(Span),
	/// Did not find a semi-colon (`;`) after a control flow statement. E.g. in `break`, we are missing a
	/// semi-colon like so `break;`. Or in `return 5 + 1`, like so `return 5 + 1;`.
	///
	/// - `0` the span where the semi-colon should be (i.e. between the control flow and the token which is not
	///   what we expected).
	ExpectedSemiAfterControlFlow(Span),
	/* IF */
	/// Did not find an opening parenthesis (`(`) after the `if` keyword.
	///
	/// - `0` - the position where the parenthesis should be inserted.
	ExpectedParenAfterIfKw(Span),
	/// Did not find a conditional expression inside the parenthesis when parsing an if statement. E.g. in `if (
	/// struct)`, we are expecting an expression not a statement like so `if (true)`.
	///
	/// - `0` - the span where the expression should be.
	ExpectedExprInIfHeader(Span),
	/// Did not find a closing parenthesis (`)`) for the if header.
	///
	/// - `0` - the span of the opening parenthesis if it exists,
	/// - `1` - the position where the parenthesis should be inserted.
	ExpectedParenAfterIfHeader(Option<Span>, Span),
	/// Did not find either a body `{...}` or a statement after the if header.
	///
	/// - `0` - the position where the brace or statement should be inserted.
	ExpectedBraceOrStmtAfterIfHeader(Span),
	/// Did not find a single statement after the if header.
	///
	/// - `0` - the position where the statement should be inserted.
	ExpectedStmtAfterIfHeader(Span),
	/// Did not find either a body `{...}` or a statement or the `if` keyword after the `else` keyword.
	///
	/// - `0` - the position where the item should be inserted.
	ExpectedIfOrBodyAfterElseKw(Span),
	/* SWITCH */
	/// Did not find an opening parenthesis (`(`) after the `switch` keyword.
	///
	/// - `0` - the position where the parenthesis should be inserted.
	ExpectedParenAfterSwitchKw(Span),
	/// Did not find a switch header after the `switch` keyword.
	///
	/// - `0` - the span between the `switch` keyword and the `{` where the header should be.
	MissingSwitchHeader(Span),
	/// Did not find a conditional expression inside the parenthesis when parsing a switch. E.g. in `switch ()`,
	/// we are expecting an expression like so `switch (val)`.
	///
	/// - `0` - the span between the parenthesis where the expression should be, or between the `switch` or `{` if
	///   either of the parenthesis are missing.
	ExpectedExprInSwitchHeader(Span),
	/// Did not find a closing parenthesis (`)`) for the switch header.
	///
	/// - `0` - the span of the opening parenthesis if it exists,
	/// - `1` - the position where the parenthesis should be inserted.
	ExpectedParenAfterSwitchHeader(Option<Span>, Span),
	/// Did not find a body after the switch header.
	///
	/// - `0` - the position where the brace should be inserted.
	ExpectedBraceAfterSwitchHeader(Span),
	/// Did not find a single case within the switch body.
	///
	/// - `0` - the span of the body.
	FoundEmptySwitchBody(Span),
	/// Did not find an expression after the `case` keyword.
	///
	/// - `0` - the position the expression should be inserted.
	ExpectedExprAfterCaseKw(Span),
	/// Did not find a colon (`:`) after the case expression or `default` keyword.
	///
	/// - `0` - the position the colon should be inserted.
	ExpectedColonAfterCase(Span),
	/// Found a token to start switch case other than `case` or `default`.
	///
	/// - `0` - the span of the token.
	InvalidSwitchCaseBegin(Span),
	/// Did not find a closing brace (`}`) to close the switch body.
	///
	/// - `0` - the span of the body opening brace if it exists,
	/// - `1` - the position where the brace should be inserted.
	MissingSwitchBodyClosingBrace(Option<Span>, Span),
	/* FOR-LOOP */
	/// Did not find an opening parenthesis (`(`) after the `for` keyword.
	///
	/// - `0` - the position where the parenthesis should be inserted.
	ExpectedParenAfterForKw(Span),
	/// Did not find a for-loop header after the `for` keyword
	///
	/// - `0` - the span between the `for` keyword and the `{` where the header should be.
	MissingForHeader(Span),
	/// Did not find anything within the for-loop header parenthesis.
	///
	/// - `0` - the span between the parenthesis.
	FoundEmptyForHeader(Span),
	/// Did not find an expression within the for-loop header.
	///
	/// - `0` - the span of the tokens which are not an expression.
	ExpectedExprInForFoundElse(Span),
	/// Did not find a semi-colon (`;`) after a for-loop header statement or expression.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterForStmtExpr(Span),
	/// Found a trailing semi-colon (`;`) after the 3rd expression in the for-loop header.
	///
	/// - `0` - the span of the semi-colon that needs to be removed.
	FoundTrailingSemiAfter3rdExprInFor(Span),
	/// Found less than one statement/expression and 2 expressions in the for-loop header.
	///
	/// - `0` - the span between the parenthesis where the statement/expressions should be, or between the `for` or
	///   `{` if either of the parenthesis are missing.
	Expected3StmtExprInFor(Span),
	/// Found more than one statement/expression and 2 expressions in the for-loop header.
	///
	/// - `0` - the span of the extra expressions that need to be removed.
	FoundMoreThan3StmtExprInFor(Span),
	/// Did not find a closing parenthesis (`)`) for the for-loop header.
	///
	/// - `0` - the span of the opening parenthesis if it exists,
	/// - `1` - the position where the parenthesis should be inserted.
	ExpectedParenAfterForHeader(Option<Span>, Span),
	/// Did not find a body after the for-loop header.
	///
	/// - `0` - the position where the brace should be inserted.
	ExpectedBraceAfterForHeader(Span),
	/* WHILE-LOOP */
	/// Did not find an opening parenthesis (`(`) after the `while` keyword.
	///
	/// - `0` - the position where the parenthesis should be inserted.
	ExpectedParenAfterWhileKw(Span),
	/// Did not find a conditional expression inside the parenthesis when parsing a while-loop. E.g. in `while ()`,
	/// we are expecting an expression like so `while (true)`.
	///
	/// - `0` - the span between the parenthesis where the expression should be, or between the `while` or `{` if
	///   either of the parenthesis are missing.
	ExpectedCondExprAfterWhile(Span),
	/// Did not find a closing parenthesis (`)`) after the while-loop condition.
	///
	/// - `0` - the span of the opening parenthesis if it exists,
	/// - `1` - the position where the parenthesis should be inserted.
	ExpectedParenAfterWhileCond(Option<Span>, Span),
	// TODO: ExpectedBraceAfterWhileHeader(Span),
	/* DO-WHILE-LOOP */
	/// Did not find an opening brace (`{`) after the `do` keyword.
	///
	/// - `0` - the position where the brace should be inserted.
	ExpectedBraceAfterDoKw(Span),
	/// Did not find a body between the `do` and `while` keywords.
	///
	/// - `0` - the span where the body should be.
	ExpectedScopeAfterDoKw(Span),
	/// Did not find the `while` keyword after the body of a do-loop.
	///
	/// - `0` - the position where the keyword should be inserted.
	ExpectedWhileKwAfterDoBody(Span),
	/// Did not find a semi-colon (`;`) after a do-while loop.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterDoWhileStmt(Span),
	/* SINGLE-WORD */
	/// Did not find a semi-colon (`;`) or an expression after the `return` keyword.
	///
	/// - `0` - the position where the semi-colon or expression should be inserted,
	ExpectedSemiOrExprAfterReturnKw(Span),
	/// Did not find a semi-colon (`;`) after the `return` expression.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterReturnExpr(Span),
	/// Did not find a semi-colon (`;`) after the `break` keyword.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterBreakKw(Span),
	/// Did not find a semi-colon (`;`) after the `continue` keyword.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterContinueKw(Span),
	/// Did not find a semi-colon (`;`) after the `discar` keyword.
	///
	/// - `0` - the position where the semi-colon should be inserted.
	ExpectedSemiAfterDiscardKw(Span),

	/* VAR DEF/DECL */
	/// Did not find identifier(s) after a type identifier. E.g. `int 5` would be an invalid identifier, but `int
	/// a` wouldn't be.
	///
	/// - `0` - the span where the identifier should be.
	ExpectedIdentsAfterVarType(Span),
	/// Did not find either a semi-colon (`;`) or an equals sign (`=`) after parsing a variable definition(s). E.g.
	/// in `int a`, we are missing a semi-colon like so `int a;`.
	///
	/// - `0` - the span where the semi-colon or equals sign should be (i.e. between the variable identifier(s) and
	///   the token which is not what we expected).
	ExpectedSemiOrEqAfterVarDef(Span),
	/// Did not find a semi-colon (`;`) after the expression in a variable declaration(s). E.g. in `int a = 5`, we
	/// are missing a semi-colon like so `int a = 5;`.
	///
	/// - `0` - the span where the semi-colon should be (i.e. between the expression and the token which is not
	///   what we expected).
	ExpectedSemiAfterVarDeclExpr(Span),
	/// Did not find a value expression after the equals sign in a variable declaration. E.g. in `int a = ;`, we
	/// are missing an expression such as `int a = 5;`.
	///
	/// - `0` - the span where the expression should be (i.e. between the equals sign and the token which is not
	///   what we expected).
	ExpectedExprAfterVarDeclEq(Span),

	/* FUNCTION DEF/DECL */
	/// Did not find a closing parenthesis (`)`) at the end of the parameter list. E.g. in `fn(void`, we are
	/// missing closing parenthesis like so `fn(void)`.
	///
	/// - `0` - the span of the opening parenthesis,
	/// - `1` - the span where the closing parenthesis should be inserted.
	ExpectedParenAtEndOfParamList(Span, Span),
	/// Did not find a parameter between the opening parenthesis (`(`) and a comma (`,`). E.g. in `fn( , int)`, we
	/// are missing a parameter like so `fn(float, int)`.
	///
	/// - `0` - the span where the parameter should be inserted.
	ExpectedParamBetweenParenComma(Span),
	/// Did not find a parameter after a comma. E.g. in `fn(int, )`, we are missing a parameter like so `fn(int,
	/// float)`.
	///
	/// - `0` the span where the parameter should be.
	ExpectedParamAfterComma(Span),
	/// Did not find a comma (`,`) after a parameter. E.g. in `fn(int v int)`, we are missing a comma like so
	/// `fn(int v, int)`.
	///
	/// - `0` - the span where the comma should be inserted.
	ExpectedCommaAfterParam(Span),

	/// Found a token signifying the end of a parameter without encountering a type identifier.
	/// E.g. in `int,)`, we are missing a type like so `int, float)`. Or in `, in)`, we are missing a type like so
	/// `, in float)`. Or in `int, in;`, we are missing a type like so `int, in float);`.
	///
	/// - `0` - the span where the type should be (i.e. between the previous token and the current token).
	MissingTypeInParamList(Span),
	/// Did not find either a semi-colon (`;`) or the beginning of the function body (`{`) after the parameter
	/// list. E.g. in `fn(...)`, we are missing a semi-colon like so `fn(...);`.
	///
	/// - `0` - the span where the semi-colon or opening brace should be inserted.
	ExpectedSemiOrScopeAfterParamList(Span),

	/* STRUCT DEF/DECL */
	/// Did not find an identifier after the `struct` keyword. E.g. in `struct {`, we are missing an identifier
	/// like so `struct Foo {`.
	///
	/// - `0` - the span where the identifier should be inserted.
	ExpectedIdentAfterStructKw(Span),
	/// Did not find the beginning of the struct body (`{`) after the identifier. E.g. in `struct A int`, we are
	/// missing an opening brace like so `struct A { int`.
	///
	/// Note that this error is not produced if a semi-colon (`;`) is encountered. In such a case,
	/// [`Self::StructDefIsIllegal`] is produced instead.
	///
	/// - `0` - the span where the opening brace should be inserted.
	ExpectedScopeAfterStructIdent(Span),
	/// Found a statement other than a variable definition within a struct body. E.g. in `struct A { if...`, we
	/// have an if-statement which is illegal.
	///
	/// - `0` - the span of the illegal statement.
	ExpectedVarDefInStructBody(Span),
	/// Did not find at least one variable definition statement within a struct body. E.g. in `struct A {};`, we
	/// are missing a member like so `struct A { int a; };`.
	///
	/// - `0` - the span of the struct body.
	ExpectedAtLeastOneMemberInStruct(Span),
	/// Did not find a semi-colon (`;`) after the struct declaration. E.g. in `struct A {...}`, we are missing a
	/// semi-colon like so `struct A {...};`.
	///
	/// - `0` - the span where the semi-colon should be inserted.
	ExpectedSemiAfterStructBody(Span),

	/* ILLEGAL STATEMENTS */
	/// Found a struct definition. This is not allowed in GLSL.
	StructDefIsIllegal(Span),
	/// Found a statement beginning with a reserved keyword.
	///
	/// - `0` - the span of the keyword.
	FoundIllegalReservedKw(Span),
	/// Found an illegal character.
	///
	/// - `0` - the span of the character,
	/// - `1` - the character.
	FoundIllegalChar(Span, char),
	/// Found a statement beginning with a punctuation symbol (not `{` or `}` or `;`).
	///
	/// - `0` - the span of the punctuation.
	PunctuationCannotStartStmt(Span),
	/// Found an unopened closing brace (`}`).
	///
	/// - `0` - the span of the brace.
	FoundLonelyRBrace(Span),
	/// Expected a function or variable definition/declaration after one or more qualifiers.
	///
	/// - `0` - the span where the def/decl should be inserted.
	ExpectedDefDeclAfterQualifiers(Span),

	/* ILLEGAL STATEMENTS AT TOP-LEVEL */
	/// Found an expression-statement the top-level of a file.
	///
	/// - `0` - the span of the statement.
	ExprStmtIsIllegalAtTopLevel(Span),
	/// Found an scope `{...}` at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	ScopeStmtIsIllegalAtTopLevel(Span),
	/// Found an if-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	IfStmtIsIllegalAtTopLevel(Span),
	/// Found a switch-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	SwitchStmtIsIllegalAtTopLevel(Span),
	/// Found an for-loop statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	ForStmtIsIllegalAtTopLevel(Span),
	/// Found an while-loop statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	WhileStmtIsIllegalAtTopLevel(Span),
	/// Found an do-while-loop statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	DoWhileStmtIsIllegalAtTopLevel(Span),
	/// Found a return-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	ReturnStmtIsIllegalAtTopLevel(Span),
	/// Found a break-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	BreakStmtIsIllegalAtTopLevel(Span),
	/// Found a continue-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	ContinueStmtIsIllegalAtTopLevel(Span),
	/// Found a discard-statement at the top-level of a file.
	///
	/// - `0` - the span of the statement.
	DiscardStmtIsIllegalAtTopLevel(Span),

	/* ILLEGAL STATEMENTS INSIDE OF FUNCTIONS */
	/// Found a function-statement within a function body.
	///
	/// - `0` - the span of the statement.
	FnStmtIsIllegalInFn(Span),
	/// Found a struct-statement within a function body.
	///
	/// - `0` - the span of the statement.
	StructStmtIsIllegalInFn(Span),
	/// Found a break-statement within a function body but outside of a loop statement.
	///
	/// - `0` - the span of the statement.
	BreakStmtIsIllegalInFnOutsideLoop(Span),
	/// Found a continue-statement within a function body but outside of a loop statement.
	///
	/// - `0` - the span of the statement.
	ContinueStmtIsIllegalInFnOutsideLoop(Span),

	/* TEMPORARY */
	/// Directives are currently unsupported.
	DirectivesNotSupported(Span),

	/// WARNING - Found a macro call site, but the macro contains no replacement tokens.
	///
	/// - `0` - the span of the call site.
	EmptyMacroCallSite(Span),

	/// A preprocessor diagnostic.
	Preproc(PreprocDiag),
	/// Diagnostics for the `#define` and `#undef` directives.
	PreprocDefine(PreprocDefineDiag),
	/// ERROR - Found trailing tokens in a directive.
	///
	/// - `0` - The span of the tokens.
	PreprocTrailingTokens(Span),
}

/// A preprocessor syntax diagnostic.
///
/// - Errors for the `#version` directive begin with `Version*`.
#[derive(Debug)]
pub enum PreprocDiag {
	/// WARNING - Found a preprocessor directive which contains nothing apart from the beginning `#`.
	///
	/// - `0` - the span of the directive.
	FoundEmptyDirective(Span),
	/// ??? - Found a line directive which contains no value, e.g. `#line \n`.
	///
	/// - `0` - the span of the directive.
	FoundEmptyLineDirective(Span),
	/// WARNING - Found an error directive which contains no message, e.g. `#error \n`.
	///
	/// - `0` - the span of the directive.
	FoundEmptyErrorDirective(Span),
	/// WARNING - Found a pragma directive which contains no option, e.g. `#pragma \n`.
	///
	/// - `0` - the span of the directive.
	FoundEmptyPragmaDirective(Span),

	/* VERSION DIRECTIVE */
	/// ERROR - Expected the version number but found a non-number token or nothing. E.g.
	/// - `#version foobar`,
	/// - `#version`.
	///
	/// Note: If the token is a valid profile, e.g. `#version core`, then the
	/// [`VersionMissingNumber`](PreprocDiag::VersionMissingNumber) diagnostic will be produced instead.
	///
	/// - `0` - the span of the invalid token or the position the number should be inserted at.
	VersionExpectedNumber(Span),
	/// ERROR - Found a number token that isn't a valid version number, e.g. `#version 19617527`.
	///
	/// - `0` - the span of the number token.
	VersionInvalidNumber(Span),
	/// ERROR - Found a valid version number that is unsupported by the extension, e.g. `#version 430`.
	///
	/// - `0` - the span of the number token.
	VersionUnsupportedNumber(Span),
	/// ERROR - Found a profile but no version number, e.g. `#version core`.
	///
	/// - `0` - the span where the version number should be inserted.
	VersionMissingNumber(Span),
	/// ERROR - Expected the profile but found a non-word token, e.g.`#version 450 300`,
	///
	/// - `0 - the span of the invalid token.
	VersionExpectedProfile(Span),
	/// ERROR - Found a word token that isn't a valid profile, e.g. `#version 450 foobar`.
	///
	/// - `0` - the span of the word token.
	VersionInvalidProfile(Span),
	/// ERROR - Found a word token that would be a valid profile with the correct capitalization, e.g. `#version
	/// 450 CoRe`.
	///
	/// - `0` - the span of the word token,
	/// - `1` - the correct spelling.
	VersionInvalidProfileCasing(Span, &'static str),
	/// ERROR - Found trailing token(s) after the version number/profile, e.g. `#version 450 core s1_sfh_5`.
	///
	/// - `0` - the span of the trailing token(s).
	VersionTrailingTokens(Span),

	/* EXTENSION DIRECTIVE */
	/// ERROR - Expected the name but found a non-word token or nothing. E.g.
	/// - `#extension 155151`,
	/// - `#extension`.
	///
	/// - `0` - the span of the invalid token or the position the name should be inserted at.
	ExtensionExpectedName(Span),
	/// ERROR - Found a colon but no name, e.g. `#extension :`.
	///
	/// - `0` - the span where the name should be inserted.
	ExtensionMissingName(Span),
	/// ERROR - Expected a colon but found a non-colon token or nothing. E.g.
	/// - `#extension foobar baz`,
	/// - `#extension foobar`.
	///
	/// - `0` - the span of the invalid token or the position the colon should be inserted at.
	ExtensionExpectedColon(Span),
	/// ERROR - Expected a colon but found a behaviour, e.g. `#extension foobar enable`.
	///
	/// - `0` - the span where the colon should be inserted.
	ExtensionMissingColon(Span),
	/// ERROR - Expected a behaviour but found a non-word token or nothing. E.g.
	/// - `#extension foobar : @@@`,
	/// - `#extension foobar :`.
	///
	/// - `0` - the span of the invalid token or the position the behaviour should be inserted at.
	ExtensionExpectedBehaviour(Span),
	/// ERROR - Found a word token that isn't a valid behaviour, e.g. `#extension foo : bar`.
	///
	/// - `0` - the span of the word token.
	ExtensionInvalidBehaviour(Span),
	/// ERROR - Found a word token that would be a valid behaviour with the correct capitalization, e.g.
	/// `#extension foobar: EnAbLe`.
	///
	/// - `0` - the span of the word token,
	/// - `1` - the correct spelling.
	ExtensionIncorrectBehaviourCasing(Span, &'static str),
	/// ERROR - Found trailing token(s) after the name/behaviour, e.g. `#extension foobar : enable baz2@@`.
	///
	/// - `0` - the span of the trailing token(s).
	ExtensionTrailingTokens(Span),

	/// ERROR - Found a token concatenation operator (`##`) outside of a directive's content, e.g. `\r\n /* comment
	/// */ ##`.
	///
	/// - `0` - the span of the operator.
	FoundTokenConcatOutsideOfDirective(Span),
}

#[derive(Debug)]
pub enum PreprocDefineDiag {
	/* DEFINE */
	/// ERROR - Did not find an identifier token after the define keyword.
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
	/// ERROR - Did not find an identifier token after the undef keyword.
	///
	/// - `0` - The span where the macro name is expected.
	UndefExpectedMacroName(Span),
}
