use crate::span::Span;

/// A syntactical/gramatical error.
#[derive(Debug)]
#[non_exhaustive]
pub enum SyntaxErr {
	/* EXPRESSIONS */
	/// In the position that either a binary or postfix operator, or the end-of-expression, was expected to occur,
	/// found an operand. E.g. in `...1 1`, we are missing an operator such as `...1 + 1`.
	///
	/// Note that this error is not produced if we encounter a delimiter, e.g. `...1 (`. In such a case, the
	/// [`Self::FoundClosingDelimInsteadOfOperand`] is produced instead.
	///
	/// - `0` - the span of the previous operand,
	/// - `1` - the span of the current operand.
	FoundOperandAfterOperand(Span, Span),
	/// In the position that a prefix operator was expected to occur, found an operator which is not a valid prefix
	/// operator. E.g. in `...+ *1`, `*` is not a valid prefix.
	///
	/// - `0` - the span of the operator.
	InvalidPrefixOperator(Span),
	/// In the position that either a binary or postfix operator, or the end-of-expression, was expected to occur,
	/// found an operator which is only valid as a prefix. E.g. `val!` instead of `val++`.
	///
	/// - `0` - the span of the operator.
	FoundPrefixInsteadOfPostfix(Span),
	/// In the position that either a prefix operator or operand was expected to occur, found an operator. E.g. in
	/// `...+ [`, we are missing an operand such as `...+ i[`.
	///
	/// - `0` - the span of the previous operator (if there is one),
	/// - `1` - the span of the current operator.
	FoundOperatorInsteadOfOperand(Span, Span),
	/// Found a non-prefix operator as the first item in the expression. E.g. `int /`.
	///
	/// - `0` - the span of the operator.
	FoundOperatorFirstThing(Span),
	/// In the position that either a prefix operator or operand was expected to occur, found a closing delimiter.
	/// E.g. in `...(...+ )`, we are missing an operand such as `...(...+ 5)`.
	///
	/// Note that this error is only produced if a matching opening delimiter exists. If no opening delimiter
	/// exists, [`Self::FoundUnmatchedClosingDelim`] is produced instead.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current closing delimiter.
	FoundClosingDelimInsteadOfOperand(Span, Span),
	/// Found a closing delimiter without the respective opening delimiter. E.g. in `i = 5)`, we are missing the
	/// opening parenthesis such as `i = (5)`. Or in `i = 5 }`, we should likely treat the `}` as a scope end
	/// delimiter (assuming we are inside of a scope).
	///
	/// - `0` - the span of the closing delimiter,
	/// - `1` - whether this is a potential scope delimiter (`}`).
	FoundUnmatchedClosingDelim(Span, bool),
	/// In the position that either a prefix operator or operand was expected to occur, found a comma. E.g. in
	/// `...+ ,` we are missing an operand such as `...+ 5,`.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current comma.
	FoundCommaInsteadOfOperand(Span, Span),
	/// Found a comma as the first item in the expression. E.g. `int ,`.
	///
	/// - `0` - the span of the comma.
	FoundCommaFirstThing(Span),
	/// Found a comma (`,`) at the top-level of the expression, with the parser set to
	/// [`Mode::DisallowTopLevelList`](crate::expression::Mode). E.g. `a, b` would cause this error but `(a, b)`
	/// wouldn't.
	///
	/// - `0` - the span of the comma.
	FoundCommaAtTopLevel(Span),
	/// In the position that either a prefix operator or operand was expected to occur, found a dot. E.g. in
	/// `...+ .` we are missing an operand such as `...+ val.`.
	///
	/// - `0` - the span of the previous operator,
	/// - `1` - the span of the current dot.
	FoundDotInsteadOfOperand(Span, Span),
	/// Found a dot as the first item in the expression. E.g. `int .`.
	///
	/// - `0` - the span of the dot.
	FoundDotFirstThing(Span),
	/// Found an equals sign (`=`), with the parser set to [`Mode::BreakAtEq`](crate::expression::Mode).
	///
	/// - `0` - the span of the equals sign.
	FoundEq(Span),
	/// Found a [`Token`](crate::lexer::Token) which cannot be part of an expression, e.g. `;`.
	///
	/// - `0` - the span of the token.
	FoundInvalidToken(Span),
	/// Found an unclosed parenthesis group, e.g. `(...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	UnclosedParenthesis(Span, Span),
	/// Found an unclosed index operator, e.g. `[...`.
	///
	/// - `0` - the span of the opening `[`,
	/// - `1` - the zero-width span at the end of the expression.
	UnclosedIndexOperator(Span, Span),
	/// Found an unclosed function call, e.g. `fn(...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	UnclosedFunctionCall(Span, Span),
	/// Found an unclosed initializer list, e.g. `{...`.
	///
	/// - `0` - the span of the opening `{`,
	/// - `1` - the zero-width span at the end of the expression.
	UnclosedInitializerList(Span, Span),
	/// Found an unclosed array constructor, e.g. `int[](...`.
	///
	/// - `0` - the span of the opening `(`,
	/// - `1` - the zero-width span at the end of the expression.
	UnclosedArrayConstructor(Span, Span),

	/* LAYOUT QUALIFIER */
	/// Did not find an opening parenthesis (`(`) after the `layout` keyword. E.g. in `layout int`, we are missing
	/// the parenthesis like so `layout(... int`
	///
	/// - `0` - the span where the opening parenthesis should be.
	ExpectedParenAfterLayout(Span),
	/// Did not find a closing parenthesis (`)`) after the layout contents. E.g. in `layout(location = 0`, we are
	/// missing the closing parenthesis like so `layout(location = 0)`.
	///
	/// - `0` - the span of the opening parenthesis,
	/// - `1` - the span where the closing parenthesis should be.
	ExpectedParenAtEndOfLayout(Span, Span),
	/// Found a token which is not a valid layout identifier. E.g. `my_ident` is not a valid layout identifier.
	///
	/// - `0` - the span of the token.
	InvalidLayoutIdentifier(Span),
	/// Did not find an equals sign (`=`) after a layout identifier which takes a value expression. E.g. in
	/// `location`, we are missing the equals sign like so `location =`.
	///
	/// - `0` - the span where the equals sign should be.
	ExpectedEqAfterLayoutIdent(Span),
	/// Did not find an expression after a layout identifier which takes a value expression. E.g. in
	/// `location = `, we are missing the value like so `location = 5`.
	///
	/// - `0` - the span where the expression should be.
	ExpectedValExprAfterLayoutIdent(Span),

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
	/// Did not find either a closing brace (`}`), or a `case` or `default` keyword when parsing a switch
	/// statement. E.g. in `switch { default:`, we are missing a closing brace like so `switch { default: }`.
	///
	/// - `0` - the span of the case opening colon (`:`),
	/// - `1` - the span where the closing brace should be.
	ExpectedSwitchCaseEnd(Span, Span),
	/// Did not find a conditional expression inside the parenthesis when parsing a while loop. E.g. in `while (
	/// if)`, we are expecting an expression not a statement like so `while (true)`.
	/// 
	/// - `0` - the span where the expression should be. 
	ExpectedCondExprForWhile(Span),
	/// Did not find the `while` keyword after the body of a `do` loop. E.g. in `do {...}`, we are missing the
	/// keyword like so `do {...} while ...`.
	/// 
	/// - `0` - the span where the keyword should be.
	ExpectedWhileKwAfterDoBody(Span),

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
	/// - `1` - the span where the closing parenthesis should be (i.e. between the last token of the parameter list
	///   and the `;` or `{`, or `EOF`).
	ExpectedParenAtEndOfParamList(Span, Span),
	/// Did not find a comma after a parameter definition. E.g. in `int v int...`, we are missing a comma like so
	/// `int v, int...`.
	///
	/// - `0` - the span where the comma should be.
	ExpectedCommaAfterParamInParamList(Span),
	/// Found a token signifying the end of a parameter without encountering a type identifier.
	/// E.g. in `int,)`, we are missing a type like so `int, float)`. Or in `, in)`, we are missing a type like so
	/// `, in float)`. Or in `int, in;`, we are missing a type like so `int, in float);`.
	///
	/// - `0` - the span where the type should be (i.e. between the previous token and the current token).
	MissingTypeInParamList(Span),
	/// Did not find either a semi-colon (`;`) or the beginning of the function body (`{`) after the parameter
	/// list. E.g. in `fn(...)`, we are missing a semi-colon like so `fn(...);`.
	///
	/// - `0` - the span where the semi-colon or opening brace should be (i.e. between the parameter list `)` and
	/// the token which is not what we expected).
	ExpectedSemiOrScopeAfterParamList(Span),

	/* STRUCT DEF/DECL */
	/// Did not find an identifier after the `struct` keyword. E.g. in `struct {`, we are missing an identifier
	/// like so `struct Foo {`.
	///
	/// - `0` - the span where the identifier should be.
	ExpectedIdentAfterStructKw(Span),
	/// Did not find the beginning of the struct body (`{`) after the identifier. E.g. in `struct A int`, we are
	/// missing an opening brace like so `struct A { int`.
	///
	/// Note that this error is not produced if a semi-colon (`;`) is encountered. In such a case,
	/// [`Self::StructDefIsIllegal`] is produced instead.
	///
	/// - `0` - the span where the opening brace should be (i.e. between the identifier token and the token which
	///   is not what we expected).
	ExpectedScopeAfterStructIdent(Span),
	/// Found a struct definition like so `struct A;`. This is illegal; GLSL only supports struct declarations.
	///
	/// - `0` - the span of the semi-colon,
	/// - `1` - the span of the entire struct definition.
	StructDefIsIllegal(Span, Span),
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
	/// - `0` - the span where the semi-colon should be (i.e. between the declaration body and the token which is
	///   not what we expected).
	ExpectedSemiAfterStructBody(Span),
}
