use crate::span::Span;

/// A syntactical/gramatical error.
#[derive(Debug)]
pub enum SyntaxErr {
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
}
