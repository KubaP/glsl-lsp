use crate::File;
use glsl_parser::{
	error::SyntaxErr::{self, *},
	span::Span,
};
use tower_lsp::lsp_types::{
	Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location,
};

/// Converts a [`SyntaxErr`] to an LSP `Diagnostic` type.
pub fn to_diagnostic(err: SyntaxErr, file: &File, diags: &mut Vec<Diagnostic>) {
	let (message, span, related) = match err {
		/* EXPRESSION */
        FoundOperandAfterOperand(prev, current) => (
            "Syntax error: expected binary operator between the operands",
            Span::new_between(prev, current),
            None
        ),
		InvalidPrefixOperator(token) => (
            "Syntax error: invalid prefix operator",
            token,
            None
        ),
		FoundPrefixInsteadOfPostfix(token) => (
            "Syntax error: invalid postfix operator",
            token,None
        ),
		FoundOperatorInsteadOfOperand(prev, current) => (
            "Syntax error: expected an operand between the operators",
            Span::new_between(prev, current),
            None
        ),
		FoundOperatorFirstThing(token) => (
            "Syntax error: expression cannot start with a non-prefix operator",
            token,None
        ),
		FoundClosingDelimInsteadOfOperand(prev, current) => (
            "Syntax error: expected an operand between the operator and delimiter",
            Span::new_between(prev, current),None
        ),
		FoundUnmatchedClosingDelim(token, _) => (
            "Syntax error: found unmatched closing delimiter",
            token,None
        ),
		FoundCommaInsteadOfOperand(prev, current) => (
            "Syntax error: expected an operand between the operator and comma",
            Span::new_between(prev, current),
            None
        ),
		FoundCommaFirstThing(token) => (
            "Syntax error: expression cannot start with a comma `,`",
            token,
            None
        ),
		FoundCommaAtTopLevel(_) => todo!(),
		FoundDotInsteadOfOperand(op, dot) => (
            "Syntax error: expected operand between operator and dot `.`",
            Span::new_between(op, dot),
            None
        ),
		FoundDotFirstThing(token) => (
            "Syntax error: expression cannot start with a dot `.`",
            token,
            None
        ),
		FoundEq(_token) => todo!(),
		FoundInvalidToken(token) => (
            "Syntax error: invalid token",
            token,
            None,
        ),
		UnclosedParenthesis(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
		UnclosedIndexOperator(opening, expected) => (
            "Syntax error: expected a closing delimiter `]`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
		UnclosedFunctionCall(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
		UnclosedInitializerList(opening, expected) => (
            "Syntax error: expected a closing delimiter `}`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
		UnclosedArrayConstructor(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
        /* LAYOUT QUALIFIER */
		ExpectedParenAfterLayout(pos) => (
            "Syntax error: expected an opening delimiter `(`",
            pos,
            None
        ),
		ExpectedParenAtEndOfLayout(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(("opening delimiter here", opening)),
        ),
		InvalidLayoutIdentifier(token) => (
            "Syntax error: invalid layout identifier",
            token,
            None
        ),
		ExpectedEqAfterLayoutIdent(pos) => (
            "Syntax error: expected an equals-sign `=`",
            pos,
            None
        ),
		ExpectedValExprAfterLayoutIdent(pos) => (
            "Syntax error: expected an expression",
            pos,
            None
        ),
        /* GENERAL */
		ExpectedType(token) => (
            "Syntax error: expected a type",
            token,
            None,
        ),
		ExpectedIdent(token) => (
            "Syntax error: expected an identifier",
            token,
            None
        ),
        ExpectedBraceScopeEnd(opening, expected) => (
            "Syntax error: expected a closing scope delimiter `}`",
            expected,
            Some(("opening delimiter here", opening))
        ),
        ExpectedStmtFoundExpr(expr) => (
            "Syntax error: expected a statement, found an expression",
            expr,
            Some(("consider adding a semi-colon `;` here", expr.end_zero_width())),
        ),
        /* CONTROL FLOW */
        ExpectedParenAfterControlFlowKw(pos) => (
            "Syntax error: expected opening parenthesis `(`",
            pos,
            None
        ),
        ExpectedParenAfterControlFlowExpr(opening, pos) => (
            "Syntax error: expected closing parenthesis `)`",
            pos,
            opening.map(|span| ("opening delimiter here", span))
        ),
        ExpectedScopeAfterControlFlowExpr(pos) => (
            "Syntax error: expected opening brace `{`",
            pos,
            None
        ),
        ExpectedSemiAfterControlFlow(pos) => (
            "Syntax error: expected a semi-colon `;`",
            pos,
            None,
        ),
        ExpectedSwitchCaseEnd(opening, expected) => (
            "Syntax error: expected a closing delimiter for the switch case; one of either `case`, `default` or `}`",
            expected,
            Some(("case opening delimiter here", opening))
        ),
        ExpectedSemiInForCond(pos) => (
            "Syntax error: expected a semi-colon `;`",
            pos,
            None
        ),
        MissingCondExprInFor(span) => (
            "Syntax error: expected a condition expression",
            span,
            None
        ),
        MissingIncrementExprInFor(span) => (
            "Syntax error: expected an increment expression",
            span,
            None
        ),
        ExpectedCondExprForWhile(span) => (
            "Syntax error: expected an expression",
            span,
            None
        ),
        ExpectedWhileKwAfterDoBody(pos) => (
            "Syntax error: expected the `while` keyword",
            pos,
            None
        ),
        ExpectedSemiAfterReturnKw(pos, has_expr) => (
            if has_expr {
                "Syntax error: expected a semi-colon `;` after the return expression"
            } else {
                "Syntax error: expected a semi-colon `;` after `return`"
            },
            pos,
            None
        ),
        ExpectedSemiAfterBreakKw(pos) => (
            "Syntax error: expected a semi-colon `;` after `break`",
            pos,
            None
        ),
        ExpectedSemiAfterContinueKw(pos) => (
            "Syntax error: expected a semi-colon `;` after `continue`",
            pos,
            None
        ),
        ExpectedSemiAfterDiscardKw(pos) => (
            "Syntax error: expected a semi-colon `;` after `discard`",
            pos,
            None
        ),
        /* VAR DEF/DECL */
        ExpectedIdentsAfterVarType(pos) => (
            "Syntax error: expected variable identifier(s)",
            pos,
            None,
        ),
        ExpectedSemiOrEqAfterVarDef(pos) => (
            "Syntax error: expected either a semi-colon `;` or an equal sign `=`",
            pos,
            None
        ),
        ExpectedSemiAfterVarDeclExpr(pos) => (
            "Syntax error: expected a semi-colon `;`",
            pos,
            None
        ),
        ExpectedExprAfterVarDeclEq(pos) => (
            "Syntax error: expected an expression",
            pos,
            None
        ),
		/* FUNCTION DEF/DECL */
		ExpectedParenAtEndOfParamList(opening, expected) => (
			"Syntax error: expected a closing delimiter `)`",
			expected,
			Some(("opening delimiter here", opening)),
		),
		ExpectedCommaAfterParamInParamList(pos) => {
			("Syntax error: expected a comma `,`", pos, None)
		}
		MissingTypeInParamList(pos) => {
			("Syntax error: expected a type", pos, None)
		}
		ExpectedSemiOrScopeAfterParamList(pos) => (
            "Syntax error: expected either a semi-colon `;` or an opening delimiter `{`",
            pos,
            None
        ),
        /* STRUCT DEF/DECL */
        ExpectedIdentAfterStructKw(pos) => (
            "Syntax error: expected a struct identifier", pos, None
        ),
        ExpectedScopeAfterStructIdent(pos) => (
            "Syntax error: expected an opening delimiter `{`", pos, None
        ),
        StructDefIsIllegal(semi, def) => (
            "Syntax error: struct definitions are illegal", def, 
            Some(("illegal semi-colon here", semi))
        ),
        ExpectedVarDefInStructBody(stmt) => (
            "Syntax error: expected a variable definition", stmt, None
        ),
        ExpectedAtLeastOneMemberInStruct(decl) => (
            "Syntax error: expected at least one variable definition", decl, None
        ),
        ExpectedSemiAfterStructBody(pos) => (
            "Syntax error: expected a semi-colon `;`", pos, None
        ),
        _ => (
            "UNIMPLEMENTED SYNTAX ERROR",
            Span::empty(),
            None
        )
	};

	diags.push(Diagnostic {
		range: file.span_to_range(span),
		severity: Some(DiagnosticSeverity::ERROR),
		code: None,
		code_description: None,
		source: Some("glsl".into()),
		message: message.into(),
		// Link to the hint if there is one.
		related_information: if let Some(related) = related {
			Some(vec![DiagnosticRelatedInformation {
				location: Location {
					uri: file.uri.clone(),
					range: file.span_to_range(related.1),
				},
				message: related.0.into(),
			}])
		} else {
			None
		},
		tags: None,
		data: None,
	});

	// `related_information` on its own doesn't create underlines in the editor, so we need to push a hint as well.
	if let Some(related) = related {
		diags.push(Diagnostic {
			range: file.span_to_range(related.1),
			severity: Some(DiagnosticSeverity::HINT),
			code: None,
			code_description: None,
			source: Some("glsl".into()),
			message: related.0.into(),
			// Link to the original error.
			related_information: Some(vec![DiagnosticRelatedInformation {
				location: Location {
					uri: file.uri.clone(),
					range: file.span_to_range(span),
				},
				message: "original diagnostic here".into(),
			}]),
			tags: None,
			data: None,
		});
	}
}
