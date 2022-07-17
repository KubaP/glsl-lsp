use crate::File;
use glsl_parser::{error::SyntaxErr::{self, *}, span::Span};
use tower_lsp::lsp_types::{
	Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location,
};

/// Converts a [`SyntaxErr`] to an LSP `Diagnostic` type.
pub fn to_diagnostic(err: SyntaxErr, file: &File) -> Diagnostic {
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
            Some(vec![DiagnosticRelatedInformation{
                location: Location { uri: file.uri.clone(), range: file.span_to_range(opening) },
                message: "opening delimiter here".into()
            }])
        ),
		UnclosedIndexOperator(opening, expected) => (
            "Syntax error: expected a closing delimiter `]`",
            expected,
            Some(vec![DiagnosticRelatedInformation{
                location: Location { uri: file.uri.clone(), range: file.span_to_range(opening) },
                message: "opening delimiter here".into()
            }])
        ),
		UnclosedFunctionCall(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(vec![DiagnosticRelatedInformation{
                location: Location { uri: file.uri.clone(), range: file.span_to_range(opening) },
                message: "opening delimiter here".into()
            }])
        ),
		UnclosedInitializerList(opening, expected) => (
            "Syntax error: expected a closing delimiter `}`",
            expected,
            Some(vec![DiagnosticRelatedInformation{
                location: Location { uri: file.uri.clone(), range: file.span_to_range(opening) },
                message: "opening delimiter here".into()
            }])
        ),
		UnclosedArrayConstructor(opening, expected) => (
            "Syntax error: expected a closing delimiter `)`",
            expected,
            Some(vec![DiagnosticRelatedInformation{
                location: Location { uri: file.uri.clone(), range: file.span_to_range(opening) },
                message: "opening delimiter here".into()
            }])
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
            Some(vec![DiagnosticRelatedInformation{
                location: Location{
                    uri: file.uri.clone(),
                    range: file.span_to_range(opening)
                },
                message: "opening delimiter here".into(),
            }])
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
            token,None
        ),

		/* FUNCTION DEF/DECL */
		ExpectedParenAtEndOfParamList(opening, expected) => (
			"Syntax error: expected a closing delimiter `)`",
			expected,
			Some(vec![DiagnosticRelatedInformation {
				location: Location {
					uri: file.uri.clone(),
					range: file.span_to_range(opening),
				},
				message: "opening delimiter here".into(),
			}]),
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
        _ => (
            "UNIMPLEMENTED SYNTAX ERROR",
            Span::empty(),
            None
        )
	};

	Diagnostic {
		range: file.span_to_range(span),
		severity: Some(DiagnosticSeverity::ERROR),
		code: None,
		code_description: None,
		source: Some("glsl".into()),
		message: message.into(),
		related_information: related,
		tags: None,
		data: None,
	}
}
