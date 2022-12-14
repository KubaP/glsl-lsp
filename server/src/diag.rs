use glast::{diag::*, Span};
use tower_lsp::lsp_types::{
	Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity,
	DiagnosticTag, Location, NumberOrString,
};

/// Converts [`Syntax`] and [`Semantic`] diagnostics to LSP diagnostics.
pub fn convert(
	syntax_diags: Vec<Syntax>,
	semantic_diags: Vec<Semantic>,
	diags: &mut Vec<Diagnostic>,
	file: &crate::File,
	supports_related_info: bool,
) {
	for diag in syntax_diags {
		let (message, span, related) = convert_syntax(diag);
		diags.push(Diagnostic {
			range: file.span_to_lsp(span),
			severity: Some(DiagnosticSeverity::ERROR),
			code: None,
			code_description: None,
			source: Some("glsl".to_owned()),
			message,
			// Link to a hint, if there is one.
			related_information: if supports_related_info {
				if let Some(ref related) = related {
					Some(vec![DiagnosticRelatedInformation {
						location: Location {
							uri: file.uri.clone(),
							range: file.span_to_lsp(related.1),
						},
						message: related.0.clone(),
					}])
				} else {
					None
				}
			} else {
				None
			},
			tags: None,
			data: None,
		});

		if supports_related_info {
			// `related_information` on its own doesn't create underlines in the editor, so we need to push a
			// separate hint diagnostic as well.
			if let Some(related) = related {
				diags.push(Diagnostic {
					range: file.span_to_lsp(related.1),
					severity: Some(DiagnosticSeverity::HINT),
					code: None,
					code_description: None,
					source: Some("glsl".into()),
					message: related.0.into(),
					// Link to the original error.
					related_information: Some(vec![
						DiagnosticRelatedInformation {
							location: Location {
								uri: file.uri.clone(),
								range: file.span_to_lsp(span),
							},
							message: "original diagnostic here".into(),
						},
					]),
					tags: None,
					data: None,
				});
			}
		}
	}

	for diag in semantic_diags {
		let (message, span, severity, error_code, related) =
			convert_semantic(diag);
		diags.push(Diagnostic {
			range: file.span_to_lsp(span),
			severity: Some(match severity {
				Severity::Error => DiagnosticSeverity::ERROR,
				Severity::Warning => DiagnosticSeverity::WARNING,
			}),
			code: error_code.map(|e| NumberOrString::String(e.to_owned())),
			code_description: None,
			source: Some("glsl".to_owned()),
			message,
			// Link to a hint, if there is one.
			related_information: if supports_related_info {
				if let Some(ref related) = related {
					Some(vec![DiagnosticRelatedInformation {
						location: Location {
							uri: file.uri.clone(),
							range: file.span_to_lsp(related.1),
						},
						message: related.0.clone(),
					}])
				} else {
					None
				}
			} else {
				None
			},
			tags: None,
			data: None,
		});

		if supports_related_info {
			// `related_information` on its own doesn't create underlines in the editor, so we need to push a
			// separate hint diagnostic as well.
			if let Some(related) = related {
				diags.push(Diagnostic {
					range: file.span_to_lsp(related.1),
					severity: Some(DiagnosticSeverity::HINT),
					code: None,
					code_description: None,
					source: Some("glsl".into()),
					message: related.0.into(),
					// Link to the original error.
					related_information: Some(vec![
						DiagnosticRelatedInformation {
							location: Location {
								uri: file.uri.clone(),
								range: file.span_to_lsp(span),
							},
							message: "original diagnostic here".into(),
						},
					]),
					tags: None,
					data: None,
				});
			}
		}
	}
}

/// Disables a block of code. This is used to grey-out code that is disabled because of conditional compilation.
pub fn disable_code(
	span: Span,
	reason: DisabledReason,
	diags: &mut Vec<Diagnostic>,
	file: &crate::File,
) {
	diags.push(Diagnostic {
		range: file.span_to_lsp(span),
		severity: Some(DiagnosticSeverity::HINT),
		code: None,
		code_description: None,
		source: Some("glsl".into()),
		message: match reason {
			DisabledReason::ConditionalCompilationDisabled => "Code inactive due to conditional directive: conditional compilation is disabled for this file",
    		DisabledReason::ConditionalCompilationDisabledGlobally => "Code inactive due to conditional directive: conditional compilation is disabled globally",
		}.into(),
		related_information: None,
		tags: Some(vec![DiagnosticTag::UNNECESSARY]),
		data: None,
	});
}

/// The reason for the disabling of a block of code.
#[allow(unused)]
pub enum DisabledReason {
	/// Conditional compilation is disable for this file.
	ConditionalCompilationDisabled,
	/// Conditional compilation is disabled across all files.
	ConditionalCompilationDisabledGlobally,
}

/* MUST FORMAT THE FOLLOWING FUNCTIONS MANUALLY, Something about them makes rustfmt give up */

#[rustfmt::skip]
fn convert_semantic(
	diag: Semantic,
) -> (
	String,
	Span,
	Severity,
	Option<&'static str>,
	Option<(String, Span)>,
) {
	let (message, span, related) = match diag {
		Semantic::EmptyDirective(span) => (
			format!("Unnecessary preprocessor directive"),
			span,
			None
		),
		/* MACROS */
		Semantic::EmptyMacroCallSite(span) => (
			format!("Unnecessary macro call; expands to nothing"),
			span,
			None
		),
		Semantic::FunctionMacroMismatchedArgCount(span, definition) => (
			format!("Number of arguments doesn't match the number of parameters"),
			span,
			Some((format!("Macro defined here"), definition))
		),
		Semantic::TokenConcatUnnecessary(span) => (
			format!("Unnecessary token concatenation operator `##`"),
			span,
			None
		),
		Semantic::UndefMacroNameUnresolved(span) => (
			format!("Unnecessary `#undef` directive; macro name could not be resolved"),
			span,
			None
		),
		_ => unreachable!(),
	};
	(
		message,
		span,
		diag.get_severity(),
		diag.get_error_code(),
		related,
	)
}

type DiagReturn = (String, Span, Option<(String, Span)>);

#[rustfmt::skip]
fn convert_syntax(diag: Syntax) -> DiagReturn {
	match diag {
		Syntax::Expr(d) => convert_syntax_expr(d),
		Syntax::Stmt(d) => convert_syntax_stmt(d),
		Syntax::FoundIllegalChar(span, char) => (
			format!("Syntax error: found an illegal character `{char}` that is not part of the GLSL character set"),
			span,
			None
		),
		Syntax::FoundReservedKw(span, kw) => (
			format!("Syntax error: found a reserved keyword `{kw}`"),
			span,
			None
		),
		Syntax::FoundUnmatchedRBrace(span) => (
			format!("Syntax error: found a trailing closing brace `}}` that doesn't match-up with an opening brace"),
			span,
			None
		),
		Syntax::FoundLonelyElseKw(span) => (
			format!("Syntax error: found an `else` keyword outside of an if-statement"),
			span,
			None
		),
		Syntax::FoundLonelyCaseKw(span) => (
			format!("Syntax error: found a `case` keyword outside of a switch-statement"),
			span,
			None
		),
		Syntax::FoundLonelyDefaultKw(span) => (
			format!("Syntax error: found a `default` keyword outside of a switch-statement"),
			span,
			None
		),
		Syntax::BlockCommentMissingEnd(pos) => (
			format!("Syntax error: expected a closing tag `*/` for the block comment"),
			pos,
			None
		),
		Syntax::PreprocVersion(d) => convert_syntax_version(d),
		Syntax::PreprocExt(d) => convert_syntax_ext(d),
		Syntax::PreprocLine(d) => convert_syntax_line(d),
		Syntax::PreprocDefine(d) => convert_syntax_define(d),
		Syntax::PreprocConditional(d) => convert_syntax_condition(d),
		Syntax::PreprocTrailingTokens(span) => (
			format!("Syntax error: found trailing tokens after the directive"),
			span,
			None
		),
		Syntax::FoundIllegalPreproc(span, kw) => (
			if let Some(kw) = kw {
				format!("Syntax error: found an illegal directive `{}`", kw.0)
			} else {
				format!("Syntax error: found an illegal directive")
			},
			span,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_expr(diag: ExprDiag) -> DiagReturn {
	match diag {
		/* LITERALS */
		ExprDiag::InvalidNumber(span) => (
			format!("Syntax error: found a number with an invalid suffix"),
			span,
			None
		),
		ExprDiag::EmptyNumber(span) => (
			format!("Syntax error: found a number that has no digits"),
			span,
			None
		),
		ExprDiag::UnparsableNumber(span) => (
			format!("Syntax error: found an un-representable number"),
			span,
			None
		),
		/* COMPOUND EXPRESSIONS */
		ExprDiag::FoundOperandAfterOperand(prev, current) => (
			format!(
				"Syntax error: expected an operator between the two operands"
			),
			Span::new_between(prev, current),
			None
		),
		ExprDiag::InvalidPrefixOperator(span) => (
			format!("Syntax error: found an invalid prefix operator"),
			span,
			None
		),
		ExprDiag::InvalidBinOrPostOperator(span) => (
			format!("Syntax error: found an invalid binary/postfix operator"),
			span,
			None
		),
		ExprDiag::FoundDotInsteadOfOperand(prev, dot) => {
			if let Some(prev) = prev {
				(
					format!("Syntax error: expected an operand between the operator and dot `.`"),
					Span::new_between(prev, dot),
					None
				)
			} else {
				(
					format!("Syntax error: expected an operand before the dot `.`"),
					dot.previous_single_width(),
					None
				)
			}
		},
		ExprDiag::FoundCommaInsteadOfOperand(prev, comma) => (
			format!("Syntax error: expected an operand between the operator and comma `,`"),
			Span::new_between(prev, comma),
			None
		),
		ExprDiag::FoundQuestionInsteadOfOperand(prev, question) => {
			if let Some(prev) = prev {
				(
					format!("Syntax error: expected an operand between the operator and question-mark `?`"),
					Span::new_between(prev, question),
					None
				)
			} else {
				(
					format!("Syntax error: expected an operand before the question-mark `?`"),
					question.previous_single_width(),
					None
				)
			}
		},
		ExprDiag::FoundColonInsteadOfOperand(prev, colon) => {
			if let Some(prev) = prev {
				(
					format!("Syntax error: expected an operand between the operator and colon `:`"),
					Span::new_between(prev, colon),
					None
				)
			} else {
				(
					format!("Syntax error: expected an operand before the colon `:`"),
					colon.previous_single_width(),
					None
				)
			}
		},
		ExprDiag::FoundInvalidToken(span) => (
			format!("Syntax error: found an invalid expression token"),
			span,
			None
		),
		/* GROUPS */
		ExprDiag::FoundEmptyParens(span) => (
			format!("Syntax error: found an empty set of parenthesis"),
			span,
			None
		),
		ExprDiag::FoundLBracketInsteadOfOperand(prev, bracket) => {
			if let Some(prev) = prev {
				(
					format!("Syntax error: expected an operand between the operator and opening bracket `[`"),
					Span::new_between(prev, bracket),
					None
				)
			} else {
				(
					format!("Syntax error: expected an operand before the opening bracket `[`"),
					bracket.previous_single_width(),
					None
				)
			}
		},
		ExprDiag::FoundRParenInsteadOfOperand(prev, closing) => (
			format!("Syntax error: expected an operand between the operator and closing parenthesis `)`"),
			Span::new_between(prev, closing),
			None
		),
		ExprDiag::FoundRBracketInsteadOfOperand(prev, closing) => (
			format!("Syntax error: expected an operand between the operator and closing bracket `]`"),
			Span::new_between(prev, closing),
			None
		),
		ExprDiag::FoundRBraceInsteadOfOperand(prev, closing) => (
			format!("Syntax error: expected an operand between the operator and closing brace `}}`"),
			Span::new_between(prev, closing),
			None
		),
		/* ARITY */
		ExprDiag::ExpectedCommaAfterArg(pos) => (
			format!("Syntax error: expected a comma after the argument"),
			pos,
			None
		),
		ExprDiag::ExpectedArgAfterComma(pos) => (
			format!("Syntax error: expected an argument after the comma `,`"),
			pos,
			None
		),
		ExprDiag::ExpectedArgBetweenParenComma(span) => (
			format!("Syntax error: expected an argument between the opening parenthesis `(` and comma `,`"),
			span,
			None
		),
		ExprDiag::ExpectedArgBetweenBraceComma(span) => (
			format!("Syntax error: expected an argument between the opening brace `{{` and comma `,`"),
			span,
			None
		),
		ExprDiag::ExpectedCommaAfterExpr(pos) => (
			format!("Syntax error: expected a comma `,` after the expression"),
			pos,
			None
		),
		ExprDiag::ExpectedExprAfterComma(pos) => (
			format!("Syntax error: expected an expression after the comma `,`"),
			pos,
			None
		),
		ExprDiag::ExpectedExprBeforeComma(pos) => (
			format!("Syntax error: expected an expression before the comma `,`"),
			pos,
			None
		),
		/* UNCLOSED GROUPS */
		ExprDiag::UnclosedParens(opening, end) => (
			format!("Syntax error: expected a closing parenthesis `)`"),
			end,
			Some((format!("Opening parenthesis here"), opening))
		),
		ExprDiag::UnclosedIndexOperator(opening, end) => (
			format!("Syntax error: expected a closing bracket `]`"),
			end,
			Some((format!("Opening bracket here"), opening))
		),
		ExprDiag::UnclosedFunctionCall(opening, end) => (
			format!("Syntax error: expected a closing parenthesis `)`"),
			end,
			Some((format!("Opening parenthesis here"), opening))
		),
		ExprDiag::UnclosedInitializerList(opening, end) => (
			format!("Syntax error: expected a closing brace `}}`"),
			end,
			Some((format!("Opening brace here"), opening))
		),
		ExprDiag::UnclosedArrayConstructor(opening, end) => (
			format!("Syntax error: expected a closing parenthesis `)`"),
			end,
			Some((format!("Opening parenthesis here"), opening))
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_stmt(diag: StmtDiag) -> DiagReturn {
	match diag {
		StmtDiag::ExprStmtExpectedSemiAfterExpr(pos) => (
			format!("Syntax error: expected a semi-colon `;` after the expression"),
			pos,
			None
		),
		StmtDiag::ScopeMissingRBrace(opening, pos) => (
			format!("Syntax error: expected a closing brace `}}`"),
			pos,
			Some((format!("Opening brace here"), opening))
		),
		StmtDiag::FoundQualifiersBeforeStmt(span) => (
			format!("Syntax error: found qualifiers before a statement that doesn't support qualifiers"),
			span,
			None
		),
		/* QUALIFIERS */
		StmtDiag::LayoutExpectedLParenAfterKw(pos) => (
			format!("Syntax error: expected an opening parenthesis `(` after `layout`"),
			pos,
			None
		),
		StmtDiag::LayoutInvalidIdent(span) => (
			format!("Syntax error: found an invalid layout identifier"),
			span,
			None
		),
		StmtDiag::LayoutExpectedEqAfterIdent(pos) => (
			format!("Syntax error: expected an equal-sign `=` after the identifier"),
			pos,
			None
		),
		StmtDiag::LayoutExpectedExprAfterEq(pos) => (
			format!("Syntax error: expected a value expression after the equals-sign `=`"),
			pos,
			None
		),
		StmtDiag::LayoutMissingRParen(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` to end the layout qualifier"),
			pos,
			None
		),
		StmtDiag::LayoutExpectedCommaAfterLayout(pos) => (
			format!("Syntax error: expected a comma `,` after a layout identifier"),
			pos,
			None
		),
		StmtDiag::LayoutExpectedLayoutAfterComma(span) => (
			format!("Syntax error: expected a layout identifier after the comma `,`"),
			span,
			None
		),
		StmtDiag::LayoutExpectedLayoutBetweenParenComma(span) => (
			format!("Syntax error: expected a layout identifier between the opening parenthesis `(` and the comma `,`"),
			span,
			None
		),
		/* VARIABLES */
		StmtDiag::VarDefExpectedSemiOrEqAfterIdents(pos) => (
			format!("Syntax error: expected a semi-colon `;` or equal-sign `=` after the variable identifier(s)"),
			pos,
			None
		),
		StmtDiag::VarDefInitExpectedValueAfterEq(pos) => (
			format!("Syntax error: expected a value expression after the equal-sign `=`"),
			pos,
			None
		),
		StmtDiag::VarDefInitExpectedSemiAfterValue(pos) => (
			format!("Syntax error: expected a semi-colon `;` after the value expression"),
			pos,
			None
		),
		/* FUNCTIONS */
		StmtDiag::ParamsExpectedCommaAfterParam(pos) => (
			format!("Syntax error: expected a comma `,` after the parameter"),
			pos,
			None
		),
		StmtDiag::ParamsExpectedParamAfterComma(span) => (
			format!("Syntax error: expected a parameter after the comma `,`"),
			span,
			None
		),
		StmtDiag::ParamsExpectedParamBetweenParenComma(span) => (
			format!("Syntax error: expected a parameter between the opening parenthesis `(` and the comma `,`"),
			span,
			None
		),
		StmtDiag::ParamsInvalidTypeExpr(span) => (
			format!("Syntax error: expected a type"),
			span,
			None
		),
		StmtDiag::ParamsInvalidIdentExpr(span) => (
			format!("Syntax error: expected type identifier(s)"),
			span,
			None
		),
		StmtDiag::ParamsExpectedRParen(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` to end the parameter list"),
			pos,
			None
		),
		StmtDiag::FnExpectedSemiOrLBraceAfterParams(pos) => (
			format!("Syntax error: expected a semi-colon `;` or an opening brace `{{` after the parameter list"),
			pos,
			None
		),
		/* SUBROUTINES */
		StmtDiag::SubroutineExpectedVarDefAfterUniformKw(pos) => (
			format!("Syntax error: expected a variable definition after the `uniform` keyword"),
			pos,
			None
		),
		StmtDiag::SubroutineExpectedTypeFuncUniformAfterKw(pos) => (
			format!("Syntax error: expected a subroutine type declaration, a subroutine associated function definition, or a subroutine uniform definition after the `subroutine` keyword"),
			pos,
			None
		),
		StmtDiag::SubroutineAssociatedListExpectedCommaAfterIdent(pos) => (
			format!("Syntax error: expected a comma `,` after the subroutine name"),
			pos,
			None
		),
		StmtDiag::SubroutineAssociatedListExpectedIdentAfterComma(span) => (
			format!("Syntax error: expected a subroutine name after the comma `,`"),
			span,
			None
		),
		StmtDiag::SubroutineAssociatedListExpectedIdentBetweenParenComma(span) => (
			format!("Syntax error: expected a subroutine name between the opening parenthesis `(` and the comma `,`"),
			span,
			None
		),
		StmtDiag::SubroutineAssociatedListExpectedRParen(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` to end the associated-subroutines list"),
			pos,
			None
		),
		StmtDiag::SubroutineExpectedFnDefAfterAssociatedList(pos) => (
			format!("Syntax error: expected a function definition after the associated-subroutines list"),
			pos,
			None
		),
		StmtDiag::SubroutineExpectedFnDefAfterAssociatedListFoundDecl(span) => (
			format!("Syntax error: expected a function definition; found a function declaration instead"),
			span,
			None
		),
		StmtDiag::SubroutineMissingAssociationsForFnDef(span) => (
			format!("Syntax error: expected an associated-subroutines list after the `subroutine` keyword"),
			span,
			None
		),
		StmtDiag::SubroutineMissingUniformKwForUniformDef(span) => (
			format!("Syntax error: expected the `uniform` keyword after the `subroutine` keyword"),
			span,
			None
		),
		/* STRUCTS */
		StmtDiag::StructExpectedIdentAfterKw(pos) => (
			format!("Syntax error: expected an name after the `struct` keyword"),
			pos,
			None
		),
		StmtDiag::StructExpectedLBraceAfterIdent(pos) => (
			format!("Syntax error: expected an opening brace `{{` after the struct name"),
			pos,
			None
		),
		StmtDiag::StructInvalidStmtInBody(span) => (
			format!("Syntax error: found an invalid statement within the struct body; only variable definitions are allowed"),
			span,
			None
		),
		StmtDiag::StructExpectedAtLeastOneStmtInBody(span) => (
			format!("Syntax error: found a struct body that is empty"),
			span,
			None
		),
		StmtDiag::StructExpectedInstanceOrSemiAfterBody(pos) => (
			format!("Syntax error: expected a semi-colon `;` or an instance name after the struct body"),
			pos,
			None
		),
		StmtDiag::StructExpectedSemiAfterBodyOrInstance(pos) => (
			format!("Syntax error: expected a semi-colon `;` after the struct's instance name"),
			pos,
			None
		),
		StmtDiag::StructDeclIsIllegal(span) => (
			format!("Syntax error: found a struct declaration; this is an illegal GLSL statement"),
			span,
			None
		),
		/* IF STATEMENTS */
		StmtDiag::IfExpectedLParenAfterKw(pos) => (
			format!("Syntax error: expected an opening parenthesis `(` after the `if` keyword"),
			pos,
			None
		),
		StmtDiag::IfExpectedExprAfterLParen(pos) => (
			format!("Syntax error: expected a value expression after the opening parenthesis `(`"),
			pos,
			None
		),
		StmtDiag::IfExpectedRParenAfterExpr(pos) => (
			format!("Syntax error: expected a closing parenthesis after the value expression"),
			pos,
			None
		),
		StmtDiag::IfExpectedLBraceOrStmtAfterRParen(pos) => (
			format!("Syntax error: expected an opening brace `{{` or a statement after the closing parenthesis `)`"),
			pos,
			None
		),
		StmtDiag::IfExpectedIfOrLBraceOrStmtAfterElseKw(pos) => (
			format!("Syntax error: expected the `if` keyword or an opening brace `{{` or a statement after the `else` keyword"),
			pos,
			None
		),
		/* SWITCH STATEMENTS */
		StmtDiag::SwitchExpectedLParenAfterKw(pos) => (
			format!("Syntax error: expected an opening parenthesis `(` after the `switch` keyword"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedExprAfterLParen(pos) => (
			format!("Syntax error: expected a value expression after the opening parenthesis `(`"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedRParenAfterExpr(pos) => (
			format!("Syntax error: expected a closing parenthesis after the value expression"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedLBraceAfterCond(pos) => (
			format!("Syntax error: expected an opening brace `{{` after the closing parenthesis `)`"),
			pos,
			None
		),
		StmtDiag::SwitchFoundEmptyBody(span) => (
			format!("Syntax error: expected at least one branch within a switch-statement's body"),
			span,
			None
		),
		StmtDiag::SwitchExpectedCaseOrDefaultKwOrEnd(span) => (
			format!("Syntax error: expected the `case` or `default` keyword to begin a new branch"),
			span,
			None
		),
		StmtDiag::SwitchExpectedExprAfterCaseKw(pos) => (
			format!("Syntax error: expected a value expression after the `case` keyword"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedColonAfterCaseExpr(pos) => (
			format!("Syntax error: expected a colon `:` after the value expression"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedColonAfterDefaultKw(pos) => (
			format!("Syntax error: expected a colon `:` after the `default` keyword"),
			pos,
			None
		),
		StmtDiag::SwitchExpectedRBrace(pos) => (
			format!("Syntax error: expected a closing brace `}}`"),
			pos,
			None
		),
		/* FOR LOOPS */
		StmtDiag::ForExpectedLParenAfterKw(pos) => (
			format!("Syntax error: expected an opening parenthesis `(` after the `for` keyword"),
			pos,
			None
		),
		StmtDiag::ForExpectedInitStmt(pos) => (
			format!("Syntax error: expected an initialization statement after the opening parenthesis `(`"),
			pos,
			None
		),
		StmtDiag::ForExpectedCondStmt(pos) => (
			format!("Syntax error: expected a condition statement after the initialization statement"),
			pos,
			None
		),
		StmtDiag::ForExpectedIncStmt(pos) => (
			format!("Syntax error: expected an increment statement after the condition statement"),
			pos,
			None
		),
		StmtDiag::ForExpected3Stmts(pos) => (
			format!("Syntax error: expected an initialization, a condition, and an increment statement"),
			pos,
			None
		),
		StmtDiag::ForExpectedRParenAfterStmts(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` after the increment statement"),
			pos,
			None
		),
		StmtDiag::ForExpectedLBraceAfterHeader(pos) => (
			format!("Syntax error: expected an opening brace `{{` after the closing parenthesis `)`"),
			pos,
			None
		),
		/* WHILE/DO-WHILE LOOPS */
		StmtDiag::WhileExpectedLParenAfterKw(pos) => (
			format!("Syntax error: expected an opening parenthesis `(` after `while`"),
			pos,
			None
		),
		StmtDiag::WhileExpectedExprAfterLParen(pos) => (
			format!("Syntax error: expected a conditional expression after the opening parenthesis `(`"),
			pos,
			None
		),
		StmtDiag::WhileExpectedRParenAfterExpr(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` after the conditional expression"),
			pos,
			None
		),
		StmtDiag::WhileExpectedLBraceAfterCond(pos) => (
			format!("Syntax error: expected an opening brace `{{` after the closing parenthesis `)`"),
			pos,
			None
		),
		StmtDiag::DoWhileExpectedLBraceAfterKw(pos) => (
			format!("Syntax error: expected an opening brace `{{` after `do`"),
			pos,
			None
		),
		StmtDiag::DoWhileExpectedWhileAfterBody(pos) => (
			format!("Syntax error: expected the `while` keyword after the body of a do-while-loop"),
			pos,
			None
		),
		StmtDiag::DoWhileExpectedSemiAfterRParen(pos) => (
			format!("Syntax error: expected a semi-colon `;` after the closing parenthesis `)`"),
			pos,
			None
		),
		/* SINGLE-KEYWORD CONTROL FLOW */
		StmtDiag::BreakExpectedSemiAfterKw(pos) => (
			format!("Syntax error: expected a semi-colon `;` after `break`"),
			pos,
			None
		),
		StmtDiag::ContinueExpectedSemiAfterKw(pos) => (
			format!("Syntax error: expected a semi-colon `;` after `continue`"),
			pos,
			None
		),
		StmtDiag::DiscardExpectedSemiAfterKw(pos) => (
			format!("Syntax error: expected a semi-colon `;` after `discard`"),
			pos,
			None
		),
		StmtDiag::ReturnExpectedSemiOrExprAfterKw(pos) => (
			format!("Syntax error: expected a semi-colon `;` or a value expression after `return`"),
			pos,
			None
		),
		StmtDiag::ReturnExpectedSemiAfterExpr(pos) => (
			format!("Syntax error: expected a semi-colon `;` after the return value expression"),
			pos,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_version(diag: PreprocVersionDiag) -> DiagReturn {
	match diag {
		PreprocVersionDiag::ExpectedNumber(span) => (
			format!("Syntax error: expected a GLSL version number"),
			span,
			None
		),
		PreprocVersionDiag::MissingNumberBetweenKwAndProfile(span) => (
			format!("Syntax error: expected a GLSL version number between `version` and `{{profile}}`"),
			span,
			None
		),
		PreprocVersionDiag::InvalidNumber(span) => (
			format!("Syntax error: found an un-representable number"),
			span,
			None
		),
		PreprocVersionDiag::InvalidVersion(span, num) => (
			format!("Syntax error: `{num}` is not a valid GLSL version number"),
			span,
			None
		),
		PreprocVersionDiag::UnsupportedVersion(span, version) => (
			format!("Error: this extension currently doesn't support GLSL {version}"),
			span,
			None
		),
		PreprocVersionDiag::ExpectedProfile(span) => (
			format!("Syntax error: expected a GLSL profile"),
			span,
			None
		),
		PreprocVersionDiag::InvalidProfile(span) => (
			format!("Syntax error: found an invalid GLSL profile"),
			span,
			None
		),
		PreprocVersionDiag::InvalidProfileCasing(span, correction) => (
			format!("Syntax error: found an invalid GLSL profile; did you mean `{correction}`?"),
			span,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_ext(diag: PreprocExtDiag) -> DiagReturn {
	match diag {
		PreprocExtDiag::ExpectedName(span) => (
			format!("Syntax error: expected a GLSL extension name"),
			span,
			None
		),
		PreprocExtDiag::MissingNameBetweenKwAndColon(span) => (
			format!("Syntax error: expected a GLSL extension name between `extension` and `:`"),
			span,
			None
		),
		PreprocExtDiag::MissingNameBetweenKwAndBehaviour(span) => (
			format!("Syntax error: expected a GLSL extension name between `extension` and `{{behaviour}}`"),
			span,
			None
		),
		PreprocExtDiag::MissingColonBetweenNameAndBehaviour(span) => (
			format!("Syntax error: expected a colon between `{{extension_name}}` and `{{behaviour}}`"),
			span,
			None
		),
		PreprocExtDiag::ExpectedColon(span) => (
			format!("Syntax error: expected a colon `:`"),
			span,
			None
		),
		PreprocExtDiag::ExpectedBehaviour(span) => (
			format!("Syntax error: expected a GLSL extension behaviour"),
			span,
			None
		),
		PreprocExtDiag::InvalidBehaviour(span) => (
			format!("Syntax error: found an invalid GLSL extension behaviour"),
			span,
			None
		),
		PreprocExtDiag::InvalidBehaviourCasing(span, correction) => (
			format!("Syntax error: found an invalid GLSL extension behaviour; did you mean `{correction}`?"),
			span,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_line(diag: PreprocLineDiag) -> DiagReturn {
	match diag {
		PreprocLineDiag::ExpectedNumber(span) => (
			format!("Syntax error: expected a line number"),
			span,
			None
		),
		PreprocLineDiag::InvalidNumber(span) => (
			format!("Syntax error: found an un-representable number"),
			span,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_define(diag: PreprocDefineDiag) -> DiagReturn {
	match diag {
		/* DEFINE */
		PreprocDefineDiag::DefineExpectedMacroName(pos) => (
			format!("Syntax error: expected a macro name"),
			pos,
			None
		),
		PreprocDefineDiag::ParamsExpectedParam(span) => (
			format!("Syntax error: expected a parameter"),
			span,
			None
		),
		PreprocDefineDiag::ParamsExpectedCommaAfterParam(pos) => (
			format!("Syntax error: expected a comma `,` after a parameter"),
			pos,
			None
		),
		PreprocDefineDiag::ParamsExpectedParamAfterComma(span) => (
			format!("Syntax error: expected a parameter after the comma `,`"),
			span,
			None
		),
		PreprocDefineDiag::ParamsExpectedParamBetweenParenComma(span) => (
			format!("Syntax error: expected a parameter between the opening parenthesis `(` and comma `,`"),
			span,
			None
		),
		PreprocDefineDiag::ParamsExpectedRParen(pos) => (
			format!("Syntax error: expected a closing parenthesis `)` to end the parameter list"),
			pos,
			None
		),
		/* TOKEN CONCAT */
		PreprocDefineDiag::TokenConcatMissingLHS(span) => (
			format!("Syntax error: token concatenation operator is missing a left-hand side"),
			span,
			None
		),
		PreprocDefineDiag::TokenConcatMissingRHS(span) => (
			format!("Syntax error: token concatenation operator is missing a right-hand side"),
			span,
			None
		),
		/* UNDEF */
		PreprocDefineDiag::UndefExpectedMacroName(span) => (
			format!("Syntax error: expected a macro name"),
			span,
			None
		),
		_ => unreachable!(),
	}
}

#[rustfmt::skip]
fn convert_syntax_condition(diag: PreprocConditionalDiag) -> DiagReturn {
	match diag {
		PreprocConditionalDiag::UnmatchedElseIf(span) => (
			format!("Syntax error: found a trailing `#elif` directive"),
			span,
			None
		),
		PreprocConditionalDiag::UnmatchedElse(span) => (
			format!("Syntax error: found a trailing `#else` directive"),
			span,
			None
		),
		PreprocConditionalDiag::UnmatchedEndIf(span) => (
			format!("Syntax error: found a trailing `#endif` directive"),
			span,
			None
		),
		_ => unreachable!(),
	}
}
