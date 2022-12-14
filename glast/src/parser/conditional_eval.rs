//! Conditional directive expression evaluation.

use super::{
	ast::{
		conditional::{Expr, ExprTy},
		Ident,
	},
	Macro,
};
use crate::{
	parser::ast::conditional::{BinOpTy, PreOpTy},
	Either3, Span,
};
use std::collections::{HashMap, VecDeque};

/// Evaluates an `#ifdef`/`#ifndef` directive.
pub(super) fn evaluate_def(
	ident: Ident,
	macros: &HashMap<String, (Span, Macro)>,
) -> bool {
	for (macro_ident, _) in macros {
		if macro_ident == &ident.name {
			return true;
		}
	}

	false
}

/// Evaluates an `#if`/`#elif` directive.
pub(super) fn evaluate_expr(
	expr: Expr,
	macros: &HashMap<String, (Span, Macro)>,
) -> bool {
	// Generate a Polish-Notation stack of the expression.
	let mut pn_stack = VecDeque::new();
	let mut stack = VecDeque::new();
	stack.push_front(expr);
	loop {
		let node = stack.pop_front().unwrap();
		match node.ty {
			ExprTy::Num(num) => pn_stack.push_back(Either3::A(Val {
				ty: ValTy::Num(num as isize),
				span: node.span,
			})),
			ExprTy::Prefix { op, expr } => {
				pn_stack.push_back(Either3::B(op));
				if let Some(expr) = expr {
					stack.push_front(*expr);
				} else {
					return false;
				}
			}
			ExprTy::Binary { left, op, right } => {
				pn_stack.push_back(Either3::C(op));
				if let Some(right) = right {
					stack.push_front(*right);
				} else {
					return false;
				}
				stack.push_front(*left);
			}
			ExprTy::Parens { expr } => {
				if let Some(expr) = expr {
					stack.push_front(*expr);
				} else {
					return false;
				}
			}
			ExprTy::Defined { ident } => {
				let mut found = false;
				for (macro_ident, _) in macros {
					if macro_ident == &ident.name {
						found = true;
						break;
					}
				}
				pn_stack.push_back(Either3::A(Val {
					ty: ValTy::Bool(found),
					span: node.span,
				}));
			}
		}

		if stack.is_empty() {
			break;
		}
	}

	// A number of value `0` is treated as false, whilst any other numeric value is treated as true. Equally, a
	// boolean of value `false` is treated as 0, whilst of value `true` is treated as 1. The representations are
	// convereted on the fly when necessary to perform the relevant mathematical operations. At the end, the final
	// value is converted to a boolean.

	// Consume the Polish-Notation stack and evaluate it.
	let mut eval_stack = VecDeque::new();
	loop {
		let v = pn_stack.pop_back().unwrap();
		match v {
			Either3::A(val) => eval_stack.push_front(val),
			Either3::B(op) => match op.ty {
				PreOpTy::Neg => {
					let val = eval_stack.pop_front().unwrap();
					let v = match &val.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(-v),
						span: Span::new(op.span.start, val.span.end),
					});
				}
				PreOpTy::Flip => {
					let val = eval_stack.pop_front().unwrap();
					let v = match &val.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(!v),
						span: Span::new(op.span.start, val.span.end),
					});
				}
				PreOpTy::Not => {
					let val = eval_stack.pop_front().unwrap();
					let v = match &val.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(!v),
						span: Span::new(op.span.start, val.span.end),
					});
				}
			},
			Either3::C(op) => match op.ty {
				BinOpTy::Add => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l + r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Sub => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l - r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Mul => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l * r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Div => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l / r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Rem => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l % r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::And => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l & r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Or => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l | r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Xor => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l ^ r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::LShift => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l << r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::RShift => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Num(l >> r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::EqEq => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l == r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::NotEq => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l != r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::AndAnd => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l && r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::OrOr => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n != 0,
						ValTy::Bool(b) => *b,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l || r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Gt => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l > r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Lt => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l < r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Ge => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l >= r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::Le => {
					let left = eval_stack.pop_front().unwrap();
					let right = eval_stack.pop_front().unwrap();

					let l = match &left.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};
					let r = match &right.ty {
						ValTy::Num(n) => *n,
						ValTy::Bool(b) => *b as isize,
					};

					eval_stack.push_front(Val {
						ty: ValTy::Bool(l <= r),
						span: Span::new(left.span.start, right.span.end),
					});
				}
			},
		}

		if pn_stack.is_empty() {
			break;
		}
	}

	if eval_stack.len() != 1 {
		unreachable!("After processing the conditional evaluation stack, we are left with more than one value. This should not happen.")
	}

	match eval_stack.remove(0).unwrap().ty {
		ValTy::Num(n) => n != 0,
		ValTy::Bool(b) => b,
	}
}

/// An evaluated value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Val {
	ty: ValTy,
	span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValTy {
	Num(isize),
	Bool(bool),
}

#[cfg(test)]
mod tests {
	//! Behaviour tests for the conditional expression evaluator, and also of the conditional expression
	//! parser and lexer since those are prerequisites.

	use crate::{parser::Macro, span};
	use std::collections::HashMap;

	/// Asserts that the source string, once parsed and evaluated, matches the desired result. The source string
	/// must consist of an `#if` or `#elif` conditional directive only.
	macro_rules! assert_eval {
		($macros:expr, $src:expr, $result:expr) => {
			let mut tokens = crate::lexer::parse_from_str_with_version(
				$src,
				crate::GlslVersion::_450,
			)
			.0;
			match tokens.remove(0) {
				(crate::lexer::Token::Directive(d), _) => match d {
					crate::lexer::preprocessor::TokenStream::If {
						tokens,
						..
					}
					| crate::lexer::preprocessor::TokenStream::ElseIf {
						tokens,
						..
					} => {
						let (expr, _, _) =
							crate::parser::conditional_expression::cond_parser(
								tokens, &$macros,
							);
						assert_eq!(
							super::evaluate_expr(expr.unwrap(), &$macros),
							$result
						);
					}
					_ => panic!(),
				},
				_ => panic!(),
			}
		};
	}

	#[test]
	fn single_value() {
		let macros = HashMap::new();
		assert_eval!(macros, "#if 0", false);
		assert_eval!(macros, "#if 1", true);
		assert_eval!(macros, "#if 50", true);
		assert_eval!(macros, "#if -100", true);
		assert_eval!(macros, "#if undefined", false);
	}

	#[test]
	fn pre() {
		let macros = HashMap::new();
		assert_eval!(macros, "#if -5", true);
		assert_eval!(macros, "#if ~1", true);
		assert_eval!(macros, "#if !0", true);
		assert_eval!(macros, "#if !1", false);
	}

	#[test]
	fn defined() {
		let mut macros = HashMap::new();
		macros.insert("FOO".into(), (span(0, 0), Macro::Object(vec![])));
		assert_eval!(macros, "#if defined BAR", false);
		assert_eval!(macros, "#if defined FOO", true);
		assert_eval!(macros, "#if defined ( FOO )", true);
	}

	#[test]
	fn binary() {
		let macros = HashMap::new();
		assert_eval!(macros, "#if 5 + 6", true);
		assert_eval!(macros, "#if 5 - 5", false);
		assert_eval!(macros, "#if 5 * 5 - 25", false);
		assert_eval!(macros, "#if 16 / 16 - 1", false);
		assert_eval!(macros, "#if 0 - !1", false);
	}
}
