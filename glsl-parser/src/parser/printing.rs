use crate::{
	cst::{Expr, Ident, List, Node, NodeTy, Nodes, Param, Qualifier, Scope},
	span::Span,
	Either,
};
use std::fmt::Write;

#[allow(unused_must_use)]
pub(super) fn print_tree_node(
	node: &Node,
	indent: usize,
	f: &mut String,
) -> Result<(), std::fmt::Error> {
	write!(f, "\r\n{:indent$}", "", indent = indent * 2);

	match &node.ty {
		NodeTy::Keyword => write!(f, "KEYWORD@{}", node.span),
		NodeTy::Punctuation => write!(f, "PUNCTUATION@{}", node.span),
		NodeTy::Ident => write!(f, "IDENT@{}", node.span),
		NodeTy::Directive => write!(f, "DIRECTIVE@{}", node.span),
		NodeTy::Invalid => write!(f, "INVALID@{}", node.span),
		NodeTy::ZeroWidth => panic!(),
		NodeTy::Expression(_e) => write!(f, "EXPR@{}", node.span),
		NodeTy::DelimitedScope(scope) => {
			write!(f, "SCOPE@{}", node.span);
			let indent = indent + 1;
			if let Some(opening) = scope.opening {
				write!(
					f,
					"\r\n{:indent$}OPENING@{}",
					"",
					opening,
					indent = indent * 2
				);
			}
			for node in &scope.inner {
				print_tree_node(node, indent, f);
			}
			if let Some(closing) = scope.closing {
				write!(
					f,
					"\r\n{:indent$}CLOSING@{}",
					"",
					closing,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::EmptyStmt => {
			write!(f, "EMPTY_STMT@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}SEMI@{}",
				"",
				node.span,
				indent = indent * 2
			)
		}
		NodeTy::VarDef {
			qualifiers,
			type_,
			ident,
			semi,
		} => {
			write!(f, "VAR_DEF@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("TYPE", type_, indent, f);
			print_tree_expr("IDENT", ident, indent, f);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::VarDefs {
			qualifiers,
			type_,
			idents,
			semi,
		} => {
			write!(f, "VAR_DEFS@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("TYPE", type_, indent, f);
			print_tree_expr("IDENTS", idents, indent, f);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::VarDecl {
			qualifiers,
			type_,
			ident,
			eq,
			value,
			semi,
		} => {
			write!(f, "VAR_DECL@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("TYPE", type_, indent, f);
			print_tree_expr("IDENT", ident, indent, f);
			if let Some(eq) = eq {
				write!(f, "\r\n{:indent$}EQ@{}", "", eq, indent = indent * 2);
			}
			if let Some(value) = value {
				print_tree_expr("VALUE", value, indent, f);
			}
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::VarDecls {
			qualifiers,
			type_,
			idents,
			eq,
			value,
			semi,
		} => {
			write!(f, "VAR_DECLS@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("TYPE", type_, indent, f);
			print_tree_expr("IDENTS", idents, indent, f);
			if let Some(eq) = eq {
				write!(f, "\r\n{:indent$}EQ@{}", "", eq, indent = indent * 2);
			}
			if let Some(value) = value {
				print_tree_expr("VALUE", value, indent, f);
			}
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::FnDef {
			qualifiers,
			return_type,
			ident,
			l_paren,
			params,
			r_paren,
			semi,
		} => {
			write!(f, "FN_DEF@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("RETURN_TYPE", return_type, indent, f);
			print_tree_ident(ident, indent, f);
			write!(
				f,
				"\r\n{:indent$}PARAMS@{}",
				"",
				Span::new(
					l_paren.start,
					if let Some(r_paren) = r_paren {
						r_paren.end
					} else {
						if let Some(span) = params.span() {
							span.end
						} else {
							l_paren.end
						}
					}
				),
				indent = indent * 2
			);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}L_PAREN@{}",
				"",
				l_paren,
				indent = indent * 2
			);
			print_tree_params(params, indent, f);
			if let Some(r_paren) = r_paren {
				write!(
					f,
					"\r\n{:indent$}R_PAREN@{}",
					"",
					r_paren,
					indent = indent * 2
				);
			}
			let indent = indent - 1;
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::FnDecl {
			qualifiers,
			return_type,
			ident,
			l_paren,
			params,
			r_paren,
			body,
		} => {
			write!(f, "FN_DECL@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			print_tree_expr("RETURN_TYPE", return_type, indent, f);
			print_tree_ident(ident, indent, f);
			write!(
				f,
				"\r\n{:indent$}PARAMS@{}",
				"",
				Span::new(
					l_paren.start,
					if let Some(r_paren) = r_paren {
						r_paren.end
					} else {
						if let Some(span) = params.span() {
							span.end
						} else {
							l_paren.end
						}
					}
				),
				indent = indent * 2
			);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}L_PAREN@{}",
				"",
				l_paren,
				indent = indent * 2
			);
			print_tree_params(params, indent, f);
			if let Some(r_paren) = r_paren {
				write!(
					f,
					"\r\n{:indent$}R_PAREN@{}",
					"",
					r_paren,
					indent = indent * 2
				);
			}
			let indent = indent - 1;
			print_tree_scope(body, indent, f);
			Ok(())
		}
		NodeTy::StructDef {
			qualifiers,
			kw,
			ident,
			semi,
		} => {
			write!(f, "STRUCT_DEF@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			write!(
				f,
				"\r\n{:indent$}STRUCT_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			print_tree_ident(ident, indent, f);
			write!(f, "\r\n{:indent$}SEMI@{}", "", semi, indent = indent * 2);
			Ok(())
		}
		NodeTy::StructDecl {
			qualifiers,
			kw,
			ident,
			body,
			instance,
			semi,
		} => {
			write!(f, "STRUCT_DECL@{}", node.span);
			let indent = indent + 1;
			print_tree_qualifiers(qualifiers, indent, f);
			write!(
				f,
				"\r\n{:indent$}STRUCT_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			print_tree_ident(ident, indent, f);
			print_tree_scope(body, indent, f);
			if let Some(instance) = instance {
				write!(
					f,
					"\r\n{:indent$}INSTANCE_IDENT@{}",
					"",
					instance.span,
					indent = indent * 2
				);
			}
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::ExprStmt { expr, semi } => {
			write!(f, "EXPR_STMT@{}", node.span);
			let indent = indent + 1;
			print_tree_expr("EXPR", expr, indent, f);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::Scope(scope) => {
			write!(f, "SCOPE@{}", scope.span);
			let indent = indent + 1;
			if let Some(opening) = scope.opening {
				write!(
					f,
					"\r\n{:indent$}OPENING@{}",
					"",
					opening,
					indent = indent * 2
				);
			}
			for node in &scope.inner {
				print_tree_node(node, indent, f);
			}
			if let Some(closing) = scope.closing {
				write!(
					f,
					"\r\n{:indent$}CLOSING@{}",
					"",
					closing,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::If { branches } => {
			use crate::cst::IfTy;

			write!(f, "IF@{}", node.span);
			let indent = indent + 1;
			for branch in branches {
				match &branch.ty {
					IfTy::If(kw) => {
						write!(
							f,
							"\r\n{:indent$}IF_BRANCH@{}",
							"",
							branch.span,
							indent = indent * 2
						);
						let indent = indent + 1;
						write!(
							f,
							"\r\n{:indent$}IF_KW@{}",
							"",
							kw,
							indent = indent * 2
						)
					}
					IfTy::ElseIf(kw1, kw2) => {
						write!(
							f,
							"\r\n{:indent$}ELSE_IF_BRANCH@{}",
							"",
							branch.span,
							indent = indent * 2
						);
						let indent = indent + 1;
						write!(
							f,
							"\r\n{:indent$}ELSE_KW@{}",
							"",
							kw1,
							indent = indent * 2
						);
						write!(
							f,
							"\r\n{:indent$}IF_KW@{}",
							"",
							kw2,
							indent = indent * 2
						)
					}
					IfTy::Else(kw) => {
						write!(
							f,
							"\r\n{:indent$}ELSE_BRANCH@{}",
							"",
							branch.span,
							indent = indent * 2
						);
						let indent = indent + 1;
						write!(
							f,
							"\r\n{:indent$}ELSE_KW@{}",
							"",
							kw,
							indent = indent * 2
						)
					}
				};

				let indent = indent + 1;
				if let Some(l_paren) = &branch.l_paren {
					write!(
						f,
						"\r\n{:indent$}L_PAREN@{}",
						"",
						l_paren,
						indent = indent * 2
					);
				}
				if let Some(cond) = &branch.cond {
					write!(
						f,
						"\r\n{:indent$}CONDITION@{}",
						"",
						cond.span,
						indent = indent * 2
					);
					print_tree_node(cond, indent + 1, f);
				}
				if let Some(r_paren) = &branch.r_paren {
					write!(
						f,
						"\r\n{:indent$}R_PAREN@{}",
						"",
						r_paren,
						indent = indent * 2
					);
				}
				if let Some(body) = &branch.body {
					print_tree_scope(body, indent, f);
				}
			}
			Ok(())
		}
		NodeTy::Switch {
			kw,
			l_paren,
			expr,
			r_paren,
			l_brace,
			cases,
			r_brace,
		} => {
			write!(f, "SWITCH@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}SWITCH_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			if let Some(l_paren) = l_paren {
				write!(
					f,
					"\r\n{:indent$}L_PAREN@{}",
					"",
					l_paren,
					indent = indent * 2
				);
			}
			if let Some(nodes) = expr {
				print_tree_nodes("SWITCH_EXPR", nodes, indent, f);
			}
			if let Some(r_paren) = r_paren {
				write!(
					f,
					"\r\n{:indent$}R_PAREN@{}",
					"",
					r_paren,
					indent = indent * 2
				);
			}
			if let Some(l_brace) = l_brace {
				write!(
					f,
					"\r\n{:indent$}L_BRACE@{}",
					"",
					l_brace,
					indent = indent * 2
				);
			}
			let indent = indent + 1;
			for case in cases {
				write!(
					f,
					"\r\n{:indent$}CASE@{}",
					"",
					case.span,
					indent = indent * 2
				);
				let indent = indent + 1;
				write!(
					f,
					"\r\n{:indent$}{}@{}",
					"",
					if case.is_default {
						"DEFAULT_KW"
					} else {
						"CASE_KW"
					},
					case.kw,
					indent = indent * 2
				);
				if let Some(expr) = &case.expr {
					print_tree_nodes("EXPR", expr, indent, f);
				}
				if let Some(colon) = &case.colon {
					write!(
						f,
						"\r\n{:indent$}COLON@{}",
						"",
						colon,
						indent = indent * 2
					);
				}
				if let Some(body) = &case.body {
					print_tree_scope(body, indent, f);
				}
			}
			let indent = indent - 1;
			if let Some(r_brace) = r_brace {
				write!(
					f,
					"\r\n{:indent$}R_BRACE@{}",
					"",
					r_brace,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::For {
			kw,
			l_paren,
			nodes,
			r_paren,
			body,
		} => {
			write!(f, "FOR@{}", node.span);
			let indent = indent + 1;
			write!(f, "\r\n{:indent$}FOR_KW@{}", "", kw, indent = indent * 2);
			if l_paren.is_some() || nodes.is_some() || r_paren.is_some() {
				write!(
					f,
					"\r\n{:indent$}STMTS@{}",
					"",
					{
						let start = if let Some(l_paren) = l_paren {
							l_paren.start
						} else if let Some(nodes) = nodes {
							nodes.span().unwrap().start
						} else if let Some(r_paren) = r_paren {
							r_paren.start
						} else {
							unreachable!()
						};

						let end = if let Some(r_paren) = r_paren {
							r_paren.end
						} else if let Some(nodes) = nodes {
							nodes.span().unwrap().end
						} else if let Some(l_paren) = l_paren {
							l_paren.end
						} else {
							unreachable!()
						};

						Span::new(start, end)
					},
					indent = indent * 2
				);
				let indent = indent + 1;
				if let Some(l_paren) = l_paren {
					write!(
						f,
						"\r\n{:indent$}L_PAREN@{}",
						"",
						l_paren,
						indent = indent * 2
					);
				}
				if let Some(nodes) = nodes {
					for entry in nodes.entry_iter() {
						match entry {
							Either::Left(n) => {
								print_tree_nodes("STMT", n, indent, f);
								Ok(())
							}
							Either::Right(span) => write!(
								f,
								"\r\n{:indent$}SEMI@{}",
								"",
								span,
								indent = indent * 2
							),
						};
					}
				}
				if let Some(r_paren) = r_paren {
					write!(
						f,
						"\r\n{:indent$}R_PAREN@{}",
						"",
						r_paren,
						indent = indent * 2
					);
				}
			}
			if let Some(body) = &body {
				print_tree_scope(body, indent, f);
			}
			Ok(())
		}
		NodeTy::While {
			kw,
			l_paren,
			cond,
			r_paren,
			body,
		} => {
			write!(f, "WHILE@{}", node.span);
			let indent = indent + 1;
			write!(f, "\r\n{:indent$}WHILE_KW@{}", "", kw, indent = indent * 2);
			if let Some(l_paren) = l_paren {
				write!(
					f,
					"\r\n{:indent$}L_PAREN@{}",
					"",
					l_paren,
					indent = indent * 2
				);
			}
			if let Some(cond) = cond {
				print_tree_nodes("CONDITION", cond, indent, f);
			}
			if let Some(r_paren) = r_paren {
				write!(
					f,
					"\r\n{:indent$}R_PAREN@{}",
					"",
					r_paren,
					indent = indent * 2
				);
			}
			if let Some(body) = body {
				print_tree_scope(body, indent, f);
			}
			Ok(())
		}
		NodeTy::DoWhile {
			do_kw,
			body,
			while_kw,
			l_paren,
			cond,
			r_paren,
			semi,
		} => {
			write!(f, "DO_WHILE@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}DO_WHILE_KW@{}",
				"",
				do_kw,
				indent = indent * 2
			);
			if let Some(body) = body {
				print_tree_scope(body, indent, f);
			}
			if let Some(while_kw) = while_kw {
				write!(
					f,
					"\r\n{:indent$}WHILE_KW@{}",
					"",
					while_kw,
					indent = indent * 2
				);
			}
			if let Some(l_paren) = l_paren {
				write!(
					f,
					"\r\n{:indent$}L_PAREN@{}",
					"",
					l_paren,
					indent = indent * 2
				);
			}
			if let Some(cond) = cond {
				print_tree_nodes("CONDITION", cond, indent, f);
			}
			if let Some(r_paren) = r_paren {
				write!(
					f,
					"\r\n{:indent$}R_PAREN@{}",
					"",
					r_paren,
					indent = indent * 2
				);
			}
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::Return { kw, value, semi } => {
			write!(f, "RETURN@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}RETURN_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			if let Some(value) = value {
				print_tree_expr("EXPR", value, indent, f);
			}
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::Break { kw, semi } => {
			write!(f, "BREAK@{}", node.span);
			let indent = indent + 1;
			write!(f, "\r\n{:indent$}BREAK_KW@{}", "", kw, indent = indent * 2);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::Continue { kw, semi } => {
			write!(f, "CONTINUE@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}CONTINUE_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		NodeTy::Discard { kw, semi } => {
			write!(f, "DISCARD@{}", node.span);
			let indent = indent + 1;
			write!(
				f,
				"\r\n{:indent$}DISCARD_KW@{}",
				"",
				kw,
				indent = indent * 2
			);
			if let Some(semi) = semi {
				write!(
					f,
					"\r\n{:indent$}SEMI@{}",
					"",
					semi,
					indent = indent * 2
				);
			}
			Ok(())
		}
		_ => write!(f, "UNIMPLEMENTED"),
	}
}

#[allow(unused_must_use)]
fn print_tree_qualifiers(
	qualifiers: &[Qualifier],
	indent: usize,
	f: &mut String,
) {
	if qualifiers.is_empty() {
		return;
	}

	write!(
		f,
		"\r\n{:indent$}QUALIFIERS@{}",
		"",
		Span::new(
			qualifiers.first().unwrap().span.start,
			qualifiers.last().unwrap().span.end
		),
		indent = indent * 2
	);
	let indent = indent + 1;

	use crate::cst::{
		Interpolation, LayoutTy, Memory, Precision, QualifierTy, Storage,
	};

	for qualifier in qualifiers {
		write!(f, "\r\n{:indent$}", "", indent = indent * 2);
		match &qualifier.ty {
			QualifierTy::Storage(ty) => write!(
				f,
				"{word}@{span}\r\n{:indent$}{word}_KW@{span}",
				"",
				word = match ty {
					Storage::Const => "CONST",
					Storage::In => "IN",
					Storage::Out => "OUT",
					Storage::InOut => "INOUT",
					Storage::Attribute => "ATTRIBUTE",
					Storage::Uniform => "UNIFORM",
					Storage::Varying => "VARYING",
					Storage::Buffer => "BUFFER",
					Storage::Shared => "SHARED",
					Storage::Centroid => "CENTROID",
					Storage::Sample => "SAMPLE",
					Storage::Patch => "PATCH",
				},
				indent = (indent + 1) * 2,
				span = qualifier.span,
			),
			QualifierTy::Layout {
				kw,
				l_paren,
				idents,
				r_paren,
			} => {
				write!(f, "LAYOUT@{}", qualifier.span);

				let indent = indent + 1;
				write!(
					f,
					"\r\n{:indent$}LAYOUT_KW@{}",
					"",
					kw,
					indent = indent * 2
				);
				if let Some(l_paren) = l_paren {
					write!(
						f,
						"\r\n{:indent$}L_PAREN@{}",
						"",
						l_paren,
						indent = indent * 2
					);
				}
				if let Some(idents) = idents {
					write!(
						f,
						"\r\n{:indent$}IDENTS@{}",
						"",
						idents.span().unwrap(),
						indent = indent * 2
					);
					let indent = indent + 1;
					for node in idents.entry_iter() {
						match node {
							Either::Left(layout) => match &layout.ty {
								LayoutTy::Invalid => {
									write!(
										f,
										"\r\n{:indent$}INVALID@{}",
										"",
										layout.span,
										indent = indent * 2
									);
								}
								LayoutTy::Shared => {
									write!(
										f,
										"\r\n{:indent$}SHARED@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}SHARED_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Packed => {
									write!(
										f,
										"\r\n{:indent$}PACKED@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}PACKED_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Std140 => {
									write!(
										f,
										"\r\n{:indent$}STD140@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}STD140_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Std430 => {
									write!(
										f,
										"\r\n{:indent$}STD430@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}STD430_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::RowMajor => {
									write!(
										f,
										"\r\n{:indent$}ROW_MAJOR@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}ROW_MAJOR_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::ColumnMajor => {
									write!(
										f,
										"\r\n{:indent$}COLUMN_MAJOR@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}COLUMN_MAJOR_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Binding { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}BINDING@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}BINDING_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Offset { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}OFFSET@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}OFFSET_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Align { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}ALIGN@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}ALIGN_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Location { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}LOCATION@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LOCATION_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Component { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}COMPONENT@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}COMPONENT_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Index { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}INDEX@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}INDEX_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Points => {
									write!(
										f,
										"\r\n{:indent$}POINTS@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}POINTS_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Lines => {
									write!(
										f,
										"\r\n{:indent$}LINES@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LINES_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Isolines => {
									write!(
										f,
										"\r\n{:indent$}ISOLINES@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}ISOLINES_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Triangles => {
									write!(
										f,
										"\r\n{:indent$}TRIANGLES@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}TRIANGLES_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Quads => {
									write!(
										f,
										"\r\n{:indent$}QUADS@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}QUADS_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::EqualSpacing => {
									write!(
										f,
										"\r\n{:indent$}EQUAL_SPACING@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}EQUAL_SPACING_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::FractionalEvenSpacing => {
									write!(
										f,
										"\r\n{:indent$}FRACTIONAL_EVEN_SPACING@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}FRACTIONAL_EVEN_SPACING_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::FractionalOddSpacing => {
									write!(
										f,
										"\r\n{:indent$}FRACTIONAL_ODD_SPACING@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}FRACTIONAL_ODD_SPACING_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Clockwise => {
									write!(
										f,
										"\r\n{:indent$}CLOCKWISE@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}CLOCKWISE_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::CounterClockwise => {
									write!(
										f,
										"\r\n{:indent$}COUNTER_CLOCKWISE@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}COUNTER_CLOCKWISE_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::PointMode => {
									write!(
										f,
										"\r\n{:indent$}POINT_MODE@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}POINT_MODE_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::LinesAdjacency => {
									write!(
										f,
										"\r\n{:indent$}LINES_ADJACENCY@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LINES_ADJACENCY_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::TrianglesAdjacency => {
									write!(
										f,
										"\r\n{:indent$}TRIANGLES_ADJACENCY@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}TRIANGLES_ADJACENCY_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::Invocations { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}INVOCATIONS@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}INVOCATIONS_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::OriginUpperLeft => {
									write!(
										f,
										"\r\n{:indent$}ORIGIN_UPPER_LEFT@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}ORIGIN_UPPER_LEFT_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::PixelCenterInteger => {
									write!(
										f,
										"\r\n{:indent$}PIXEL_CENTER_INTEGER@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
									f,
									"\r\n{:indent$}PIXEL_CENTER_INTEGER_KW@{}",
									"",
									layout.span,
									indent = (indent + 1) * 2
								);
								}
								LayoutTy::EarlyFragmentTests => {
									write!(
										f,
										"\r\n{:indent$}EARLY_FRAGMENT_TESTS@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
									f,
									"\r\n{:indent$}EARLY_FRAGMENT_TESTS_KW@{}",
									"",
									layout.span,
									indent = (indent + 1) * 2
								);
								}
								LayoutTy::LocalSizeX { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_X@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_X_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::LocalSizeY { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_Y@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_Y_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::LocalSizeZ { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_Z@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LOCAL_SIZE_Z_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::XfbBuffer { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}XFB_BUFFER@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}XFB_BUFFER_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::XfbStride { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}XFB_STRIDE@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}XFB_STRIDE_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::XfbOffset { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}XFB_OFFSET@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}XFB_OFFSET_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Vertices { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}VERTICES@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}VERTICES_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::LineStrip => {
									write!(
										f,
										"\r\n{:indent$}LINE_STRIP@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}LINE_STRIP_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::TriangleStrip => {
									write!(
										f,
										"\r\n{:indent$}TRIANGLE_STRIP@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}TRIANGLE_STRIP_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::MaxVertices { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}MAX_VERTICES@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}MAX_VERTICES_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::Stream { kw, eq, value } => {
									write!(
										f,
										"\r\n{:indent$}STREAM@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}STREAM_KW@{}",
										"",
										kw,
										indent = (indent + 1) * 2
									);
									if let Some(eq) = eq {
										write!(
											f,
											"\r\n{:indent$}EQ@{}",
											"",
											eq,
											indent = (indent + 1) * 2
										);
									}
									if let Some(value) = value {
										print_tree_expr(
											"VALUE",
											value,
											indent + 1,
											f,
										);
									}
								}
								LayoutTy::DepthAny => {
									write!(
										f,
										"\r\n{:indent$}DEPTH_ANY@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}DEPTH_ANY_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::DepthGreater => {
									write!(
										f,
										"\r\n{:indent$}DEPTH_GREATER@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}DEPTH_GREATER_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::DepthLess => {
									write!(
										f,
										"\r\n{:indent$}DEPTH_LESS@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}DEPTH_LESS_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
								LayoutTy::DepthUnchanged => {
									write!(
										f,
										"\r\n{:indent$}DEPTH_UNCHANGED@{}",
										"",
										layout.span,
										indent = indent * 2
									);
									write!(
										f,
										"\r\n{:indent$}DEPTH_UNCHANGED_KW@{}",
										"",
										layout.span,
										indent = (indent + 1) * 2
									);
								}
							},
							Either::Right(span) => {
								write!(
									f,
									"\r\n{:indent$}COMMA@{}",
									"",
									span,
									indent = indent * 2
								);
							}
						}
					}
					let indent = indent - 1;
				}
				if let Some(r_paren) = r_paren {
					write!(
						f,
						"\r\n{:indent$}R_PAREN@{}",
						"",
						r_paren,
						indent = indent * 2
					);
				}
				Ok(())
			}
			QualifierTy::Interpolation(ty) => write!(
				f,
				"{word}@{span}\r\n{:indent$}{word}_KW@{span}",
				"",
				word = match ty {
					Interpolation::Smooth => "SMOOTH",
					Interpolation::Flat => "FLAT",
					Interpolation::NoPerspective => "NOPERSPECTIVE",
				},
				indent = (indent + 1) * 2,
				span = qualifier.span
			),
			QualifierTy::Precision(ty) => {
				write!(
					f,
					"{word}@{span}\r\n{:indent$}{word}_KW@{span}",
					"",
					word = match ty {
						Precision::HighP => "HIGH_P",
						Precision::MediumP => "MEDIUM_P",
						Precision::LowP => "LOW_P",
					},
					indent = (indent + 1) * 2,
					span = qualifier.span
				)
			}
			QualifierTy::Invariant => {
				write!(
					f,
					"INVARIANT@{span}\r\n{:indent$}INVARIANT_KW@{span}",
					"",
					indent = (indent + 1) * 2,
					span = qualifier.span
				)
			}
			QualifierTy::Precise => {
				write!(
					f,
					"PRECISE@{span}\r\n{:indent$}PRECISE_KW@{span}",
					"",
					indent = (indent + 1) * 2,
					span = qualifier.span
				)
			}
			QualifierTy::Memory(ty) => write!(
				f,
				"{word}@{span}\r\n{:indent$}{word}_KW@{span}",
				"",
				word = match ty {
					Memory::Coherent => "COHERENT_KW",
					Memory::Volatile => "VOLATILE_KW",
					Memory::Restrict => "RESTRICT_KW",
					Memory::Readonly => "READONLY_KW",
					Memory::Writeonly => "WRITEONLY_KW",
				},
				indent = (indent + 1) * 2,
				span = qualifier.span
			),
		};
	}
}

#[allow(unused_must_use)]
fn print_tree_expr(label: &str, expr: &Expr, indent: usize, f: &mut String) {
	write!(f, "\r\n{:indent$}", "", indent = indent * 2);
	write!(f, "{}@{}", label, expr.span);
}

#[allow(unused_must_use)]
fn print_tree_ident(ident: &Ident, indent: usize, f: &mut String) {
	write!(f, "\r\n{:indent$}", "", indent = indent * 2);
	write!(f, "IDENT@{}", ident.span);
}

#[allow(unused_must_use)]
fn print_tree_scope(scope: &Scope, indent: usize, f: &mut String) {
	write!(
		f,
		"\r\n{:indent$}SCOPE@{}",
		"",
		scope.span,
		indent = indent * 2
	);
	let indent = indent + 1;
	if let Some(opening) = scope.opening {
		write!(
			f,
			"\r\n{:indent$}OPENING@{}",
			"",
			opening,
			indent = indent * 2
		);
	}
	for node in &scope.inner {
		print_tree_node(node, indent, f);
	}
	if let Some(closing) = scope.closing {
		write!(
			f,
			"\r\n{:indent$}CLOSING@{}",
			"",
			closing,
			indent = indent * 2
		);
	}
}

#[allow(unused_must_use)]
fn print_tree_nodes(label: &str, nodes: &Nodes, indent: usize, f: &mut String) {
	write!(
		f,
		"\r\n{:indent$}{label}@{}",
		"",
		nodes.span(),
		indent = indent * 2
	);
	for node in &nodes.inner {
		print_tree_node(node, indent + 1, f);
	}
}

#[allow(unused_must_use)]
fn print_tree_params(list: &List<Param>, indent: usize, f: &mut String) {
	for entry in list.entry_iter() {
		match entry {
			Either::Left(param) => {
				write!(
					f,
					"\r\n{:indent$}PARAM@{}",
					"",
					param.span,
					indent = indent * 2
				);
				let indent = indent + 1;
				print_tree_qualifiers(&param.qualifiers, indent, f);
				print_tree_expr("TYPE", &param.type_, indent, f);
				if let Some(ident) = &param.ident {
					print_tree_expr("IDENT", ident, indent, f);
				}
				Ok(())
			}
			Either::Right(span) => write!(
				f,
				"\r\n{:indent$}COMMA@{}",
				"",
				span,
				indent = indent * 2
			),
		};
	}
}
