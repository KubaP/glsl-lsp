//! Functionality for pretty-printing the abstract syntax tree.

use super::{ast::*, NodeHandle};
use crate::{Either, Either3};
use generational_arena::Arena;
use std::fmt::Write;

struct PrintCtx<'a> {
	arena: &'a Arena<Node>,
	structs: &'a [super::StructSymbol],
	subroutines: &'a [super::SubroutineSymbol],
}

pub(super) fn print_ast(
	ast: &super::Ast,
	root_handle: generational_arena::Index,
) -> String {
	let mut writer = Writer {
		buffer: String::with_capacity(1_000),
		indent: 0,
	};

	let root_node = ast.arena.get(root_handle).expect("Ensured by parser");

	let NodeTy::TranslationUnit(scope) = &root_node.ty else { unreachable!("Ensured by parser"); };

	for handle in &scope.contents {
		write!(
			writer.buffer,
			"{:indent$}",
			"",
			indent = writer.indent * INDENT
		)
		.unwrap();
		print_node(
			&mut writer,
			&PrintCtx {
				arena: &ast.arena,
				structs: &ast.structs,
				subroutines: &ast.subroutines,
			},
			*handle,
		);
	}

	writer.buffer.shrink_to_fit();
	writer.buffer
}

/// Number of spaces to indent by.
const INDENT: usize = 4;

struct Writer {
	buffer: String,
	indent: usize,
}

impl Writer {
	fn indent(&mut self) {
		self.indent += 1;
	}
	fn de_indent(&mut self) {
		self.indent -= 1;
	}
}

macro_rules! new_line_whole {
	($writer:expr, $($tts:tt)*) => {
		{
			::std::write!($writer.buffer, "{:indent$}", "", indent = $writer.indent * INDENT).unwrap();
			::std::write!($writer.buffer, $($tts)*).unwrap();
			::std::write!($writer.buffer, "\r\n").unwrap();
		}
	};
}

macro_rules! new_line_part {
	($writer:expr, $($tts:tt)*) => {
		{
			::std::write!($writer.buffer, "{:indent$}", "", indent = $writer.indent * INDENT).unwrap();
			::std::write!($writer.buffer, $($tts)*).unwrap();
		}
	};
	($writer:expr) => {
		{
			::std::write!($writer.buffer, "{:indent$}", "", indent = $writer.indent * INDENT).unwrap();
		}
	};
}

macro_rules! continue_eol {
	($writer:expr, $($tts:tt)*) => {
		{
			::std::write!($writer.buffer, $($tts)*).unwrap();
			::std::write!($writer.buffer, "\r\n").unwrap();
		}
	};
}

fn print_node<'a>(w: &mut Writer, ctx: &PrintCtx<'a>, handle: NodeHandle) {
	let node = ctx.arena.get(handle.0).unwrap();
	match &node.ty {
		NodeTy::TranslationUnit(_) => unreachable!(),
		NodeTy::Empty => continue_eol!(w, "Empty"),
		NodeTy::Expr(expr) => {
			continue_eol!(w, "Expr(");
			w.indent();
			new_line_part!(w);
			print_expr(w, ctx, expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Block(body) => {
			continue_eol!(w, "Block(");
			print_scope(w, ctx, body);
			new_line_whole!(w, ")");
		}
		NodeTy::TypeSpecifier(type_) => {
			continue_eol!(w, "Type(");
			w.indent();
			print_type(w, ctx, type_);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::VarDef {
			type_,
			ident,
			eq_span: _,
			init_expr,
		} => {
			continue_eol!(w, "VarDef(");
			w.indent();
			new_line_part!(w, "type: ");
			print_type(w, ctx, type_);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			if let Omittable::Some(expr) = init_expr {
				new_line_part!(w, "init_expr: ");
				w.indent();
				print_expr(w, ctx, expr);
				w.de_indent();
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Qualifiers(qualifiers) => {
			continue_eol!(w, "Qualifiers: [");
			print_qualifiers(w, ctx, qualifiers);
			new_line_whole!(w, "]");
		}
		NodeTy::VarDefs(vars) => {
			continue_eol!(w, "VarDef(");
			w.indent();
			for (type_, ident, _, init_expr) in vars {
				new_line_whole!(w, "(");
				w.indent();
				new_line_part!(w, "type: ");
				print_type(w, ctx, type_);
				new_line_whole!(w, "ident: {}", print_ident(ident));
				if let Omittable::Some(expr) = init_expr {
					new_line_part!(w, "init_expr: ");
					w.indent();
					print_expr(w, ctx, expr);
					w.de_indent();
				}
				w.de_indent();
				new_line_whole!(w, ")");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::FnDecl {
			return_type,
			ident,
			params,
		} => {
			continue_eol!(w, "FnDecl(");
			w.indent();
			new_line_part!(w, "return type: ");
			print_type(w, ctx, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, ctx, params);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::FnDef {
			return_type,
			ident,
			params,
			body,
		} => {
			continue_eol!(w, "FnDef(");
			w.indent();
			new_line_part!(w, "return type: ");
			print_type(w, ctx, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, ctx, params);
			new_line_whole!(w, "body: Scope(");
			print_scope(w, ctx, body);
			new_line_whole!(w, ")");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineTypeDecl {
			return_type,
			ident,
			params,
		} => {
			continue_eol!(w, "SubroutineTypeDecl(");
			w.indent();
			new_line_part!(w, "return type: ");
			print_type(w, ctx, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, ctx, params);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineFnDefAssociation {
			associations,
			return_type,
			ident,
			params,
			body,
		} => {
			continue_eol!(w, "SubroutineFnDef(");
			w.indent();
			new_line_whole!(w, "associations: [");
			w.indent();
			for (_, ident) in associations {
				new_line_whole!(w, "{}", print_ident(ident));
			}
			w.de_indent();
			new_line_whole!(w, "]");
			new_line_part!(w, "return type: ");
			print_type(w, ctx, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, ctx, params);
			new_line_whole!(w, "body: Scope(");
			print_scope(w, ctx, body);
			new_line_whole!(w, ")");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineUniformDef { type_, ident } => {
			continue_eol!(w, "SubroutineUniformDef(");
			w.indent();
			new_line_part!(w, "type: ");
			print_sub_type(w, ctx, type_);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineUniformDefs(vars) => {
			continue_eol!(w, "SubroutineUniformDef(");
			w.indent();
			for (type_, ident) in vars {
				new_line_whole!(w, "(");
				w.indent();
				new_line_part!(w, "type: ");
				print_sub_type(w, ctx, type_);
				new_line_whole!(w, "ident: {}", print_ident(ident));
				w.de_indent();
				new_line_whole!(w, ")");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::StructDecl { qualifiers, name } => {
			continue_eol!(w, "StructDecl(");
			w.indent();
			if let Omittable::Some(qualifiers) = qualifiers {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, ctx, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(name));
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::StructDef {
			qualifiers,
			name,
			fields,
			instances,
		} => {
			continue_eol!(w, "StructDef(");
			w.indent();
			if let Omittable::Some(qualifiers) = qualifiers {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, ctx, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(name));
			new_line_whole!(w, "fields: [");
			w.indent();
			for (type_, ident) in fields.iter() {
				new_line_part!(w, "type: ");
				print_type(w, ctx, type_);
				if let Omittable::Some(ident) = ident {
					write!(w.buffer, " , ident: {}", print_ident(ident));
				}
			}
			w.de_indent();
			new_line_whole!(w, "]");
			if !instances.is_empty() {
				new_line_whole!(w, "instances: [");
				w.indent();
				for (ident, arr_size) in instances {
					new_line_part!(w, "ident: {}", print_ident(ident));
					if let Omittable::Some(arr_size) = arr_size {
						//continue_eol!(w, " , arr_size: ");
					}
				}
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::InterfaceDef {
			qualifiers,
			name,
			fields,
			instances,
		} => {
			continue_eol!(w, "InterfaceDef(");
			w.indent();
			if let Some(qualifiers) = qualifiers {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, ctx, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(name));
			new_line_whole!(w, "fields: [");
			w.indent();
			for (type_, ident) in fields.iter() {
				new_line_part!(w, "type: ");
				print_type(w, ctx, type_);
				if let Omittable::Some(ident) = ident {
					write!(w.buffer, " , ident: {}", print_ident(ident));
				}
			}
			w.de_indent();
			new_line_whole!(w, "]");
			if !instances.is_empty() {
				new_line_whole!(w, "instances: [");
				w.indent();
				for (ident, arr_size) in instances {
					new_line_part!(w, "ident: {}", print_ident(ident));
					if let Omittable::Some(arr_size) = arr_size {
						//continue_eol!(w, " , arr_size: ");
					}
				}
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::If(branches) => {
			continue_eol!(w, "If(");
			w.indent();
			for branch in branches {
				match &branch.condition.0 {
					IfCondition::If(e) => {
						new_line_whole!(w, "if: (");
						w.indent();
						if let Some(cond) = e {
							new_line_part!(w, "cond: ");
							print_expr(w, ctx, &cond);
						}
						if let Some(ref body) = branch.body {
							new_line_whole!(w, "body: Scope(");
							print_scope(w, ctx, &body);
							new_line_whole!(w, ")");
						}
						w.de_indent();
						new_line_whole!(w, ")");
					}
					IfCondition::ElseIf(e) => {
						new_line_whole!(w, "else if: (");
						w.indent();
						if let Some(cond) = e {
							new_line_part!(w, "cond: ");
							print_expr(w, ctx, &cond);
						}
						if let Some(ref body) = branch.body {
							new_line_whole!(w, "body: Scope(");
							print_scope(w, ctx, &body);
							new_line_whole!(w, ")");
						}
						w.de_indent();
						new_line_whole!(w, ")");
					}
					IfCondition::Else => {
						new_line_whole!(w, "else: (");
						w.indent();
						if let Some(ref body) = branch.body {
							new_line_whole!(w, "body: Scope(");
							print_scope(w, ctx, &body);
							new_line_whole!(w, ")");
						}
						w.de_indent();
						new_line_whole!(w, ")");
					}
				}
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Switch { cond, cases } => {
			continue_eol!(w, "Switch(");
			w.indent();
			if let Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_expr(w, ctx, cond);
			}
			new_line_whole!(w, "cases: [");
			w.indent();
			for case in cases {
				match &case.expr {
					Either::Left(e) => {
						new_line_whole!(w, "case: (");
						w.indent();
						if let Some(ref expr) = e {
							new_line_part!(w, "expr: ");
							print_expr(w, ctx, &expr);
						}
						new_line_whole!(w, "body: Scope(");
						if let Some(ref body) = case.body {
							print_scope(w, ctx, &body);
						}
						new_line_whole!(w, ")");
						w.de_indent();
						new_line_whole!(w, ")");
					}
					Either::Right(_) => {
						new_line_whole!(w, "default: Scope(");
						if let Some(ref body) = case.body {
							print_scope(w, ctx, &body);
						}
						new_line_whole!(w, ")");
					}
				}
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::For {
			init,
			cond,
			inc,
			body,
		} => {
			continue_eol!(w, "For(");
			w.indent();
			if let Omittable::Some(init) = init {
				new_line_part!(w, "init: ");
				match init {
					Either::Left(expr) => {
						print_expr(w, ctx, expr);
					}
					Either::Right(_) => {}
				}
			}
			if let Omittable::Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_expr(w, ctx, cond);
			}
			if let Omittable::Some(inc) = inc {
				new_line_part!(w, "inc: ");
				print_expr(w, ctx, inc);
			}
			if let Some(body) = body {
				new_line_whole!(w, "body: Scope(");
				print_scope(w, ctx, body);
				new_line_whole!(w, ")");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::While { cond, body } => {
			continue_eol!(w, "While(");
			w.indent();
			if let Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_expr(w, ctx, cond);
			}
			new_line_whole!(w, "body: Scope(");
			print_scope(w, ctx, body);
			new_line_whole!(w, ")");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::DoWhile { body, cond } => {
			continue_eol!(w, "Do-While(");
			w.indent();
			new_line_whole!(w, "body: Scope(");
			print_scope(w, ctx, body);
			new_line_whole!(w, ")");
			if let Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_expr(w, ctx, cond);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Break => {
			continue_eol!(w, "Break");
		}
		NodeTy::Continue => {
			continue_eol!(w, "Continue");
		}
		NodeTy::Discard => {
			continue_eol!(w, "Discard");
		}
		NodeTy::Return { value } => {
			if let Omittable::Some(value) = value {
				continue_eol!(w, "Return(");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, value);
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "Return");
			}
		}
		NodeTy::EmptyDirective => {
			continue_eol!(w, "#Empty");
		}
		NodeTy::VersionDirective { version, profile } => {
			if version.is_some() || profile.is_some() {
				continue_eol!(w, "#Version(");
				w.indent();
				if let Some(version) = version {
					new_line_whole!(w, "version: {}", version.0);
				}
				if let Omittable::Some(profile) = profile {
					new_line_whole!(
						w,
						"profile: {}",
						match profile.0 {
							ProfileTy::Core => "core",
							ProfileTy::Compatability => "compatability",
							ProfileTy::Es => "es",
						}
					);
				}
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Version");
			}
		}
		NodeTy::ExtensionDirective { name, behaviour } => {
			if name.is_some() || behaviour.is_some() {
				continue_eol!(w, "#Extension(");
				w.indent();
				if let Some(name) = name {
					new_line_whole!(w, "name: {}", name.0);
				}
				if let Some(behaviour) = behaviour {
					new_line_whole!(
						w,
						"behaviour: {}",
						match behaviour.0 {
							BehaviourTy::Enable => "enable",
							BehaviourTy::Require => "require",
							BehaviourTy::Warn => "warn",
							BehaviourTy::Disable => "disable",
						}
					);
				}
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Extension");
			}
		}
		NodeTy::LineDirective { line, src_str_num } => {
			if let Some(line) = line {
				continue_eol!(w, "#Line(");
				w.indent();
				new_line_whole!(w, "line: {}", line.0);
				if let Omittable::Some(src_str_num) = src_str_num {
					new_line_whole!(w, "src_str_num: {}", src_str_num.0);
				}
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Line");
			}
		}
		NodeTy::DefineDirective {
			macro_,
			replacement_tokens,
		} => {
			continue_eol!(w, "#Define(");
			w.indent();
			match macro_ {
				Macro::Object { ident } => {
					new_line_whole!(w, "object_macro: {}", print_ident(ident))
				}
				Macro::Function { ident, params } => {
					new_line_whole!(
						w,
						"function_macro: {}(",
						print_ident(ident)
					);
					w.indent();
					for param in params {
						new_line_whole!(w, "{}", print_ident(param));
					}
					w.de_indent();
					new_line_whole!(w, ")");
				}
			}
			new_line_whole!(w, "replacement_tokens: [");
			w.indent();
			for token in replacement_tokens {
				new_line_whole!(w, "{}", token.0);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::UndefDirective { name } => {
			if let Omittable::Some(name) = name {
				continue_eol!(w, "#Undef(");
				w.indent();
				new_line_whole!(w, "name: {}", print_ident(name));
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Undef");
			}
		}
		NodeTy::ErrorDirective { message } => {
			if let Omittable::Some(message) = message {
				continue_eol!(w, "#Error(");
				w.indent();
				new_line_whole!(w, "message: {}", message.0);
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Error");
			}
		}
		NodeTy::PragmaDirective { options } => {
			if let Omittable::Some(options) = options {
				continue_eol!(w, "#Pragma(");
				w.indent();
				new_line_whole!(w, "options: {}", options.0);
				w.de_indent();
				new_line_whole!(w, ")");
			} else {
				continue_eol!(w, "#Pragma");
			}
		}
	}
}

fn print_scope<'a>(w: &mut Writer, ctx: &PrintCtx<'a>, scope: &Scope) {
	w.indent();
	for handle in scope.contents.iter() {
		new_line_part!(w);
		print_node(w, ctx, *handle);
	}
	w.de_indent();
}

fn print_params<'a>(w: &mut Writer, ctx: &PrintCtx<'a>, params: &[Param]) {
	new_line_whole!(w, "params: [");
	w.indent();
	for param in params {
		new_line_whole!(w, "(");
		w.indent();
		new_line_part!(w, "type: ");
		print_type(w, ctx, &param.type_);
		if let Omittable::Some(ref ident) = param.ident {
			new_line_whole!(w, "ident: {}", print_ident(ident));
		}
		w.de_indent();
		new_line_whole!(w, ")");
	}
	w.de_indent();
	new_line_whole!(w, "]");
}

fn print_ident(ident: &Ident) -> &str {
	&ident.name
}

fn print_expr<'a>(w: &mut Writer, ctx: &PrintCtx<'a>, expr: &Expr) {
	match &expr.ty {
		ExprTy::Invalid => continue_eol!(w, "{{invalid}}"),
		ExprTy::Lit(l) => match l {
			Lit::Bool(b) => continue_eol!(w, "{b}"),
			Lit::Int(i) => continue_eol!(w, "{i}"),
			Lit::UInt(u) => continue_eol!(w, "{u}"),
			Lit::Float(f) => continue_eol!(w, "{f}"),
			Lit::Double(d) => continue_eol!(w, "{d}"),
			Lit::InvalidNum => continue_eol!(w, "{{invalid_num}}"),
		},
		ExprTy::Local { name, .. } => continue_eol!(w, "{}", name.name),
		ExprTy::Prefix { op, expr } => {
			continue_eol!(w, "Pre(");
			w.indent();
			new_line_whole!(w, "op: {}", print_pre_op(op));
			new_line_part!(w);
			print_expr(w, ctx, &expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Postfix { expr, op } => {
			continue_eol!(w, "Post(");
			w.indent();
			new_line_whole!(w, "op: {}", print_post_op(op));
			new_line_part!(w);
			print_expr(w, ctx, &expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Binary { left, op, right } => {
			continue_eol!(w, "Bin(");
			w.indent();
			new_line_whole!(w, "op: {}", print_bin_op(op));
			new_line_part!(w, "left: ");
			print_expr(w, ctx, &left);
			new_line_part!(w, "right: ");
			print_expr(w, ctx, &right);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Ternary {
			cond,
			true_,
			false_,
		} => {
			continue_eol!(w, "Ternary(");
			w.indent();
			new_line_part!(w, "cond: ");
			print_expr(w, ctx, &cond);
			new_line_part!(w, "true: ");
			print_expr(w, ctx, &true_);
			new_line_part!(w, "false: ");
			print_expr(w, ctx, &false_);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Parens { expr } => {
			continue_eol!(w, "Paren(");
			w.indent();
			new_line_part!(w);
			print_expr(w, ctx, &expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::ObjAccess { obj, leafs } => {
			continue_eol!(w, "ObjAccess(");
			w.indent();
			new_line_part!(w, "obj: ");
			print_expr(w, ctx, &obj);
			w.indent();
			for (ident, type_) in leafs.iter() {
				new_line_whole!(
					w,
					"{}{}",
					ident.name,
					match type_ {
						Either3::A(_) => " (field)",
						Either3::B(_) => " (method)",
						Either3::C(_) => " (swizzle)",
					}
				);
			}
			w.de_indent();
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Index { item, i } => {
			continue_eol!(w, "Index(");
			w.indent();
			new_line_part!(w, "item: ");
			print_expr(w, ctx, &item);
			if let Omittable::Some(i) = i {
				new_line_part!(w, "i: ");
				print_expr(w, ctx, &i);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::FnCall {
			name,
			handle: _,
			args,
		} => {
			continue_eol!(w, "Fn(");
			w.indent();
			new_line_whole!(w, "ident: {}", print_ident(name));
			new_line_whole!(w, "args: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, ctx, arg);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::SubroutineCall {
			name,
			handle: _,
			args,
		} => {
			continue_eol!(w, "Subroutine(");
			w.indent();
			new_line_whole!(w, "ident: {}", print_ident(name));
			new_line_whole!(w, "args: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, ctx, arg);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::StructConstructor {
			name,
			handle: _,
			args,
		} => {
			continue_eol!(w, "Struct(");
			w.indent();
			new_line_whole!(w, "ident: {}", print_ident(name));
			new_line_whole!(w, "args: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, ctx, arg);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Initializer { args } => {
			continue_eol!(w, "Initializer([");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, ctx, arg);
			}
			w.de_indent();
			new_line_whole!(w, "])");
		}
		ExprTy::ArrConstructor { type_, args } => {
			continue_eol!(w, "ArrayConstructor(");
			w.indent();
			new_line_part!(w, "type: ");
			print_type(w, ctx, type_);
			new_line_whole!(w, "params: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, ctx, arg);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::List { items } => {
			continue_eol!(w, "List([");
			w.indent();
			for item in items {
				new_line_part!(w);
				print_expr(w, ctx, item);
			}
			w.de_indent();
			new_line_whole!(w, "])");
		}
	}
}

fn print_type<'a>(w: &mut Writer, ctx: &PrintCtx<'a>, type_: &Type) {
	match &type_.ty {
		TypeTy::Single(p) => continue_eol!(w, "{}", print_type_handle(ctx, p)),
		TypeTy::Array(p, a) => {
			continue_eol!(w, "{}", print_type_handle(ctx, p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		TypeTy::Array2D(p, a, b) => {
			continue_eol!(w, "{}", print_type_handle(ctx, p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			if let Omittable::Some(expr) = b {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		TypeTy::ArrayND(p, v) => {
			continue_eol!(w, "{}", print_type_handle(ctx, p));
			w.indent();
			for i in v {
				if let Omittable::Some(expr) = i {
					new_line_part!(w, "[");
					w.indent();
					new_line_part!(w);
					print_expr(w, ctx, &expr);
					w.de_indent();
					new_line_whole!(w, "]");
				}
			}
			w.de_indent();
		}
	}
	if let Omittable::Some(qualifiers) = &type_.qualifiers {
		new_line_whole!(w, "+ qualifiers: [");
		print_qualifiers(w, ctx, &qualifiers);
		new_line_whole!(w, "]");
	}
}

fn print_sub_type<'a>(
	w: &mut Writer,
	ctx: &PrintCtx<'a>,
	type_: &SubroutineType,
) {
	match &type_.ty {
		SubroutineTypeTy::Single(p) => {
			continue_eol!(w, "{}", print_sub_type_handle(ctx, p))
		}
		SubroutineTypeTy::Array(p, a) => {
			continue_eol!(w, "{}", print_sub_type_handle(ctx, p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		SubroutineTypeTy::Array2D(p, a, b) => {
			continue_eol!(w, "{}", print_sub_type_handle(ctx, p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			if let Omittable::Some(expr) = b {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, ctx, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		SubroutineTypeTy::ArrayND(p, v) => {
			continue_eol!(w, "{}", print_sub_type_handle(ctx, p));
			w.indent();
			for i in v {
				if let Omittable::Some(expr) = i {
					new_line_part!(w, "[");
					w.indent();
					new_line_part!(w);
					print_expr(w, ctx, &expr);
					w.de_indent();
					new_line_whole!(w, "]");
				}
			}
			w.de_indent();
		}
	}
	if let Omittable::Some(qualifiers) = &type_.qualifiers {
		new_line_whole!(w, "+ qualifiers: [");
		print_qualifiers(w, ctx, &qualifiers);
		new_line_whole!(w, "]");
	}
}

fn print_sub_type_handle<'a>(
	ctx: &PrintCtx<'a>,
	handle: &super::SubroutineHandle,
) -> &'a str {
	&ctx.subroutines[handle.0].name
}

fn print_pre_op(op: &PreOp) -> String {
	(match op.ty {
		PreOpTy::Add => "++",
		PreOpTy::Sub => "--",
		PreOpTy::Neg => "-",
		PreOpTy::Flip => "~",
		PreOpTy::Not => "!",
	})
	.to_owned()
}

fn print_post_op(op: &PostOp) -> String {
	(match op.ty {
		PostOpTy::Add => "++",
		PostOpTy::Sub => "-",
	})
	.to_owned()
}

fn print_bin_op(op: &BinOp) -> String {
	(match op.ty {
		BinOpTy::Add => "+",
		BinOpTy::Sub => "-",
		BinOpTy::Mul => "*",
		BinOpTy::Div => "/",
		BinOpTy::Rem => "%",
		BinOpTy::And => "&",
		BinOpTy::Or => "|",
		BinOpTy::Xor => "^",
		BinOpTy::LShift => "<<",
		BinOpTy::RShift => ">>",
		BinOpTy::Eq => "=",
		BinOpTy::AddEq => "+=",
		BinOpTy::SubEq => "-=",
		BinOpTy::MulEq => "*=",
		BinOpTy::DivEq => "/=",
		BinOpTy::RemEq => "%=",
		BinOpTy::AndEq => "&=",
		BinOpTy::OrEq => "|=",
		BinOpTy::XorEq => "^=",
		BinOpTy::LShiftEq => "<<=",
		BinOpTy::RShiftEq => ">>=",
		BinOpTy::EqEq => "==",
		BinOpTy::NotEq => "!=",
		BinOpTy::AndAnd => "&&",
		BinOpTy::OrOr => "||",
		BinOpTy::XorXor => "^^",
		BinOpTy::Gt => ">",
		BinOpTy::Lt => "<",
		BinOpTy::Ge => ">=",
		BinOpTy::Le => "<=",
	})
	.to_owned()
}

fn print_type_handle<'a>(
	ctx: &PrintCtx<'a>,
	handle: &Either<Primitive, super::StructHandle>,
) -> &'a str {
	let primitive = match handle {
		Either::Left(p) => p,
		Either::Right(handle) => {
			return &ctx.structs[handle.0].name;
		}
	};
	match primitive {
		Primitive::Void => "void",
		Primitive::Bool => "bool",
		Primitive::Int => "int",
		Primitive::Uint => "uint",
		Primitive::Float => "float",
		Primitive::Double => "double",
		Primitive::Vec2 => "vec2",
		Primitive::Vec3 => "vec3",
		Primitive::Vec4 => "vec4",
		Primitive::BVec2 => "bvec2",
		Primitive::BVec3 => "bvec3",
		Primitive::BVec4 => "bvec4",
		Primitive::IVec2 => "ivec2",
		Primitive::IVec3 => "ivec3",
		Primitive::IVec4 => "ivec4",
		Primitive::UVec2 => "uvec2",
		Primitive::UVec3 => "uvec3",
		Primitive::UVec4 => "uvec4",
		Primitive::DVec2 => "dvec2",
		Primitive::DVec3 => "dvec3",
		Primitive::DVec4 => "dvec4",
		Primitive::Mat2x2 => "mat2",
		Primitive::Mat2x2 => "mat2x2",
		Primitive::Mat2x3 => "mat2x3",
		Primitive::Mat2x4 => "mat2x4",
		Primitive::Mat3x2 => "mat3x2",
		Primitive::Mat3x3 => "mat3",
		Primitive::Mat3x3 => "mat3x3",
		Primitive::Mat3x4 => "mat3x4",
		Primitive::Mat4x2 => "mat4x2",
		Primitive::Mat4x3 => "mat4x3",
		Primitive::Mat4x4 => "mat4",
		Primitive::Mat4x4 => "mat4x4",
		Primitive::DMat2x2 => "dmat2",
		Primitive::DMat2x2 => "dmat2x2",
		Primitive::DMat2x3 => "dmat2x3",
		Primitive::DMat2x4 => "dmat2x4",
		Primitive::DMat3x2 => "dmat3x2",
		Primitive::DMat3x3 => "dmat3",
		Primitive::DMat3x3 => "dmat3x3",
		Primitive::DMat3x4 => "dmat3x4",
		Primitive::DMat4x2 => "dmat4x2",
		Primitive::DMat4x3 => "dmat4x3",
		Primitive::DMat4x4 => "dmat4",
		Primitive::DMat4x4 => "dmat4x4",
		Primitive::Sampler1d => "sampler1D",
		Primitive::Sampler2d => "sampler2D",
		Primitive::Sampler3d => "sampler3D",
		Primitive::SamplerCube => "samplerCube",
		Primitive::Sampler2dRect => "sampler2DRect",
		Primitive::Sampler1dArray => "sampler1DArray",
		Primitive::Sampler2dArray => "sampler2DArray",
		Primitive::SamplerCubeArray => "samplerCubeArray",
		Primitive::SamplerBuffer => "samplerBuffer",
		Primitive::Sampler2dms => "sampler2DMS",
		Primitive::Sampler2dmsArray => "sampler2DMSArray",
		Primitive::ISampler1d => "isampler1D",
		Primitive::ISampler2d => "isampler2D",
		Primitive::ISampler3d => "isampler3D",
		Primitive::ISamplerCube => "isamplerCube",
		Primitive::ISampler2dRect => "isampler2DRect",
		Primitive::ISampler1dArray => "isampler1DArray",
		Primitive::ISampler2dArray => "isampler2DArray",
		Primitive::ISamplerCubeArray => "isamplerCubeArray",
		Primitive::ISamplerBuffer => "isamplerBuffer",
		Primitive::ISampler2dms => "isampler2DMS",
		Primitive::ISampler2dmsArray => "isampler2DMSArray",
		Primitive::USampler1d => "usampler1D",
		Primitive::USampler2d => "usampler2D",
		Primitive::USampler3d => "usampler3D",
		Primitive::USamplerCube => "usamplerCube",
		Primitive::USampler2dRect => "usampler2DRect",
		Primitive::USampler1dArray => "usampler1DArray",
		Primitive::USampler2dArray => "usampler2DArray",
		Primitive::USamplerCubeArray => "usamplerCubeArray",
		Primitive::USamplerBuffer => "usamplerBuffer",
		Primitive::USampler2dms => "usampler2DMS",
		Primitive::USampler2dmsArray => "usampler2DMSArray",
		Primitive::Sampler1dShadow => "sampler1DShadow",
		Primitive::Sampler2dShadow => "sampler2DShadow",
		Primitive::SamplerCubeShadow => "samplerCubeShadow",
		Primitive::Sampler2dRectShadow => "sampler2DRectShadow",
		Primitive::Sampler1dArrayShadow => "sampler1DArrayShadow",
		Primitive::Sampler2dArrayShadow => "sampler2DArrayShadow",
		Primitive::SamplerCubeArrayShadow => "samplerCubeArrayShadow",
		Primitive::Image1d => "image1D",
		Primitive::Image2d => "image2D",
		Primitive::Image3d => "image3D",
		Primitive::ImageCube => "imageCube",
		Primitive::Image2dRect => "image2DRect",
		Primitive::Image1dArray => "image1DArray",
		Primitive::Image2dArray => "image2DArray",
		Primitive::ImageCubeArray => "imageCubeArray",
		Primitive::ImageBuffer => "imageBuffer",
		Primitive::Image2dms => "image2DMS",
		Primitive::Image2dmsArray => "image2DMSArray",
		Primitive::IImage1d => "iimage1D",
		Primitive::IImage2d => "iimage2D",
		Primitive::IImage3d => "iimage3D",
		Primitive::IImageCube => "iimageCube",
		Primitive::IImage2dRect => "iimage2DRect",
		Primitive::IImage1dArray => "iimage1DArray",
		Primitive::IImage2dArray => "iimage2DArray",
		Primitive::IImageCubeArray => "iimageCubeArray",
		Primitive::IImageBuffer => "iimageBuffer",
		Primitive::IImage2dms => "iimage2DMS",
		Primitive::IImage2dmsArray => "iimage2DMSArray",
		Primitive::UImage1d => "uimage1D",
		Primitive::UImage2d => "uimage2D",
		Primitive::UImage3d => "uimage3D",
		Primitive::UImageCube => "uimageCube",
		Primitive::UImage2dRect => "uimage2DRect",
		Primitive::UImage1dArray => "uimage1DArray",
		Primitive::UImage2dArray => "uimage2DArray",
		Primitive::UImageCubeArray => "uimageCubeArray",
		Primitive::UImageBuffer => "uimageBuffer",
		Primitive::UImage2dms => "uimage2DMS",
		Primitive::UImage2dmsArray => "uimage2DMSArray",
		Primitive::AtomicUint => "atomic_uint",
	}
}

fn print_qualifiers<'a>(
	w: &mut Writer,
	ctx: &PrintCtx<'a>,
	qualifiers: &[Qualifier],
) {
	w.indent();
	for qualifier in qualifiers {
		if let QualifierTy::Layout(layouts) = &qualifier.ty {
			new_line_whole!(w, "layout: [");
			w.indent();
			for layout in layouts {
				match &layout.ty {
					LayoutTy::Shared => new_line_whole!(w, "shared"),
					LayoutTy::Packed => new_line_whole!(w, "packed"),
					LayoutTy::Std140 => new_line_whole!(w, "std140"),
					LayoutTy::Std430 => new_line_whole!(w, "std430"),
					LayoutTy::RowMajor => new_line_whole!(w, "row major"),
					LayoutTy::ColumnMajor => new_line_whole!(w, "column major"),
					LayoutTy::Binding(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "binding: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "binding");
						}
					}
					LayoutTy::Offset(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "offset: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "offset");
						}
					}
					LayoutTy::Align(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "align: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "align");
						}
					}
					LayoutTy::Location(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "location: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "location");
						}
					}
					LayoutTy::Component(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "component: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "component");
						}
					}
					LayoutTy::Index(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "index: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "index");
						}
					}
					LayoutTy::Points => new_line_whole!(w, "points"),
					LayoutTy::Lines => new_line_whole!(w, "lines"),
					LayoutTy::Isolines => new_line_whole!(w, "isolines"),
					LayoutTy::Triangles => new_line_whole!(w, "triangles"),
					LayoutTy::Quads => new_line_whole!(w, "quads"),
					LayoutTy::EqualSpacing => {
						new_line_whole!(w, "equal spacing")
					}
					LayoutTy::FractionalEvenSpacing => {
						new_line_whole!(w, "fractional even spacing")
					}
					LayoutTy::FractionalOddSpacing => {
						new_line_whole!(w, "fractional odd spacing")
					}
					LayoutTy::Clockwise => new_line_whole!(w, "clockwise"),
					LayoutTy::CounterClockwise => {
						new_line_whole!(w, "counter clockwise")
					}
					LayoutTy::PointMode => new_line_whole!(w, "point mode"),
					LayoutTy::LineAdjacency => {
						new_line_whole!(w, "line adjacency")
					}
					LayoutTy::TriangleAdjacency => {
						new_line_whole!(w, "triangle adjacency")
					}
					LayoutTy::Invocations(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "invocations: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "invocations");
						}
					}
					LayoutTy::OriginUpperLeft => {
						new_line_whole!(w, "origin upper left")
					}
					LayoutTy::PixelCenterInteger => {
						new_line_whole!(w, "pixel center integer")
					}
					LayoutTy::EarlyFragmentTests => {
						new_line_whole!(w, "early fragment tests")
					}
					LayoutTy::LocalSizeX(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "local size x: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "local size x");
						}
					}
					LayoutTy::LocalSizeY(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "local size y: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "local size y");
						}
					}
					LayoutTy::LocalSizeZ(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "local size z: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "local size z");
						}
					}
					LayoutTy::XfbBuffer(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfb buffer: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "xfb buffer");
						}
					}
					LayoutTy::XfbStride(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfv stride: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "xfv stride");
						}
					}
					LayoutTy::XfbOffset(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfb offset: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "xfb offset");
						}
					}
					LayoutTy::Vertices(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "vertices: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "vertices");
						}
					}
					LayoutTy::LineStrip => new_line_whole!(w, "line strip"),
					LayoutTy::TriangleStrip => {
						new_line_whole!(w, "triangle strip")
					}
					LayoutTy::MaxVertices(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "max vertices: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "max vertices");
						}
					}
					LayoutTy::Stream(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "stream: ");
							new_line_part!(w);
							print_expr(w, ctx, expr);
						} else {
							new_line_whole!(w, "stream");
						}
					}
					LayoutTy::DepthAny => new_line_whole!(w, "depth any"),
					LayoutTy::DepthGreater => {
						new_line_whole!(w, "depth greater")
					}
					LayoutTy::DepthLess => new_line_whole!(w, "depth less"),
					LayoutTy::DepthUnchanged => {
						new_line_whole!(w, "depth unchanged")
					}
				};
			}
			w.de_indent();
			new_line_whole!(w, "]");
			continue;
		}
		new_line_whole!(
			w,
			"{}",
			match qualifier.ty {
				QualifierTy::Const => "const",
				QualifierTy::In => "in",
				QualifierTy::Out => "out",
				QualifierTy::InOut => "inout",
				QualifierTy::Attribute => "attribute",
				QualifierTy::Uniform => "uniform",
				QualifierTy::Varying => "varying",
				QualifierTy::Buffer => "buffer",
				QualifierTy::Shared => "shared",
				QualifierTy::Centroid => "centroid",
				QualifierTy::Sample => "sample",
				QualifierTy::Patch => "patch",
				QualifierTy::Layout(_) => unreachable!(),
				QualifierTy::Flat => "flat",
				QualifierTy::Smooth => "smooth",
				QualifierTy::NoPerspective => "noperspective",
				QualifierTy::HighP => "highp",
				QualifierTy::MediumP => "mediump",
				QualifierTy::LowP => "lowp",
				QualifierTy::Invariant => "invariant",
				QualifierTy::Precise => "precise",
				QualifierTy::Coherent => "coherent",
				QualifierTy::Volatile => "volatile",
				QualifierTy::Restrict => "restrict",
				QualifierTy::Readonly => "readonly",
				QualifierTy::Writeonly => "writeonly",
			}
		);
	}
	w.de_indent();
}
