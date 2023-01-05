//! Functionality for pretty-printing the abstract syntax tree.

use super::ast::*;
use crate::Either;
use std::fmt::Write;

pub(super) fn print_ast(ast: &[Node]) -> String {
	let mut writer = Writer {
		buffer: String::with_capacity(1_000),
		indent: 0,
	};
	for node in ast {
		write!(
			writer.buffer,
			"{:indent$}",
			"",
			indent = writer.indent * INDENT
		)
		.unwrap();
		print_node(&mut writer, node);
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

fn print_node(w: &mut Writer, node: &Node) {
	match &node.ty {
		NodeTy::Empty => continue_eol!(w, "Empty"),
		NodeTy::Expr(expr) => {
			continue_eol!(w, "Expr(");
			w.indent();
			new_line_part!(w);
			print_expr(w, expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Block(body) => {
			continue_eol!(w, "Block(");
			print_scope(w, body);
			new_line_whole!(w, ")");
		}
		NodeTy::VarDef { type_, ident } => {
			continue_eol!(w, "VarDef(");
			w.indent();
			new_line_part!(w, "type: ");
			print_type(w, type_);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::VarDefs(v) => {
			continue_eol!(w, "VarDef(");
			w.indent();
			for (type_, ident) in v {
				new_line_whole!(w, "(");
				w.indent();
				new_line_part!(w, "type: ");
				print_type(w, type_);
				new_line_whole!(w, "ident: {}", print_ident(ident));
				w.de_indent();
				new_line_whole!(w, ")");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::VarDefInit {
			type_,
			ident,
			value,
		} => {
			continue_eol!(w, "VarDef(");
			w.indent();
			new_line_part!(w, "type: ");
			print_type(w, type_);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			if let Some(value) = value {
				new_line_part!(w, "value: ");
				print_expr(w, value);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::VarDefInits(v, value) => {
			continue_eol!(w, "VarDef(");
			w.indent();
			for (type_, ident) in v {
				new_line_whole!(w, "(");
				w.indent();
				new_line_part!(w, "type: ");
				print_type(w, type_);
				new_line_whole!(w, "ident: {}", print_ident(ident));
				w.de_indent();
				new_line_whole!(w, ")");
			}
			if let Some(value) = value {
				new_line_part!(w, "value: ");
				print_expr(w, value);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::InterfaceDef {
			qualifiers,
			ident,
			body,
			instance,
		} => {
			continue_eol!(w, "InterfaceDef(");
			w.indent();
			if !qualifiers.is_empty() {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(ident));
			new_line_whole!(w, "body: [");
			print_scope(w, body);
			new_line_whole!(w, "]");
			if let Omittable::Some(instance) = instance {
				new_line_part!(w, "instance: ");
				print_expr(w, instance);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::Qualifiers(qualifiers) => {
			continue_eol!(w, "Qualifiers: [");
			print_qualifiers(w, qualifiers);
			new_line_whole!(w, "]");
		}
		NodeTy::FnDecl {
			return_type,
			ident,
			params,
		} => {
			continue_eol!(w, "FnDecl(");
			w.indent();
			new_line_part!(w, "return type: ");
			print_type(w, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, params);
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
			print_type(w, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, params);
			new_line_whole!(w, "body: Scope(");
			print_scope(w, body);
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
			print_type(w, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, params);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineFnDef {
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
			for ident in associations {
				new_line_whole!(w, "{}", print_ident(ident));
			}
			w.de_indent();
			new_line_whole!(w, "]");
			new_line_part!(w, "return type: ");
			print_type(w, return_type);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			print_params(w, params);
			if let Some(body) = body {
				new_line_whole!(w, "body: Scope(");
				print_scope(w, body);
				new_line_whole!(w, ")");
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::SubroutineUniformDef { type_, ident } => {
			continue_eol!(w, "SubroutineUniformDef(");
			w.indent();
			new_line_part!(w, "type: ");
			print_type(w, type_);
			new_line_whole!(w, "ident: {}", print_ident(ident));
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::StructDecl { qualifiers, ident } => {
			continue_eol!(w, "StructDecl(");
			w.indent();
			if !qualifiers.is_empty() {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(ident));
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::StructDef {
			qualifiers,
			ident,
			body,
			instance,
		} => {
			continue_eol!(w, "StructDef(");
			w.indent();
			if !qualifiers.is_empty() {
				new_line_whole!(w, "qualifiers: [");
				print_qualifiers(w, qualifiers);
				new_line_whole!(w, "]");
			}
			new_line_whole!(w, "name: {}", print_ident(ident));
			new_line_whole!(w, "body: [");
			print_scope(w, body);
			new_line_whole!(w, "]");
			if let Omittable::Some(instance) = instance {
				new_line_whole!(w, "instance: {}", print_ident(instance));
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
							print_expr(w, &cond);
						}
						if let Some(ref body) = branch.body {
							new_line_whole!(w, "body: Scope(");
							print_scope(w, &body);
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
							print_expr(w, &cond);
						}
						if let Some(ref body) = branch.body {
							new_line_whole!(w, "body: Scope(");
							print_scope(w, &body);
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
							print_scope(w, &body);
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
				print_expr(w, cond);
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
							print_expr(w, &expr);
						}
						new_line_whole!(w, "body: Scope(");
						if let Some(ref body) = case.body {
							print_scope(w, &body);
						}
						new_line_whole!(w, ")");
						w.de_indent();
						new_line_whole!(w, ")");
					}
					Either::Right(_) => {
						new_line_whole!(w, "default: Scope(");
						if let Some(ref body) = case.body {
							print_scope(w, &body);
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
			if let Some(init) = init {
				new_line_part!(w, "init: ");
				print_node(w, &init);
			}
			if let Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_node(w, &cond);
			}
			if let Some(inc) = inc {
				new_line_part!(w, "inc: ");
				print_node(w, &inc);
			}
			if let Some(body) = body {
				new_line_whole!(w, "body: Scope(");
				print_scope(w, body);
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
				print_expr(w, cond);
			}
			new_line_whole!(w, "body: Scope(");
			print_scope(w, body);
			new_line_whole!(w, ")");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		NodeTy::DoWhile { body, cond } => {
			continue_eol!(w, "Do-While(");
			w.indent();
			new_line_whole!(w, "body: Scope(");
			print_scope(w, body);
			new_line_whole!(w, ")");
			if let Some(cond) = cond {
				new_line_part!(w, "cond: ");
				print_expr(w, cond);
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
				print_expr(w, value);
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

fn print_scope(w: &mut Writer, scope: &Scope) {
	w.indent();
	for node in scope.contents.iter() {
		new_line_part!(w);
		print_node(w, node);
	}
	w.de_indent();
}

fn print_params(w: &mut Writer, params: &[Param]) {
	new_line_whole!(w, "params: [");
	w.indent();
	for param in params {
		new_line_whole!(w, "(");
		w.indent();
		new_line_part!(w, "type: ");
		print_type(w, &param.type_);
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

fn print_expr(w: &mut Writer, expr: &Expr) {
	match &expr.ty {
		ExprTy::Lit(l) => match l {
			Lit::Bool(b) => continue_eol!(w, "{b}"),
			Lit::Int(i) => continue_eol!(w, "{i}"),
			Lit::UInt(u) => continue_eol!(w, "{u}"),
			Lit::Float(f) => continue_eol!(w, "{f}"),
			Lit::Double(d) => continue_eol!(w, "{d}"),
			Lit::InvalidNum => continue_eol!(w, "{{invalid_num}}"),
		},
		ExprTy::Ident(i) => continue_eol!(w, "{}", i.name),
		ExprTy::Prefix { op, expr } => {
			continue_eol!(w, "Pre(");
			w.indent();
			new_line_whole!(w, "op: {}", print_pre_op(op));
			if let Some(expr) = expr {
				new_line_part!(w);
				print_expr(w, &expr);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Postfix { expr, op } => {
			continue_eol!(w, "Post(");
			w.indent();
			new_line_whole!(w, "op: {}", print_post_op(op));
			new_line_part!(w);
			print_expr(w, &expr);
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Binary { left, op, right } => {
			continue_eol!(w, "Bin(");
			w.indent();
			new_line_whole!(w, "op: {}", print_bin_op(op));
			new_line_part!(w, "left: ");
			print_expr(w, &left);
			if let Some(right) = right {
				new_line_part!(w, "right: ");
				print_expr(w, &right);
			}
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
			print_expr(w, &cond);
			if let Some(true_) = true_ {
				new_line_part!(w, "true: ");
				print_expr(w, &true_);
			}
			if let Some(false_) = false_ {
				new_line_part!(w, "false: ");
				print_expr(w, &false_);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Parens { expr } => {
			continue_eol!(w, "Paren(");
			w.indent();
			if let Some(expr) = expr {
				new_line_part!(w);
				print_expr(w, &expr);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::ObjAccess { obj, leaf } => {
			continue_eol!(w, "DotAccess(");
			w.indent();
			new_line_part!(w, "obj: ");
			print_expr(w, &obj);
			if let Some(leaf) = leaf {
				new_line_part!(w, "leaf: ");
				print_expr(w, &leaf);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::Index { item, i } => {
			continue_eol!(w, "Index(");
			w.indent();
			new_line_part!(w, "item: ");
			print_expr(w, &item);
			if let Some(i) = i {
				new_line_part!(w, "i: ");
				print_expr(w, &i);
			}
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::FnCall { ident, args } => {
			continue_eol!(w, "Fn(");
			w.indent();
			new_line_whole!(w, "ident: {}", print_ident(ident));
			new_line_whole!(w, "params: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, arg);
			}
			w.de_indent();
			new_line_whole!(w, "]");
			w.de_indent();
			new_line_whole!(w, ")");
		}
		ExprTy::InitList { args } => {
			continue_eol!(w, "Initializer([");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, arg);
			}
			w.de_indent();
			new_line_whole!(w, "])");
		}
		ExprTy::ArrConstructor { arr, args } => {
			continue_eol!(w, "ArrayConstructor(");
			w.indent();
			new_line_part!(w, "type: ");
			print_expr(w, &arr);
			new_line_whole!(w, "params: [");
			w.indent();
			for arg in args {
				new_line_part!(w);
				print_expr(w, arg);
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
				print_expr(w, item);
			}
			w.de_indent();
			new_line_whole!(w, "])");
		}
		ExprTy::Separator => {}
	}
}

fn print_type(w: &mut Writer, type_: &Type) {
	match &type_.ty {
		TypeTy::Single(p) => continue_eol!(w, "{}", print_primitive(p)),
		TypeTy::Array(p, a) => {
			continue_eol!(w, "{}", print_primitive(p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		TypeTy::Array2D(p, a, b) => {
			continue_eol!(w, "{}", print_primitive(p));
			w.indent();
			if let Omittable::Some(expr) = a {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			if let Omittable::Some(expr) = b {
				new_line_whole!(w, "[");
				w.indent();
				new_line_part!(w);
				print_expr(w, &expr);
				w.de_indent();
				new_line_whole!(w, "]");
			}
			w.de_indent();
		}
		TypeTy::ArrayND(p, v) => {
			continue_eol!(w, "{}", print_primitive(p));
			w.indent();
			for i in v {
				if let Omittable::Some(expr) = i {
					new_line_part!(w, "[");
					w.indent();
					new_line_part!(w);
					print_expr(w, &expr);
					w.de_indent();
					new_line_whole!(w, "]");
				}
			}
			w.de_indent();
		}
	}
	if !type_.qualifiers.is_empty() {
		new_line_whole!(w, "+ qualifiers: [");
		print_qualifiers(w, &type_.qualifiers);
		new_line_whole!(w, "]");
	}
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

fn print_primitive(primitive: &Primitive) -> &str {
	if let Primitive::Struct(ident) = primitive {
		return &ident.name;
	}

	match primitive {
		Primitive::Scalar(Fundamental::Void) => "void",
		Primitive::Scalar(Fundamental::Bool) => "bool",
		Primitive::Scalar(Fundamental::Int) => "int",
		Primitive::Scalar(Fundamental::UInt) => "uint",
		Primitive::Scalar(Fundamental::Float) => "float",
		Primitive::Scalar(Fundamental::Double) => "double",
		Primitive::Vector(Fundamental::Float, 2) => "vec2",
		Primitive::Vector(Fundamental::Float, 3) => "vec3",
		Primitive::Vector(Fundamental::Float, 4) => "vec4",
		Primitive::Vector(Fundamental::Bool, 2) => "bvec2",
		Primitive::Vector(Fundamental::Bool, 3) => "bvec3",
		Primitive::Vector(Fundamental::Bool, 4) => "bvec4",
		Primitive::Vector(Fundamental::Int, 2) => "ivec2",
		Primitive::Vector(Fundamental::Int, 3) => "ivec3",
		Primitive::Vector(Fundamental::Int, 4) => "ivec4",
		Primitive::Vector(Fundamental::UInt, 2) => "uvec2",
		Primitive::Vector(Fundamental::UInt, 3) => "uvec3",
		Primitive::Vector(Fundamental::UInt, 4) => "uvec4",
		Primitive::Vector(Fundamental::Double, 2) => "dvec2",
		Primitive::Vector(Fundamental::Double, 3) => "dvec3",
		Primitive::Vector(Fundamental::Double, 4) => "dvec4",
		Primitive::Matrix(2, 2) => "mat2x2",
		Primitive::Matrix(2, 3) => "mat2x3",
		Primitive::Matrix(2, 4) => "mat2x4",
		Primitive::Matrix(3, 2) => "mat3x2",
		Primitive::Matrix(3, 3) => "mat3x3",
		Primitive::Matrix(3, 4) => "mat3x4",
		Primitive::Matrix(4, 2) => "mat4x2",
		Primitive::Matrix(4, 3) => "mat4x3",
		Primitive::Matrix(4, 4) => "mat4x4",
		Primitive::DMatrix(2, 2) => "dmat2x2",
		Primitive::DMatrix(2, 3) => "dmat2x3",
		Primitive::DMatrix(2, 4) => "dmat2x4",
		Primitive::DMatrix(3, 2) => "dmat3x2",
		Primitive::DMatrix(3, 3) => "dmat3x3",
		Primitive::DMatrix(3, 4) => "dmat3x4",
		Primitive::DMatrix(4, 2) => "dmat4x2",
		Primitive::DMatrix(4, 3) => "dmat4x3",
		Primitive::DMatrix(4, 4) => "dmat4x4",
		Primitive::Sampler(Fundamental::Float, TexType::D1) => "sampler1D",
		Primitive::Sampler(Fundamental::Float, TexType::D2) => "sampler2D",
		Primitive::Sampler(Fundamental::Float, TexType::D3) => "sampler3D",
		Primitive::Sampler(Fundamental::Float, TexType::Cube) => "samplerCube",
		Primitive::Sampler(Fundamental::Float, TexType::D2Rect) => {
			"sampler2DRect"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D1Array) => {
			"sampler1DArray"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2Array) => {
			"sampler2DArray"
		}
		Primitive::Sampler(Fundamental::Float, TexType::CubeArray) => {
			"samplerCubeArray"
		}
		Primitive::Sampler(Fundamental::Float, TexType::Buffer) => {
			"samplerBuffer"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2Multisample) => {
			"sampler2DMS"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2MultisampleArray) => {
			"sampler2DMSArray"
		}
		Primitive::Sampler(Fundamental::Int, TexType::D1) => "isampler1D",
		Primitive::Sampler(Fundamental::Int, TexType::D2) => "isampler2D",
		Primitive::Sampler(Fundamental::Int, TexType::D3) => "isampler3D",
		Primitive::Sampler(Fundamental::Int, TexType::Cube) => "isamplerCube",
		Primitive::Sampler(Fundamental::Int, TexType::D2Rect) => {
			"isampler2DRect"
		}
		Primitive::Sampler(Fundamental::Int, TexType::D1Array) => {
			"isampler1DArray"
		}
		Primitive::Sampler(Fundamental::Int, TexType::D2Array) => {
			"isampler2DArray"
		}
		Primitive::Sampler(Fundamental::Int, TexType::CubeArray) => {
			"isamplerCubeArray"
		}
		Primitive::Sampler(Fundamental::Int, TexType::Buffer) => {
			"isamplerBuffer"
		}
		Primitive::Sampler(Fundamental::Int, TexType::D2Multisample) => {
			"isampler2DMS"
		}
		Primitive::Sampler(Fundamental::Int, TexType::D2MultisampleArray) => {
			"isampler2DMSArray"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::D1) => "usampler1D",
		Primitive::Sampler(Fundamental::UInt, TexType::D2) => "usampler2D",
		Primitive::Sampler(Fundamental::UInt, TexType::D3) => "usampler3D",
		Primitive::Sampler(Fundamental::UInt, TexType::Cube) => "usamplerCube",
		Primitive::Sampler(Fundamental::UInt, TexType::D2Rect) => {
			"usampler2DRect"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::D1Array) => {
			"usampler1DArray"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::D2Array) => {
			"usampler2DArray"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::CubeArray) => {
			"usamplerCubeArray"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::Buffer) => {
			"usamplerBuffer"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::D2Multisample) => {
			"usampler2DMS"
		}
		Primitive::Sampler(Fundamental::UInt, TexType::D2MultisampleArray) => {
			"usampler2DMSArray"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D1Shadow) => {
			"sampler1DShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2Shadow) => {
			"sampler2DShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::CubeShadow) => {
			"samplerCubeShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2RectShadow) => {
			"sampler2DRectShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D1ArrayShadow) => {
			"sampler1DArrayShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::D2ArrayShadow) => {
			"sampler2DArrayShadow"
		}
		Primitive::Sampler(Fundamental::Float, TexType::CubeArrayShadow) => {
			"samplerCubeArrayShadow"
		}
		Primitive::Image(Fundamental::Float, TexType::D1) => "image1D",
		Primitive::Image(Fundamental::Float, TexType::D2) => "image2D",
		Primitive::Image(Fundamental::Float, TexType::D3) => "image3D",
		Primitive::Image(Fundamental::Float, TexType::Cube) => "imageCube",
		Primitive::Image(Fundamental::Float, TexType::D2Rect) => "image2DRect",
		Primitive::Image(Fundamental::Float, TexType::D1Array) => {
			"image1DArray"
		}
		Primitive::Image(Fundamental::Float, TexType::D2Array) => {
			"image2DArray"
		}
		Primitive::Image(Fundamental::Float, TexType::CubeArray) => {
			"imageCubeArray"
		}
		Primitive::Image(Fundamental::Float, TexType::Buffer) => "imageBuffer",
		Primitive::Image(Fundamental::Float, TexType::D2Multisample) => {
			"image2DMS"
		}
		Primitive::Image(Fundamental::Float, TexType::D2MultisampleArray) => {
			"image2DMSArray"
		}
		Primitive::Image(Fundamental::Int, TexType::D1) => "iimage1D",
		Primitive::Image(Fundamental::Int, TexType::D2) => "iimage2D",
		Primitive::Image(Fundamental::Int, TexType::D3) => "iimage3D",
		Primitive::Image(Fundamental::Int, TexType::Cube) => "iimageCube",
		Primitive::Image(Fundamental::Int, TexType::D2Rect) => "iimage2DRect",
		Primitive::Image(Fundamental::Int, TexType::D1Array) => "iimage1DArray",
		Primitive::Image(Fundamental::Int, TexType::D2Array) => "iimage2DArray",
		Primitive::Image(Fundamental::Int, TexType::CubeArray) => {
			"iimageCubeArray"
		}
		Primitive::Image(Fundamental::Int, TexType::Buffer) => "iimageBuffer",
		Primitive::Image(Fundamental::Int, TexType::D2Multisample) => {
			"iimage2DMS"
		}
		Primitive::Image(Fundamental::Int, TexType::D2MultisampleArray) => {
			"iimage2DMSArray"
		}
		Primitive::Image(Fundamental::UInt, TexType::D1) => "uimage1D",
		Primitive::Image(Fundamental::UInt, TexType::D2) => "uimage2D",
		Primitive::Image(Fundamental::UInt, TexType::D3) => "uimage3D",
		Primitive::Image(Fundamental::UInt, TexType::Cube) => "uimageCube",
		Primitive::Image(Fundamental::UInt, TexType::D2Rect) => "uimage2DRect",
		Primitive::Image(Fundamental::UInt, TexType::D1Array) => {
			"uimage1DArray"
		}
		Primitive::Image(Fundamental::UInt, TexType::D2Array) => {
			"uimage2DArray"
		}

		Primitive::Image(Fundamental::UInt, TexType::CubeArray) => {
			"uimageCubeArray"
		}
		Primitive::Image(Fundamental::UInt, TexType::Buffer) => "uimageBuffer",
		Primitive::Image(Fundamental::UInt, TexType::D2Multisample) => {
			"uimage2DMS"
		}
		Primitive::Image(Fundamental::UInt, TexType::D2MultisampleArray) => {
			"uimage2DMSArray"
		}
		Primitive::Atomic => "atomic_uint",
		_ => unreachable!(),
	}
}

fn print_qualifiers(w: &mut Writer, qualifiers: &[Qualifier]) {
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
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "binding");
						}
					}
					LayoutTy::Offset(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "offset: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "offset");
						}
					}
					LayoutTy::Align(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "align: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "align");
						}
					}
					LayoutTy::Location(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "location: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "location");
						}
					}
					LayoutTy::Component(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "component: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "component");
						}
					}
					LayoutTy::Index(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "index: ");
							new_line_part!(w);
							print_expr(w, expr);
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
							print_expr(w, expr);
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
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "local size x");
						}
					}
					LayoutTy::LocalSizeY(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "local size y: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "local size y");
						}
					}
					LayoutTy::LocalSizeZ(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "local size z: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "local size z");
						}
					}
					LayoutTy::XfbBuffer(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfb buffer: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "xfb buffer");
						}
					}
					LayoutTy::XfbStride(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfv stride: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "xfv stride");
						}
					}
					LayoutTy::XfbOffset(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "xfb offset: ");
							new_line_part!(w);
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "xfb offset");
						}
					}
					LayoutTy::Vertices(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "vertices: ");
							new_line_part!(w);
							print_expr(w, expr);
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
							print_expr(w, expr);
						} else {
							new_line_whole!(w, "max vertices");
						}
					}
					LayoutTy::Stream(expr) => {
						if let Some(expr) = expr {
							new_line_whole!(w, "stream: ");
							new_line_part!(w);
							print_expr(w, expr);
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
