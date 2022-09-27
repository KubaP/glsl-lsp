//! Types and functionality related to the Concrete Syntax Tree.

mod parser;

use crate::{
	ast::ArrSize,
	error::SyntaxErr,
	span::Span,
	token::{NumType, Token},
	Either,
};

/// A concrete syntax tree; this vector represents the root of a GLSL source file.
pub type Cst = Vec<Node>;

/// Parses a string representing the GLSL source file into a Concrete Syntax Tree.
///
/// # Examples
/// Parse a simple GLSL expression:
/// ```rust
/// # use glast::cst::parse_from_str;
/// let src = r#"
/// int i = 5.0 + 1;
/// "#;
/// let (cst, syntax_errors) = parse_from_str(&src);
/// ```
pub fn parse_from_str(source: &str) -> (Cst, Vec<SyntaxErr>) {
	use self::parser::{parse_stmt, Walker};

	let token_stream = crate::token::parse_from_str(source);

	let mut walker = Walker {
		token_stream,
		cursor: 0,
	};
	let mut nodes = Vec::new();
	let mut errors = Vec::new();
	while walker.peek().is_some() {
		parse_stmt(&mut walker, &mut nodes, &mut errors);
	}

	(nodes, errors)
}

/// Parses a token stream into a Concrete Syntax Tree.
///
/// # Examples
/// Parse a simple GLSL expression, whilst performing some custom logic between the steps:
/// ```rust
/// # use glast::{cst, token};
/// let src = r#"
/// int i = 5.0 + 1;
/// "#;
/// let token_stream = token::parse_from_str(&src);
/// // .. do some logic
/// let (cst, syntax_errors) = cst::parse_from_token_stream(token_stream);
/// ```
pub fn parse_from_token_stream(
	stream: crate::token::TokenStream,
) -> (Cst, Vec<SyntaxErr>) {
	use self::parser::{parse_stmt, Walker};

	let mut walker = Walker {
		token_stream: stream,
		cursor: 0,
	};
	let mut nodes = Vec::new();
	let mut errors = Vec::new();
	while walker.peek().is_some() {
		parse_stmt(&mut walker, &mut nodes, &mut errors);
	}

	(nodes, errors)
}

/// Prints the concrete syntax tree.
///
/// This produces a formatted [`String`] which contains all of the information of the CST.
///
/// # Examples
/// Print the contents for debugging purposes:
/// ```rust
/// # use glast::cst::{parse_from_str, print_tree};
/// let src = r#"
/// int i = 5.0 + 1;
/// "#;
/// let (cst, syntax_errors) = parse_from_str(&src);
/// println!("{}", print_tree(&cst));
/// ```
/// would result in:
/// ```text
/// VAR_DECL@0..16
///     TYPE@0..3
///         IDENT@0..3 "int"
///     IDENT
///         IDENT@4..5 "i"
///     EQ@6..7
///     VALUE@8..15
///         BINARY@8..15
///             LIT_FLOAT@8..11 "5.0"
///             OP@12..13 "+"
///             LIT_INT@14..15 "1"
///     SEMI@15..16
/// ```
/// *Note that this string representation is not stable and can change at any time.*
pub fn print_tree(cst: &Cst) -> String {
	if let Some(last) = cst.last() {
		use std::fmt::Write;

		let mut buffer = String::with_capacity(10_000);
		let _ = write!(&mut buffer, "SOURCE_FILE@0..{}", last.span.end);
		for node in cst {
			let _ = parser::printing::print_tree_node(node, 1, &mut buffer);
		}

		buffer
	} else {
		"SOURCE_FILE@0..0".to_string()
	}
}

/// A collection of tokens (attempted to be) grouped into logical nodes. Nodes are either:
/// - valid statements in their entirety,
/// - statements with missing syntax which have been parsed with error recovery,
/// - individual tokens that could not be recovered into statements.
///
/// When it comes to error recovery, the approach taken is that of high likelyhood. If it is quite obvious that a
/// bit of syntax is missing from making a valid statement, it will be recovered and a statement will be produced,
/// with the relevant `Option<T>` field set to `None`. If however there is a lot of ambiguity what the
/// already-parsed tokens could construct, they are emitted as individual `NodeTy::FIXME` nodes.
#[derive(Debug, Clone, PartialEq)]
pub struct Node {
	pub ty: NodeTy,
	pub span: Span,
}

/// The following variants represent individual [`Token`]s or groups of tokens that were not parsed into a
/// statement:
/// - `Keyword`,
/// - `Punctuation`,
/// - `Ident`,
/// - `Directive`,
/// - `Invalid`,
/// - `Expression`,
/// - `DelimitedScope`.
///
/// All of the other variants represent either fully valid statements, or statements that have been created with
/// error recovery. In the case of missing tokens, the relevant `Option<Span>` field will be set to `None`, or the
/// relevant `Vec<T>` will be empty of expected nodes.
#[derive(Debug, Clone, PartialEq)]
pub enum NodeTy {
	Keyword,
	Punctuation,
	Ident,
	Directive,
	Invalid,
	ZeroWidth,
	Expression(Expr),
	DelimitedScope(Scope),
	/* STATEMENTS */
	/// An empty statement, i.e. just a `;`.
	EmptyStmt,
	/// A variable definition, e.g. `int a;`.
	VarDef {
		qualifiers: Vec<Qualifier>,
		type_: Expr,
		ident: Expr,
		semi: Option<Span>,
	},
	/// Multiple variable definitions, e.g. `int a, b;`.
	VarDefs {
		qualifiers: Vec<Qualifier>,
		type_: Expr,
		idents: Expr,
		semi: Option<Span>,
	},
	/// A variable declaration, e.g. `int a = 5 + 1;`.
	VarDecl {
		qualifiers: Vec<Qualifier>,
		type_: Expr,
		ident: Expr,
		eq: Option<Span>,
		value: Option<Expr>,
		semi: Option<Span>,
	},
	/// Multiple variable declarations, e.g. `int a, b = 5 + 1;`.
	VarDecls {
		qualifiers: Vec<Qualifier>,
		type_: Expr,
		idents: Expr,
		eq: Option<Span>,
		value: Option<Expr>,
		semi: Option<Span>,
	},
	/// A function definition.
	FnDef {
		qualifiers: Vec<Qualifier>,
		return_type: Expr,
		ident: Ident,
		l_paren: Span,
		params: List<Param>,
		r_paren: Option<Span>,
		semi: Option<Span>,
	},
	/// A function declaration.
	FnDecl {
		qualifiers: Vec<Qualifier>,
		return_type: Expr,
		ident: Ident,
		l_paren: Span,
		params: List<Param>,
		r_paren: Option<Span>,
		body: Scope,
	},
	/// A struct definition. *Note:* This is invalid glsl grammar.
	StructDef {
		qualifiers: Vec<Qualifier>,
		kw: Span,
		ident: Ident,
		semi: Span,
	},
	/// A struct declaration.
	StructDecl {
		qualifiers: Vec<Qualifier>,
		kw: Span,
		ident: Ident,
		body: Scope,
		/// Instance name can be omitted, so `None` is a valid value.
		instance: Option<Ident>,
		semi: Option<Span>,
	},
	/// A general expression, e.g.
	///
	/// - `i + 5;`
	/// - `fn();`
	/// - `i = 5 + 1;`
	/// - `i *= fn();`
	ExprStmt {
		expr: Expr,
		semi: Option<Span>,
	},
	/// A standalone scope, e.g.
	/// ```glsl
	/// /* .. */
	/// {
	/// 	/* new scope */
	/// }
	/// ```
	Scope(Scope),
	/// A preprocessor call.
	Preproc(Preproc),
	/// An if statement.
	If {
		branches: Vec<IfBranch>,
	},
	/// A switch statement.
	Switch {
		kw: Span,
		l_paren: Option<Span>,
		expr: Option<Nodes>,
		r_paren: Option<Span>,
		l_brace: Option<Span>,
		cases: Vec<SwitchBranch>,
		r_brace: Option<Span>,
	},
	/// A for-loop statement.
	For {
		kw: Span,
		l_paren: Option<Span>,
		nodes: Option<List<Nodes>>,
		r_paren: Option<Span>,
		body: Option<Scope>,
	},
	/// A while-loop, i.e. `while ( /*..*/ ) { /*..*/ }`.
	While {
		kw: Span,
		l_paren: Option<Span>,
		cond: Option<Nodes>,
		r_paren: Option<Span>,
		body: Option<Scope>,
	},
	/// A do-while loop, i.e. `do { /*..*/ } while ( /*..*/ );`.
	DoWhile {
		do_kw: Span,
		body: Option<Scope>,
		while_kw: Option<Span>,
		l_paren: Option<Span>,
		cond: Option<Nodes>,
		r_paren: Option<Span>,
		semi: Option<Span>,
	},
	/// A return statement.
	Return {
		kw: Span,
		value: Option<Expr>,
		semi: Option<Span>,
	},
	/// A break statement.
	Break {
		kw: Span,
		semi: Option<Span>,
	},
	/// A continue statement.
	Continue {
		kw: Span,
		semi: Option<Span>,
	},
	/// A discard statement.
	Discard {
		kw: Span,
		semi: Option<Span>,
	},
}

/// A symbol-seperated list of items of type `T`.
///
/// This struct stores entries; each entry consists of an optional `T` and of an optional separator [`Span`].
///
/// The following series of syntactical tokens:
/// ```text
/// T , T  T ,  ,
/// ```
/// would be constructed like so:
/// ```
/// # use glsl_parser::{cst::List, span::Span};
/// # let mut list = List::new();
/// # let t = 1;
/// # let comma_span = Span::new(0, 1);
/// list.push_item(t);
/// list.push_separator(comma_span);
/// list.push_item(t);
/// list.push_item(t);
/// list.push_separator(comma_span);
/// list.push_separator(comma_span);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct List<T> {
	/// Each entry consists of an optional item followed by an optional separator.
	entries: Vec<(Option<T>, Option<Span>)>,
}

/// A growable collection of [`Node`]s.
///
/// This is basically a wrapper around `Vec<Node>` with some helper functions to automatically keep track of spans.
/// This differs from [`Scope`] in that `Scope` represents a complete lexical scope of nodes. This is more of just
/// a collection, and is suited towards the parsing logic where nodes may need to be added later down the line.
#[derive(Debug, Clone, PartialEq)]
pub struct Nodes {
	pub inner: Vec<Node>,
	start: usize,
	end: usize,
}

/// A parameter in a function definition/declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
	pub qualifiers: Vec<Qualifier>,
	pub type_: Expr,
	/// Parameter name can be omitted, so `None` is a valid value.
	pub ident: Option<Expr>,
	pub span: Span,
}

/// The type of an if-statement branch. This also tracks the relevant keyword spans.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IfTy {
	If(Span),
	ElseIf(Span, Span),
	Else(Span),
}

/// An if-statement branch.
#[derive(Debug, Clone, PartialEq)]
pub struct IfBranch {
	pub ty: IfTy,
	pub l_paren: Option<Span>,
	pub cond: Option<Node>,
	pub r_paren: Option<Span>,
	pub body: Option<Scope>,
	pub span: Span,
}

/// A switch-statement branch.
#[derive(Debug, Clone, PartialEq)]
pub struct SwitchBranch {
	pub kw: Span,
	pub is_default: bool,
	pub expr: Option<Nodes>,
	pub colon: Option<Span>,
	pub body: Option<Scope>,
	pub span: Span,
}

/// A scope of nodes, potentially delimited by opening and closing delimiters.
///
/// - If this represents a general scope, it would be delimited by `{` and `}`.
/// - If this represents a switch-case body, it would be delimited by `:` and `case`/`default`/`}`.
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
	/// The span of the opening delimiter if present.
	pub opening: Option<Span>,
	/// The inner nodes within this scope.
	pub inner: Vec<Node>,
	/// The span of the closing delimiter if present.
	pub closing: Option<Span>,
	/// The span of the entire scope. If the delimiters are present, this is from the beginning of the opening
	/// delimiter to the end of the closing delimiter. However, if one or both delimiters are missing, the span
	/// starts/ends at the start/end of the first/last node.
	pub span: Span,
}

/// A qualifier which is associated with a definition/declaration or a parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Qualifier {
	pub ty: QualifierTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum QualifierTy {
	Storage(Storage),
	Layout {
		kw: Span,
		l_paren: Option<Span>,
		idents: Option<List<Layout>>,
		r_paren: Option<Span>,
	},
	Interpolation(Interpolation),
	Precision(Precision),
	Invariant,
	Precise,
	Memory(Memory),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Storage {
	Const,
	In,
	Out,
	InOut,
	Attribute,
	Uniform,
	Varying,
	Buffer,
	Shared,
	Centroid,
	Sample,
	Patch,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Precision {
	HighP,
	MediumP,
	LowP,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Interpolation {
	Smooth,
	Flat,
	NoPerspective,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Memory {
	Coherent,
	Volatile,
	Restrict,
	Readonly,
	Writeonly,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Layout {
	pub ty: LayoutTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LayoutTy {
	Invalid,
	Shared,
	Packed,
	Std140,
	Std430,
	RowMajor,
	ColumnMajor,
	Binding {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Offset {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Align {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Location {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Component {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Index {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Points,
	Lines,
	Isolines,
	Triangles,
	Quads,
	EqualSpacing,
	FractionalEvenSpacing,
	FractionalOddSpacing,
	Clockwise,
	CounterClockwise,
	PointMode,
	LinesAdjacency,
	TrianglesAdjacency,
	Invocations {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	OriginUpperLeft,
	PixelCenterInteger,
	EarlyFragmentTests,
	LocalSizeX {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	LocalSizeY {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	LocalSizeZ {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	XfbBuffer {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	XfbStride {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	XfbOffset {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Vertices {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	LineStrip,
	TriangleStrip,
	MaxVertices {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	Stream {
		kw: Span,
		eq: Option<Span>,
		value: Option<Expr>,
	},
	DepthAny,
	DepthGreater,
	DepthLess,
	DepthUnchanged,
}

/// A preprocessor directive.
#[derive(Debug, Clone, PartialEq)]
pub enum Preproc {
	Version {
		version: usize,
		is_core: bool,
	},
	Extension {
		name: String,
		behaviour: ExtBehaviour,
	},
	Line {
		line: usize,
		src_str: Option<usize>,
	},
	Include(String),
	UnDef(String),
	IfDef(String),
	IfnDef(String),
	Else,
	EndIf,
	Error(String),
	Pragma(String),
	Unsupported,
}

/// The possible behaviours in an `#extension` directive.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExtBehaviour {
	Enable,
	Require,
	Warn,
	Disable,
}

impl<T> List<T> {
	/// Constructs a new `List`.
	pub fn new() -> Self {
		Self {
			entries: Vec::new(),
		}
	}

	/// Returns the number of elements in this `List`.
	pub fn len(&self) -> usize {
		self.entries.len()
	}

	/// Returns whether this `List` is empty.
	pub fn is_empty(&self) -> bool {
		self.entries.is_empty()
	}

	/// Appends an item `T` to the `List`.
	pub fn push_item(&mut self, item: T) {
		self.entries.push((Some(item), None));
	}

	/// Appends a separator to the `List`.
	pub fn push_separator(&mut self, span: Span) {
		if let Some(last) = self.entries.last_mut() {
			if last.1.is_none() {
				last.1 = Some(span);
				return;
			}
		}
		self.entries.push((None, Some(span)));
	}

	/// Wraps this `List` within an `Option<List`. If this list is empty, `None` will returned.
	pub fn wrap_in_option(self) -> Option<Self> {
		if self.entries.is_empty() {
			None
		} else {
			Some(self)
		}
	}

	/// Creates an iterator over the items **and** the separators in the `List`.
	///
	/// The iterator returns `Either<&T, &Span>` corresponding to `Either<Item, Separator span>`, in the order that
	/// they appear in.
	pub fn entry_iter(&self) -> ListEntryIterator<T> {
		ListEntryIterator {
			items: &&self.entries,
			cursor: 0,
			index: 0,
		}
	}

	/// Creates an iterator over the items in this `List`.
	pub fn item_iter(&self) -> ListItemIterator<T> {
		ListItemIterator {
			items: &self.entries,
			cursor: 0,
		}
	}
}

impl List<Expr> {
	pub fn analyze_syntax_errors_fn_arr_init(
		&self,
		syntax_errors: &mut Vec<SyntaxErr>,
		l_paren: Span,
	) {
		enum Prev {
			None,
			Item(Span),
			Comma(Span),
		}
		let mut previous = Prev::None;
		let mut cursor = 0;
		while let Some((item, comma)) = self.entries.get(cursor) {
			if let Some(item) = item {
				match previous {
					Prev::Item(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedCommaAfterArg(
							span.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Item(item.span);
			}

			if let Some(comma) = comma {
				match previous {
					Prev::Comma(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedArgAfterComma(
							span.next_single_width(),
						),
					),
					Prev::None => syntax_errors.push(
						SyntaxErr::ExprExpectedArgBetweenParenComma(
							l_paren.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Comma(*comma);
			}

			cursor += 1;
		}
		if let Prev::Comma(span) = previous {
			syntax_errors.push(SyntaxErr::ExprExpectedArgAfterComma(
				span.next_single_width(),
			));
		}
	}

	pub fn analyze_syntax_errors_init(
		&self,
		syntax_errors: &mut Vec<SyntaxErr>,
		l_brace: Span,
	) {
		enum Prev {
			None,
			Item(Span),
			Comma(Span),
		}
		let mut previous = Prev::None;
		let mut cursor = 0;
		while let Some((item, comma)) = self.entries.get(cursor) {
			if let Some(item) = item {
				match previous {
					Prev::Item(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedCommaAfterArg(
							span.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Item(item.span);
			}

			if let Some(comma) = comma {
				match previous {
					Prev::Comma(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedArgAfterComma(
							span.next_single_width(),
						),
					),
					Prev::None => syntax_errors.push(
						SyntaxErr::ExprExpectedArgBetweenBraceComma(
							l_brace.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Comma(*comma);
			}

			cursor += 1;
		}
		// We don't check for a trailing comma because that is legal in an initializer list.
	}

	pub fn analyze_syntax_errors_list(
		&self,
		syntax_errors: &mut Vec<SyntaxErr>,
	) {
		enum Prev {
			None,
			Item(Span),
			Comma(Span),
		}
		let mut previous = Prev::None;
		let mut cursor = 0;
		while let Some((item, comma)) = self.entries.get(cursor) {
			if let Some(item) = item {
				match previous {
					Prev::Item(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedExprAfterComma(
							span.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Item(item.span);
			}

			if let Some(comma) = comma {
				match previous {
					Prev::Comma(span) => syntax_errors.push(
						SyntaxErr::ExprExpectedExprAfterComma(
							span.next_single_width(),
						),
					),
					Prev::None => syntax_errors.push(
						SyntaxErr::ExprExpectedExprBeforeComma(
							comma.previous_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Comma(*comma);
			}

			cursor += 1;
		}
		if let Prev::Comma(span) = previous {
			syntax_errors.push(SyntaxErr::ExprExpectedExprAfterComma(
				span.next_single_width(),
			));
		}
	}
}

impl List<Param> {
	/// Returns the [`Span`] of the entire `List` if the list is not empty.
	pub fn span(&self) -> Option<Span> {
		if self.entries.is_empty() {
			return None;
		}

		let first = self.entries.first().unwrap();
		let start = if let Some(p) = &first.0 {
			p.span.start
		} else if let Some(s) = &first.1 {
			s.start
		} else {
			unreachable!("[List<Param>::span] `self.entries` first element has no item or separator.")
		};

		let last = self.entries.last().unwrap();
		let end = if let Some(s) = &last.1 {
			s.end
		} else if let Some(p) = &last.0 {
			p.span.end
		} else {
			unreachable!("[List<Param>::span] `self.entries` last element has no item or separator.")
		};

		Some(Span::new(start, end))
	}

	/// Converts this list of [`Param`]s into individual nodes. This is used in the scenario that the parsing of a
	/// function definition/declaration failed early.
	pub fn convert_into_failed_nodes(self, nodes: &mut Nodes) {
		for entry in self.entries {
			if let Some(Param {
				qualifiers,
				type_,
				ident,
				span: _,
			}) = entry.0
			{
				for Qualifier { span, .. } in qualifiers {
					nodes.push(Node {
						span,
						ty: NodeTy::Keyword,
					});
				}
				nodes.push(Node {
					span: type_.span,
					ty: NodeTy::Expression(type_),
				});
				if let Some(ident) = ident {
					nodes.push(Node {
						span: ident.span,
						ty: NodeTy::Ident,
					});
				}
			}
			if let Some(separator) = entry.1 {
				nodes.push(Node {
					span: separator,
					ty: NodeTy::Punctuation,
				});
			}
		}
	}

	pub fn analyze_syntax_errors(
		&self,
		syntax_errors: &mut Vec<SyntaxErr>,
		l_paren: Span,
	) {
		enum Prev {
			None,
			Item(Span),
			Comma(Span),
		}
		let mut previous = Prev::None;
		let mut cursor = 0;
		while let Some((item, comma)) = self.entries.get(cursor) {
			if let Some(item) = item {
				match previous {
					Prev::Item(span) => {
						syntax_errors.push(SyntaxErr::ExpectedCommaAfterParam(
							span.next_single_width(),
						))
					}
					_ => {}
				}

				previous = Prev::Item(item.span);
			}

			if let Some(comma) = comma {
				match previous {
					Prev::Comma(span) => {
						syntax_errors.push(SyntaxErr::ExpectedParamAfterComma(
							span.next_single_width(),
						))
					}
					Prev::None => syntax_errors.push(
						SyntaxErr::ExpectedParamBetweenParenComma(
							l_paren.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Comma(*comma);
			}

			cursor += 1;
		}
		if let Prev::Comma(span) = previous {
			syntax_errors.push(SyntaxErr::ExpectedParamAfterComma(
				span.next_single_width(),
			));
		}
	}
}

impl List<Layout> {
	/// Returns the [`Span`] of the entire `List` if the list is not empty.
	pub fn span(&self) -> Option<Span> {
		if self.entries.is_empty() {
			return None;
		}

		let first = self.entries.first().unwrap();
		let start = if let Some(l) = &first.0 {
			l.span.start
		} else if let Some(s) = &first.1 {
			s.start
		} else {
			unreachable!("[List<Layout>::span] `self.entries` first element has no item or separator.")
		};

		let last = self.entries.last().unwrap();
		let end = if let Some(s) = &last.1 {
			s.end
		} else if let Some(l) = &last.0 {
			l.span.end
		} else {
			unreachable!("[List<Layout>::span] `self.entries` last element has no item or separator.")
		};

		Some(Span::new(start, end))
	}

	/// Converts this list of [`Layout`]s into individual nodes. This is used in the scenario that the parsing
	/// result for a qualifier list has been unused because it forms invalid syntax.
	pub fn convert_into_failed_nodes(self, nodes: &mut Vec<Node>) {
		for entry in self.entries {
			if let Some(Layout { ty, span }) = entry.0 {
				match ty {
					LayoutTy::Invalid
					| LayoutTy::Shared
					| LayoutTy::Packed
					| LayoutTy::Std140
					| LayoutTy::Std430
					| LayoutTy::RowMajor
					| LayoutTy::ColumnMajor
					| LayoutTy::Points
					| LayoutTy::Lines
					| LayoutTy::Isolines
					| LayoutTy::Triangles
					| LayoutTy::Quads
					| LayoutTy::EqualSpacing
					| LayoutTy::FractionalEvenSpacing
					| LayoutTy::FractionalOddSpacing
					| LayoutTy::Clockwise
					| LayoutTy::CounterClockwise
					| LayoutTy::PointMode
					| LayoutTy::LinesAdjacency
					| LayoutTy::TrianglesAdjacency
					| LayoutTy::OriginUpperLeft
					| LayoutTy::PixelCenterInteger
					| LayoutTy::EarlyFragmentTests
					| LayoutTy::LineStrip
					| LayoutTy::TriangleStrip
					| LayoutTy::DepthAny
					| LayoutTy::DepthGreater
					| LayoutTy::DepthLess
					| LayoutTy::DepthUnchanged => nodes.push(Node {
						span,
						ty: NodeTy::Ident,
					}),
					LayoutTy::Binding { kw, eq, value }
					| LayoutTy::Offset { kw, eq, value }
					| LayoutTy::Align { kw, eq, value }
					| LayoutTy::Location { kw, eq, value }
					| LayoutTy::Component { kw, eq, value }
					| LayoutTy::Index { kw, eq, value }
					| LayoutTy::Invocations { kw, eq, value }
					| LayoutTy::LocalSizeX { kw, eq, value }
					| LayoutTy::LocalSizeY { kw, eq, value }
					| LayoutTy::LocalSizeZ { kw, eq, value }
					| LayoutTy::XfbBuffer { kw, eq, value }
					| LayoutTy::XfbStride { kw, eq, value }
					| LayoutTy::XfbOffset { kw, eq, value }
					| LayoutTy::Vertices { kw, eq, value }
					| LayoutTy::MaxVertices { kw, eq, value }
					| LayoutTy::Stream { kw, eq, value } => {
						nodes.push(Node {
							span: kw,
							ty: NodeTy::Ident,
						});
						if let Some(eq) = eq {
							nodes.push(Node {
								span: eq,
								ty: NodeTy::Punctuation,
							});
						}
						if let Some(value) = value {
							nodes.push(Node {
								span: value.span,
								ty: NodeTy::Expression(value),
							});
						}
					}
				}
			}
			if let Some(separator) = entry.1 {
				nodes.push(Node {
					span: separator,
					ty: NodeTy::Punctuation,
				});
			}
		}
	}

	pub fn analyze_syntax_errors(
		&self,
		syntax_errors: &mut Vec<SyntaxErr>,
		l_paren: Span,
	) {
		enum Prev {
			None,
			Item(Span),
			Comma(Span),
		}
		let mut previous = Prev::None;
		let mut cursor = 0;
		while let Some((item, comma)) = self.entries.get(cursor) {
			if let Some(item) = item {
				match previous {
					Prev::Item(span) => syntax_errors.push(
						SyntaxErr::ExpectedCommaAfterLayoutIdentOrExpr(
							span.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Item(item.span);
			}

			if let Some(comma) = comma {
				match previous {
					Prev::Comma(span) => syntax_errors.push(
						SyntaxErr::ExpectedLayoutIdentAfterComma(
							span.next_single_width(),
						),
					),
					Prev::None => syntax_errors.push(
						SyntaxErr::ExpectedLayoutIdentAfterParen(
							l_paren.next_single_width(),
						),
					),
					_ => {}
				}

				previous = Prev::Comma(*comma);
			}

			cursor += 1;
		}
		if let Prev::Comma(span) = previous {
			syntax_errors.push(SyntaxErr::ExpectedLayoutIdentAfterComma(
				span.next_single_width(),
			));
		} else if let Prev::None = previous {
			syntax_errors.push(SyntaxErr::ExpectedLayoutIdentAfterParen(
				l_paren.next_single_width(),
			));
		}
	}
}

impl List<Nodes> {
	/// Returns the [`Span`] of the entire `List` if the list is not empty.
	pub fn span(&self) -> Option<Span> {
		if self.entries.is_empty() {
			return None;
		}

		let first = self.entries.first().unwrap();
		let start = if let Some(n) = &first.0 {
			n.span().start
		} else if let Some(s) = &first.1 {
			s.start
		} else {
			unreachable!("[List<Layout>::span] `self.entries` first element has no item or separator.")
		};

		let last = self.entries.last().unwrap();
		let end = if let Some(s) = &last.1 {
			s.end
		} else if let Some(n) = &last.0 {
			n.span().end
		} else {
			unreachable!("[List<Layout>::span] `self.entries` last element has no item or separator.")
		};

		Some(Span::new(start, end))
	}
}

/// An iterator over the items `T` **and** separators of a [`List<T>`]. This iterator returns `Either<&T, &Span>`
/// corresponding to `Either<Item, Separator span>`.
///
/// This struct is created by the [`List::entry_iter()`](List::entry_iter) method.
pub struct ListEntryIterator<'a, T> {
	items: &'a [(Option<T>, Option<Span>)],
	cursor: usize,
	index: usize,
}

impl<'a, T> Iterator for ListEntryIterator<'a, T> {
	type Item = Either<&'a T, &'a Span>;

	fn next(&mut self) -> Option<Self::Item> {
		while let Some(t) = self.items.get(self.cursor) {
			if self.index == 0 {
				if let Some(t) = &t.0 {
					self.index = 1;
					return Some(Either::Left(t));
				}
			}

			self.cursor += 1;
			self.index = 0;

			if let Some(s) = &t.1 {
				return Some(Either::Right(s));
			}
		}
		None
	}
}

/// An iterator over the items `T` of a [`List<T>`].
///
/// This struct is created by the [`List::item_iter()`](List::item_iter) method.
pub struct ListItemIterator<'a, T> {
	items: &'a [(Option<T>, Option<Span>)],
	cursor: usize,
}

impl<'a, T> Iterator for ListItemIterator<'a, T> {
	type Item = &'a T;

	fn next(&mut self) -> Option<Self::Item> {
		while let Some(t) = self.items.get(self.cursor) {
			self.cursor += 1;

			if let Some(t) = &t.0 {
				return Some(t);
			}
		}
		None
	}
}

impl Nodes {
	/// Constructs an empty set of `Nodes`.
	pub fn new() -> Self {
		Self {
			inner: Vec::new(),
			start: 0,
			end: 0,
		}
	}

	/// Constructs a set of `Nodes` with the provided [`Node`].
	pub fn new_with(node: Node) -> Self {
		let start = node.span.start;
		let end = node.span.end;
		Self {
			inner: vec![node],
			start,
			end,
		}
	}

	/// Converts a [`Vec<Node>`] into a set of `Nodes`.
	pub fn from_vec(v: Vec<Node>) -> Self {
		let (start, end) = if !v.is_empty() {
			(v.first().unwrap().span.start, v.last().unwrap().span.end)
		} else {
			(0, 0)
		};
		Self {
			inner: v,
			start,
			end,
		}
	}

	/// Appends a [`Node`] to this set of `Nodes`.
	pub fn push(&mut self, node: Node) {
		// If this is the first node added, we need to set the `start` position for this collection.
		if self.inner.is_empty() {
			self.start = node.span.start;
		}

		self.end = node.span.end;
		self.inner.push(node);
	}

	/// Returns whether this set of `Nodes` is empty.
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}

	/// Returns the first [`Node`] from this set of `Nodes`, if there is one.
	pub fn first(&self) -> Option<&Node> {
		self.inner.first()
	}

	/// Returns the last [`Node`] from this set of `Nodes`, if there is one.
	pub fn last(&self) -> Option<&Node> {
		self.inner.last()
	}

	/// Returns the [`Span`] of this set of `Nodes`.
	pub fn span(&self) -> Span {
		Span::new(self.start, self.end)
	}
}

impl IfTy {
	/// Returns the [`Span`] of the keywords of this if-branch type.
	pub fn span(&self) -> Span {
		match self {
			Self::If(i) => *i,
			Self::ElseIf(e, i) => Span::new(e.start, i.end),
			Self::Else(e) => *e,
		}
	}
}

/// An expression, which is part of a larger statement.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
	pub ty: ExprTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprTy {
	/// A placeholder expression for one that is missing.
	///
	/// This token exists because when parsing, the entire expected expression, such as a while-loop condition, may
	/// be missing. We want to have better error recovery so we must be able to represent a missing expression. One
	/// way would be to make a bunch of `Expr` fields into `Option<Expr>`, but that seems needlessly verbose and
	/// would require nested matching, so hence we represent this "none" state in this enum through this variant.
	Missing,
	/// An expression which is incomplete, e.g. `3+5-`.
	///
	/// This token exists to allow the analyzer to gracefully deal with expression errors without affecting the
	/// ability to deal with surrounding expressions or statements. E.g.
	/// ```c
	/// int i = 3+5-;
	///
	/// // becomes
	///
	/// Expr::Binary {
	///     left: Expr::Lit(3),
	///     op: Add
	///     right: Expr::Incomplete
	/// }
	/// ```
	/// We can produce an error about the incomplete expression but still reason about the existence of `i`, such
	/// as in later uses. Obviously however, we cannot analyze whether the expression evaluates to a valid integer
	/// value.
	///
	/// This token is also used to represent unclosed delimiter groups, e.g.
	/// ```c
	/// fn(1+2
	///
	/// // or
	///
	/// i[0
	/// ```
	///
	/// Note: This token is not used for unclosed parenthesis groups, e.g.
	/// ```c
	/// (5+1
	///
	/// // becomes
	///
	/// Expr:: Binary {
	///     left: Expr::Lit(5),
	///     op: Add,
	///     right: Expr::Lit(1)
	/// }
	/// ```
	/// We produce an error about the missing parenthesis, but we can assume that the bracket group extends till
	/// the end. This is because whilst the position of the closing parenthesis may be unknown, no matter where it
	/// is placed it will not affect the analysis; either the types match or they don't. (It will affect the result
	/// of the evaluation but that is irrelevant to our analysis).
	Incomplete,
	/// A number token which could not be parsed as a valid number, e.g. `1.0B` cannot be converted to a valid
	/// `Lit` because `B` is not a valid numerical suffix.
	Invalid,
	Separator,
	/// A literal value; either a number or a boolean.
	Lit(Lit),
	/// An identifier; could be a variable name, function name, type name, etc.
	Ident(Ident),
	/// A prefix operation.
	Prefix {
		op: PreOp,
		expr: Option<Box<Expr>>,
	},
	/// A postfix operation.
	Postfix {
		expr: Box<Expr>,
		op: PostOp,
	},
	/// A binary expression with a left and right hand-side.
	Binary {
		left: Box<Expr>,
		op: BinOp,
		right: Option<Box<Expr>>,
	},
	/// A ternary condition.
	Ternary {
		cond: Box<Expr>,
		question: Span,
		true_: Option<Box<Expr>>,
		colon: Option<Span>,
		false_: Option<Box<Expr>>,
	},
	/// A parenthesis group.
	Paren {
		l_paren: Span,
		expr: Option<Box<Expr>>,
		r_paren: Option<Span>,
	},
	/// An index operator, e.g. `item[i]`.
	Index {
		item: Box<Expr>,
		l_bracket: Span,
		i: Option<Box<Expr>>,
		r_bracket: Option<Span>,
	},
	/// Object access.
	ObjAccess {
		obj: Box<Expr>,
		dot: Span,
		leaf: Option<Box<Expr>>,
	},
	/// A function call.
	Fn {
		ident: Ident,
		l_paren: Span,
		args: List<Expr>,
		r_paren: Option<Span>,
	},
	/// An initializer list.
	Init {
		l_brace: Span,
		args: List<Expr>,
		r_brace: Option<Span>,
	},
	/// An array constructor.
	ArrInit {
		/// Contains the first part of an array constructor, e.g. `int[3]`.
		arr: Box<Expr>,
		l_paren: Span,
		/// Contains the expressions within the brackets i.e. `..](a, b, ...)`.
		args: List<Expr>,
		r_paren: Option<Span>,
	},
	/// A general list expression, e.g. `a, b`.
	List(List<Expr>),
}

/// A binary operator.
#[derive(Debug, Clone, PartialEq)]
pub struct BinOp {
	pub ty: BinOpTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinOpTy {
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	And,
	Or,
	Xor,
	LShift,
	RShift,
	Eq,
	AddEq,
	SubEq,
	MulEq,
	DivEq,
	RemEq,
	AndEq,
	OrEq,
	XorEq,
	LShiftEq,
	RShiftEq,
	EqEq,
	NotEq,
	AndAnd,
	OrOr,
	XorXor,
	Gt,
	Lt,
	Ge,
	Le,
}

/// A prefix operator.
#[derive(Debug, Clone, PartialEq)]
pub struct PreOp {
	pub ty: PreOpTy,
	pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PreOpTy {
	Add,
	Sub,
	Neg,
	Flip,
	Not,
}

/// A postfix operator.
#[derive(Debug, Clone, PartialEq)]
pub struct PostOp {
	pub ty: PostOpTy,
	pub span: Span,
}
#[derive(Debug, Clone, PartialEq)]
pub enum PostOpTy {
	Add,
	Sub,
}

/// An identifier; this can be a variable name, function name, struct name, etc.
#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
	pub name: String,
	pub span: Span,
}

/// A literal value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Lit {
	Bool(bool),
	Int(i64),
	UInt(u64),
	Float(f32),
	Double(f64),
}

impl Expr {
	/// Tries to convert this `Expr` to variable definition/declaration identifiers, e.g. `my_num` or `a, b` or
	/// `c[1], p[3]`.
	///
	/// Each entry is either just an [`Ident`] if the expression is something like `my_num`, or it is an `Ident`
	/// plus one or more [`ArrSize`] if the expression is something like `a[1]` or `b[][3]`.
	pub fn to_var_def_decl_ident(
		&self,
	) -> Vec<Either<Ident, (Ident, Vec<ArrSize>)>> {
		let mut idents = Vec::new();

		match &self.ty {
			ExprTy::List(v) => {
				for expr in v.item_iter() {
					match Ident::from_expr(&expr.ty) {
						Some(result) => idents.push(result),
						None => {}
					}
				}
			}
			_ => match Ident::from_expr(&self.ty) {
				Some(result) => idents.push(result),
				None => {}
			},
		}

		idents
	}

	pub fn to_ident_list(&self) -> List<Expr> {
		let mut idents = List::new();

		match &self.ty {
			// TODO: Track comma spans.
			ExprTy::List(v) => {
				for expr in v.item_iter() {
					match Ident::from_expr(&expr.ty) {
						Some(_) => idents.push_item(expr.clone()),
						None => {}
					}
				}
			}
			_ => match Ident::from_expr(&self.ty) {
				Some(_) => idents.push_item(self.clone()),
				None => {}
			},
		}

		idents
	}
}

impl Ident {
	fn from_expr(
		expr: &ExprTy,
	) -> Option<Either<Ident, (Ident, Vec<ArrSize>)>> {
		match expr {
			ExprTy::Ident(i) => Some(Either::Left(i.clone())),
			ExprTy::Index { item, i, .. } => {
				let mut current_item = item;
				let mut stack = Vec::new();
				stack.push(i.as_deref());

				let ident = loop {
					match &current_item.ty {
						ExprTy::Ident(i) => {
							break i.clone();
						}
						ExprTy::Index { item, i, .. } => {
							stack.push(i.as_deref());
							current_item = item;
						}
						_ => return None,
					};
				};

				// In the expression parser, the `[..]` brackets are right-associative, so the outer-most pair is
				// at the top, and the inner-most is at the bottom. We want to reverse this to be in line with our
				// intuition, i.e. 2nd dimension first, then 1st dimension.
				stack.reverse();

				Some(Either::Right((
					ident,
					stack.into_iter().map(|i| i.cloned()).collect(),
				)))
			}
			_ => None,
		}
	}
}

impl Lit {
	pub fn parse(token: &Token) -> Result<Self, ()> {
		match token {
			Token::Bool(b) => Ok(Self::Bool(*b)),
			Token::Num {
				num: s,
				suffix,
				type_,
			} => Self::parse_num(&s, suffix.as_deref(), *type_),
			_ => Err(()),
		}
	}

	pub fn parse_num(
		s: &str,
		suffix: Option<&str>,
		type_: NumType,
	) -> Result<Self, ()> {
		// This can be empty, e.g. `0xu` is a `NumType::Hex` with contents `` with suffix `u`.
		if s == "" {
			return Err(());
		}
		match type_ {
			NumType::Dec => Self::parse_num_dec(s, suffix),
			NumType::Hex => Self::parse_num_hex(s, suffix),
			NumType::Oct => Self::parse_num_oct(s, suffix),
			NumType::Float => Self::parse_num_float(s, suffix),
		}
	}

	fn parse_num_dec(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 10) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 10) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_hex(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 16) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 16) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_oct(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "u" || suffix == "U" {
				if let Ok(u) = u64::from_str_radix(s, 8) {
					return Ok(Self::UInt(u));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 8) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_float(s: &str, suffix: Option<&str>) -> Result<Self, ()> {
		if let Some(suffix) = suffix {
			if suffix == "lf" || suffix == "LF" {
				if let Ok(f) = s.parse::<f64>() {
					return Ok(Self::Double(f));
				}
			} else if suffix == "f" || suffix == "F" {
				if let Ok(f) = s.parse::<f32>() {
					return Ok(Self::Float(f));
				}
			} else {
				return Err(());
			}
		} else {
			if let Ok(f) = s.parse::<f32>() {
				return Ok(Self::Float(f));
			}
		}

		Err(())
	}
}
