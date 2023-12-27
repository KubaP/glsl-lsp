//! *glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.
//!
//! ⚠ This crate is still heavily **work-in-progress**. The main functionality & API of the lexer and parser are
//! roughly finalized, but small changes and tweaks are still to be expected, and other features are not
//! implemented yet.
//!
//! This crate is part of a larger effort to provide a high-quality LSP implementation for GLSL. Hence, this crate
//! exposes more than just the basic lexing and parsing functionality found in other crates or libraries for other
//! languages:
//! - The lexer changes the grammar depending on an encountered version directive, in line with the specification.
//! - Lexing and parsing functions produce useful metadata about their inputs.
//! - The parser produces not only an AST, but also syntax and (some) semantic diagnostics, as well as syntax
//!   highlighting information.
//! - The parser correctly expands arbitrarily-complex macros anywhere that it should, in line with the
//!   specification.
//! - The parser correctly handles all conditional compilation, no matter how convoluted. Full control over which
//!   conditional branches to include/exclude is provided, include the ability to evaluate conditional directives
//!   on-the-fly.
//! - Both the lexer and parser are aiming to be 100% specification compliant.
//!
//! The currently supported GLSL versions are:
//!
//! |GLSL version|OpenGL version|
//! |-|-|
//! |460|4.6|
//! |450|4.5|
//!
//! There are plans to support many more versions, not limited to but including 110 (default), 130, 330, 400, 410,
//! and 100 (es), 300 es & 320 es
//!
//! # The parsing pipeline
//! This crate is split into modules representing the different stages of parsing/manipulation:
//! - [`lexer`] - Lexer and the token stream.
//! - [`parser`] - Parser and the abstract syntax tree.
//! - `analyzer` - High intermediate representation and analysis, such as name resolution.
//!
//! This crate operates only on [`str`] inputs because the GLSL specification states that GLSL source strings must
//! use the UTF-8 encoding. That means that if the source can be parsed into a valid Rust [`str`] then it must be
//! valid, so no support for `[u8]` inputs is provided.
//!
//! ## Source String
//! We start with a string of characters that makes up the glsl source file. We will use the following example to
//! illustrate the pipeline:
//! ```c
//! // Comment
//! int i = 5.0+1;
//! ```
//!
//! ## Lexer
//! This is the first transformation in the parsing pipeline, and it converts a string of characters into a stream
//! of tokens. The source string would become (in pseudocode):
//! ```text
//! (comment " Comment") (ident "int") (ident "i") (op "=") (float "5.0") (op "+") (int "1") (punct ";")
//! ```
//!
//! ## Parser
//! This is the next transformation in the parsing pipeline, and it converts the token stream into a tree that only
//! contains semantic information, loosing things like irrelevant punctuation symbols or comments.
//!
//! Firstly, conditional compilation is applied to the token stream. Then, the resulting token stream is parsed,
//! expanding any macros in the process.
//!
//! The token stream would become (in pseudocode):
//! ```text
//! VariableDeclaration {
//!     type: Primitive.Int,
//!     ident: Identifier("i"),
//!     value: BinaryExpression {
//!         left: Float(5.0),
//!         op: Addition,
//!         right: Int(1),
//!     }
//! }
//! ```
//!
//! ## Analyzer
//! This is the final stage of the parsing pipeline, and includes actions such as name resolution and
//! type-checking.
//!
//! ⚠ This module is **not implemented yet**.
//!
//! # Diagnostics
//! The parser produces syntax errors when it encounters invalid syntax. It also produces semantic diagnostics in
//! relation to macros. All other semantic diagnostics are currently waiting on the `analyzer` module to be
//! implemented.
//!
//! For more details, see the [`diag`] module.
//!
//! # Syntax Highlighting
//! The parser produces syntax highlighting tokens as part of the parsing process. These tokens correctly highlight
//! all text that has been parsed, but they are not fully semantically-aware; this is because the parser only
//! creates an abstract syntax tree, it does not perform name-resolution. This means that currently most
//! identifiers are of the `UncheckedIdent` variant. Once the `analyzer` module has been implemented to include
//! name-resolution functionality, these syntax tokens can be converted into more specific variable/type/function
//! identifiers, which would result in fully semantically-aware highlighting information.
//!
//! For more details, see the [`syntax`] module.
//!
//! # Security
//! This crate has zero uses of `unsafe`.
//!
//! This crate does not execute arbitrary source code; any evaluations (such as evaluating `#if` expressions) are
//! free of any side-effects. This crate takes in string slices, performs analysis operations, and returns data
//! structures; it does not perform any I/O or networking calls.
//!
//! # Performance & Testing
//! Currently, this crate has not been particularly optimized for performance; there is a lot of `clone()`-ing. The
//! general internal structure is well suited for optimization, but the work has not yet been done because the
//! internals have undergone numerous large-scale refactors and re-writes whilst the functionality and public api
//! have matured. Unless any massive oversights have occurred, the current structure is the one that will go
//! forward, and once this crate has been given a bit of use to iron out any remaining minor bugs, it will be
//! optimized to minimize data cloning and memory allocations.
//!
//! Currently, this crate does not have extensive testing. Some parts of the crate have good unit test coverage,
//! but other parts lack any tests completely and there are no integration tests yet. This is an important goal
//! that is being progressively worked towards.
//!
//! # Dependencies
//! Dependencies are kept to a minimum. Currently they consist of: `bitflags`, `generational-arena`, and `tinyvec`.

pub mod diag;
pub mod lexer;
pub mod parser;
mod span;
pub mod syntax;

pub use span::*;

/// Describes a GLSL version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum GlslVersion {
	/// OpenGL 4.5
	_450,
	/// OpenGL 4.6
	_460,
	/// A GLSL version unsupported by the crate.
	#[default]
	// TODO: The default GLSL version in reality is 110, but we currently don't support that.
	Unsupported,
}

impl GlslVersion {
	/// Parses a number into a GLSL version.
	fn parse(num: usize) -> Option<Self> {
		match num {
			450 => Some(Self::_450),
			460 => Some(Self::_460),
			_ => None,
		}
	}
}

/// Holds one of 2 possible values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Either<L, R> {
	Left(L),
	Right(R),
}

/// Holds one of 3 possible values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Either3<A, B, C> {
	A(A),
	B(B),
	C(C),
}

/// A non-empty vector, guaranteed to always have at least one element.
///
/// This is just a wrapper struct around [`Vec<T>`]. This implements a lot of commonly used (stable) `Vec` methods,
/// includes derives for commonly used traits, as well as implements [`AsRef`]/[`AsMut`],
/// [`Deref`](std::ops::Deref)/[`DerefMut`](std::ops::DerefMut),
/// [`Index`](std::ops::Index)/[`IndexMut`](std::ops::IndexMut), [`Default`], [`IntoIterator`] for ref/mut/owned
/// iteration, and [`PartialEq`] against all array/slice types.
///
/// # Examples
/// ```rust
/// // A non-empty vector must be initialized with one element.
/// let mut vec = NonEmpty::new(5i32);
/// assert_eq!(vec.len(), 1);
///
/// // You can push elements into the vector like normal.
/// vec.push(10);
/// vec.push(100);
///
/// assert_eq!(vec.len(), 3);
///
/// // You can iterate (immutably/mutably/by value) over the vector just like normal.
/// for i in &vec {
///     println!("{i}");
/// }
///
/// // The vector's contents can be compared just like normal.
/// assert_eq!(vec, [5, 10, 100]);
///
/// // You can remove elements from the vector, ** apart from the last one. **
/// assert_eq!(vec.pop(), Some(100));
/// assert_eq!(vec.pop(), Some(10));
/// assert_eq!(vec.pop(), None);
///
/// assert_eq!(vec.len(), 1);
///
/// // To remove the final element, you must destruct the vector.
/// // This method consumes the vector in the process.
/// assert_eq!(vec.destruct(), 5);
///
/// // `vec` no longer exists.
/// ```
/// For rare cases when access to the underlying vector is necessary, because the API of this type doesn't/can't
/// implement something (or for other reasons), use the [`as_vec()`](NonEmpty::as_vec()) and
/// [`as_mut_vec()`](NonEmpty::as_mut_vec()) methods. If using the mutable method, the caller must ensure the type
/// invariant is upheld at all times, otherwise undefined behaviour may occur.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NonEmpty<T>(Vec<T>);

impl<T> NonEmpty<T> {
	/// Constructs a new `NonEmpty<T>`.
	pub fn new(item: T) -> Self {
		Self(vec![item])
	}

	/// Tries to construct a new `NonEmpty<T>` from a `Vec<T>`. This succeeds only if the vector has at least one
	/// element.
	pub fn from_vec(vec: Vec<T>) -> Option<Self> {
		if vec.is_empty() {
			None
		} else {
			Some(Self(vec))
		}
	}

	/// Appends an element to the back of the vector.
	pub fn push(&mut self, item: T) {
		self.0.push(item);
	}

	/// Inserts an element at position `index` within the vector, shifting all elements after it to the right.
	pub fn insert(&mut self, index: usize, item: T) {
		self.0.insert(index, item);
	}

	/// Returns a reference to an element at position `index`, or [`None`] if the index is out of bounds.
	pub fn get(&self, index: usize) -> Option<&T> {
		self.0.get(index)
	}

	/// Returns a mutable reference to an element at position `index`, or [`None`] if the index is out of bounds.
	pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
		self.0.get_mut(index)
	}

	/// Removes the last element from the vector and returns it, or [`None`] if the vector contains only one
	/// element.
	pub fn pop(&mut self) -> Option<T> {
		if self.0.len() == 1 {
			None
		} else {
			self.0.pop()
		}
	}

	/// Removes the element at position `index` from the vector and returns it, or [`None`] if the vector contains
	/// only one element. If the vector contains only one element, use the [`NonEmpty::destruct()`] function
	/// instead.
	pub fn remove(&mut self, index: usize) -> Option<T> {
		if self.0.len() == 1 {
			None
		} else {
			Some(self.0.remove(index))
		}
	}

	/// Destructs this non-empty vector, returning the last element.
	///
	/// This is implemented in this manner because removing the last element would make this non-empty vector
	/// empty, which would break the invariant. Hence, this method must consume the value to prevent it from being
	/// accessed afterwards.
	///
	/// # Panics
	/// If this vector has more than one element, this method will panic.
	pub fn destruct(mut self) -> T {
		if self.0.len() > 1 {
			panic!("NonEmpty vector cannot be destructed because it has more than 1 element")
		}
		self.0.remove(0)
	}

	/// Appends the other non-empty vector into this non-empty vector.
	pub fn append(&mut self, mut other: Self) {
		self.0.append(&mut other.0);
	}

	/// Returns the number of elements in the vector.
	pub fn len(&self) -> std::num::NonZeroUsize {
		unsafe { std::num::NonZeroUsize::new_unchecked(self.0.len()) }
	}

	/// Returns a reference to the first element of the vector.
	pub fn first(&self) -> &T {
		self.0.first().unwrap()
	}

	/// Returns a mutable reference to the first element of the vector.
	pub fn first_mut(&mut self) -> &mut T {
		self.0.first_mut().unwrap()
	}

	/// Returns a reference to the last element of the vector.
	pub fn last(&self) -> &T {
		self.0.last().unwrap()
	}

	/// Returns a mutable reference to the last element of the vector.
	pub fn last_mut(&mut self) -> &mut T {
		self.0.last_mut().unwrap()
	}

	/// Returns a reference to the underlying vector.
	///
	/// # Invariants
	/// The vector has at least one element.
	pub fn as_vec(&self) -> &Vec<T> {
		&self.0
	}

	/// Returns a mutable reference to the underlying vector.
	///
	/// # Safety
	/// The caller must ensure that the vector always retains at least one element. Failure to do so will break the
	/// invariant on the `NonEmpty` type, and potentially lead to undefined behaviour.
	pub fn as_mut_vec(&mut self) -> &mut Vec<T> {
		&mut self.0
	}

	/// Returns the underlying vector, destructuring this type in the process.
	///
	/// # Invariants
	/// The vector has at least one element.
	pub fn into_vec(self) -> Vec<T> {
		self.0
	}
}

impl<T: Default> Default for NonEmpty<T> {
	fn default() -> Self {
		Self(vec![T::default()])
	}
}

impl<T> std::ops::Index<usize> for NonEmpty<T> {
	type Output = T;

	fn index(&self, index: usize) -> &Self::Output {
		&self.0[index]
	}
}

impl<T> std::ops::IndexMut<usize> for NonEmpty<T> {
	fn index_mut(&mut self, index: usize) -> &mut Self::Output {
		&mut self.0[index]
	}
}

impl<T> AsRef<[T]> for NonEmpty<T> {
	fn as_ref(&self) -> &[T] {
		self.0.as_ref()
	}
}

impl<T> AsMut<[T]> for NonEmpty<T> {
	fn as_mut(&mut self) -> &mut [T] {
		self.0.as_mut()
	}
}

impl<T> std::ops::Deref for NonEmpty<T> {
	type Target = [T];

	fn deref(&self) -> &Self::Target {
		self.0.deref()
	}
}

impl<T> std::ops::DerefMut for NonEmpty<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.0.deref_mut()
	}
}

impl<T> IntoIterator for NonEmpty<T> {
	type Item = T;

	type IntoIter = std::vec::IntoIter<Self::Item>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<'a, T> IntoIterator for &'a NonEmpty<T> {
	type Item = &'a T;

	type IntoIter = std::slice::Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.iter()
	}
}

impl<'a, T> IntoIterator for &'a mut NonEmpty<T> {
	type Item = &'a mut T;

	type IntoIter = std::slice::IterMut<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.iter_mut()
	}
}

impl<T: PartialEq<T>, const N: usize> PartialEq<&[T; N]> for NonEmpty<T> {
	fn eq(&self, other: &&[T; N]) -> bool {
		&self.0 == other
	}
}

impl<T: PartialEq<T>> PartialEq<&[T]> for NonEmpty<T> {
	fn eq(&self, other: &&[T]) -> bool {
		&self.0 == other
	}
}

impl<T: PartialEq<T>, const N: usize> PartialEq<&mut [T; N]> for NonEmpty<T> {
	fn eq(&self, other: &&mut [T; N]) -> bool {
		&self.0 == &**other
	}
}

impl<T: PartialEq<T>, const N: usize> PartialEq<[T; N]> for NonEmpty<T> {
	fn eq(&self, other: &[T; N]) -> bool {
		&self.0 == other
	}
}

impl<T: PartialEq<T>> PartialEq<[T]> for NonEmpty<T> {
	fn eq(&self, other: &[T]) -> bool {
		&self.0 == other
	}
}

/// Crate-level checks.
#[cfg(test)]
mod checks {
	use crate::{parser::ast::Omittable, NonEmpty};
	use std::mem::size_of;

	#[test]
	fn sizes() {
		assert_eq!(size_of::<Option<i32>>(), size_of::<Omittable<i32>>());
		assert_eq!(size_of::<Vec<i32>>(), size_of::<NonEmpty<i32>>());
		assert_eq!(
			size_of::<Option<Vec<i32>>>(),
			size_of::<Omittable<NonEmpty<i32>>>()
		);

		// TODO: Check `symbol::Type` booleans are optimized into bitflag.
	}
}
