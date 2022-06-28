/// A span in the source file.
/// 
/// Keeps track of the offset between characters from the start of the source, e.g. `if=abc` would be stored as
/// `0..2, 2..3, 3..6`.
/// 
/// Illustrated:
/// ```text
///   i   f   =   a   b   c
/// ^   ^   ^   ^   ^   ^   ^
/// 0   1   2   3   4   5   6
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
	pub start: usize,
	pub end: usize,
}

impl Span {
	/// Constructs a span which starts and ends at `0`. This should only be used as a temporary placeholder.
	pub fn empty() -> Self {
		Self { start: 0, end: 0 }
	}

	/// Returns whether this span is located after the other span.
	pub fn is_after(&self, other: &Self) -> bool {
		// MAYBE: Implement `PartialOrd+Ord` instead?
		self.start >= other.end
	}
}

/// Constructs a new [`Span`] from a start and end point.
pub fn span(start: usize, end: usize) -> Span {
	Span { start, end }
}

pub type Spanned<T> = (T, Span);