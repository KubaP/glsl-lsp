/// A span in the source file.
///
/// Keeps track of the offset between characters from the start of the source, e.g. `if=abc` would be stored as
/// `0-2, 2-3, 3-6`.
///
/// Illustrated example:
/// ```text
///   i   f   =   a   b   c
///  |-----| |-| |---------|
/// ^   ^   ^   ^   ^   ^   ^
/// 0   1   2   3   4   5   6
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
	pub start: usize,
	pub end: usize,
}

impl Span {
	/// Constructs a new `Span`.
	pub fn new(start: usize, end: usize) -> Self {
		Self { start, end }
	}

	/// Constructs a zero-width `Span` at `0`.
	///
	/// *Note:* This should only be used as a temporary placeholder for debugging purposes.
	pub fn empty() -> Self {
		Self { start: 0, end: 0 }
	}

	/// Constructs a zero-width `Span` from a position.
	pub fn from_zero_width(position: usize) -> Self {
		Self {
			start: position,
			end: position,
		}
	}

	/// Returns whether this span is located after the other span.
	pub fn is_after(&self, other: &Self) -> bool {
		self.start >= other.end
	}

	/// Returns whether the beginning of this span is located at or after the specified position.
	pub fn starts_at_or_after(&self, position: usize) -> bool {
		self.start >= position
	}

	/// Returns a new `Span` which ends at the previous position.
	pub fn end_at_previous(self) -> Self {
		// FIXME: Make this saturating to prevent overflow panic.
		let new_end = self.end - 1;

		// Note: The only time a span should have an end at `0` is if it was created with the `empty()`
		// constructor, which in itself is only a temporary feature and should be removed at some point.
		#[cfg(debug_assertions)]
		let new_end = if self.end == 0 { 0 } else { new_end };

		Self {
			// If this span has the same start and end, we need to set the new start to be the value of the new
			// end. Otherwise, we don't change anything.
			start: usize::min(self.start, new_end),
			end: new_end,
		}
	}

	/// Returns a new `Span` which spans the first character.
	pub fn first_char(self) -> Self {
		// FIXME: Make this saturating to prevent overflow panic.
		Self {
			start: self.start,
			end: usize::min(self.start + 1, self.end),
		}
	}

	/// Returns a new `Span` which spans the last character.
	pub fn last_char(self) -> Self {
		// FIXME: Make this saturating to prevent overflow panic.
		Self {
			start: usize::max(self.end - 1, self.start),
			end: self.end,
		}
	}

	/// Returns a new zero-width `Span` located at the start of this span.
	pub fn start_zero_width(self) -> Self {
		Self {
			start: self.start,
			end: self.start,
		}
	}

	/// Returns a new zero-width `Span` located at the end of this span.
	pub fn end_zero_width(self) -> Self {
		Self {
			start: self.end,
			end: self.end,
		}
	}
}

/// Constructs a new [`Span`] from a start and end position.
///
/// *Note:* This is just a shorthand for [`Span::new()`], since that becomes a bit verbose to type out again and
/// again, especially in the unit test assertions.
pub fn span(start: usize, end: usize) -> Span {
	Span { start, end }
}

pub type Spanned<T> = (T, Span);
