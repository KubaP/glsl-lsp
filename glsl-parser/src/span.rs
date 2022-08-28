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
///
/// # Invariants
/// If this type is manually constructed, the `end` position must be equal-to or greater than the `start` position.
/// If this invariant is not upheld, converting such a `Span` to an LSP diagnostic will result in a logically wrong
/// range.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span {
	pub start: usize,
	pub end: usize,
}

impl Span {
	/// Constructs a new `Span` between the positions.
	pub fn new(start: usize, end: usize) -> Self {
		// Panics: If this assertion is not met, the semantic meaning of this type will be incorrect, but it will
		// never cause any further panics or memory unsafety. Hence, I've made a decision to only perform this
		// check in debug builds; the tests should catch any potential misuses.
		debug_assert!(
			start <= end,
			"[Span::new] `start: {start}` is located after `end: {end}`"
		);

		Self { start, end }
	}

	/// Constructs a new `Span` between the two spans.
	pub fn new_between(a: Span, b: Span) -> Self {
		// Panics: If this assertion is not met, the semantic meaning of this type will be incorrect, but it will
		// never cause any further panics or memory unsafety. Hence, I've made a decision to only perform this
		// check in debug builds; the tests should catch any potential misuses.
		debug_assert!(
			a.end <= b.start,
			"[Span::new_between] `a.end: {}` is located after `b.start: {}`",
			a.end,
			b.start
		);

		Self {
			start: a.end,
			end: b.start,
		}
	}

	/// Constructs a zero-width `Span` from a position.
	pub fn new_zero_width(position: usize) -> Self {
		Self {
			start: position,
			end: position,
		}
	}

	/// Constructs a zero-width `Span` at `0`.
	pub fn empty() -> Self {
		Self { start: 0, end: 0 }
	}

	/// Returns whether this span is located after the other span.
	pub fn is_after(&self, other: &Self) -> bool {
		self.start >= other.end
	}

	/// Returns whether this span is zero-width.
	pub fn is_zero_width(&self) -> bool {
		self.start == self.end
	}

	/// Returns whether the beginning of this span is located at or after the specified position.
	pub fn starts_at_or_after(&self, position: usize) -> bool {
		self.start >= position
	}

	/// Returns a new `Span` which starts at the same poisition but ends at a previous position, i.e. `end:
	/// span.end - 1`.
	pub fn end_at_previous(self) -> Self {
		let new_end = self.end.saturating_sub(1);
		let new_end = if self.end == 0 { 0 } else { new_end };

		Self {
			// If this span has the same start and end, we need to set the new start to be the value of the new
			// end. Otherwise, we don't change anything.
			start: usize::min(self.start, new_end),
			end: new_end,
		}
	}

	/// Returns a new `Span` which spans the first character of this span.
	pub fn first_char(self) -> Self {
		Self {
			start: self.start,
			end: usize::min(self.start.saturating_add(1), self.end),
		}
	}

	/// Returns a new `Span` which spans the last character of this span.
	pub fn last_char(self) -> Self {
		Self {
			start: usize::max(self.end.saturating_sub(1), self.start),
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

	/// Returns a new `Span` one width long, beginning at the end of this span.
	///
	/// Examples of how vscode will squiggle this:
	/// ```c
	/// // \ is the beginning of the newline char
	///
	/// return\
	///      ^^
	///
	/// return  \
	///       ^^
	///
	/// return)
	///       ^^
	/// ```
	pub fn next_single_width(self) -> Self {
		// Note: Because every line has at least a `\r` or `\n` at the end, even if the token ends at the last
		// position on the line, the extra +1 will never overflow onto the next line because we have the
		// end-of-line character(s).
		Self {
			start: self.end,
			end: self.end.saturating_add(1),
		}
	}

	/// Returns a new `Span` one width long, ending at the beginning of this span.
	pub fn previous_single_width(self) -> Self {
		// Note: Unlike `next_single_width()`, this has a potential to overflow onto the previous line if the token
		// starts at the beginning on the line. Since this is used comparatively much less often, I don't think
		// it's worth fixing this.
		Self {
			start: self.start.saturating_sub(1),
			end: self.start,
		}
	}

	/// Returns whether a position lies within this `Span`.
	pub fn contains_position(&self, position: usize) -> bool {
		self.start <= position && position <= self.end
	}
}

impl std::fmt::Debug for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}-{}", self.start, self.end)
	}
}

impl std::fmt::Display for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}..{}", self.start, self.end)
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
