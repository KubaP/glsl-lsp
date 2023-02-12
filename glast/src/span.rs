/// A span in the source string.
///
/// Keeps track of the offset between **code units** from the start of the source string, e.g. `if=abc` would be
/// stored as `0-2, 2-3, 3-6`:
/// ```text
///   i   f   =   a   b   c
///  ├─────┤ ├─┤ ├─────────┤
/// ^   ^   ^   ^   ^   ^   ^
/// 0   1   2   3   4   5   6
/// ```
///
/// A code unit is a basic building block used by the unicode encoding system. It is effectively the primitive type
/// that is used to represent entire unicode code points. `utf-8` uses [`u8`] as the code unit, `utf-16` uses
/// [`u16`] as the code unit, and `utf-32` uses [`char`] (`u32`).
///
/// The offsets depend on which code unit is being counted, which in turn depends on the called parsing function.
/// By default, the spans count `utf-32` code units, i.e. rust [`char`]s, however, there are alternate functions
/// that count `utf-16` or `utf-8` code units:
/// - [`lexer::parse_with_utf_16_offsets()`](crate::lexer::parse_with_utf_16_offsets),
/// - [`lexer::parse_with_utf_16_offsets_and_version()`](crate::lexer::parse_with_utf_16_offsets_and_version),
/// - [`lexer::parse_with_utf_8_offsets()`](crate::lexer::parse_with_utf_8_offsets),
/// - [`lexer::parse_with_utf_8_offsets_and_version()`](crate::lexer::parse_with_utf_8_offsets_and_version).
///
/// The difference is only noticeable with non-ascii characters. Take the following string: `a𐐀c`. It has the
/// following representations in the different encodings (in decimal):
/// ```text
///         a (U+0061)    𐐀 (U+10400)          c (U+0063)
/// utf-8:  [97, 0, 0, 0] [240, 144, 144, 128] [99, 0, 0, 0]
/// utf-16: [97, 0]       [55297, 56320]       [99, 0]
/// utf-32: [97]          [66560]              [99]
/// ```
///
/// As you can see, both `a` and `c` use a single code point for all encodings; (a `u32` or `u16` takes up more
/// memory than a `u8`, but we aren't concerned with that). However, the `𐐀` takes 4 code units in `utf-8`, but
/// only two code units in `utf-16`, and only one code unit in `utf-32`. This is why the spans would differ:
/// ```text
///           a   𐐀   c
///         ^   ^   ^   ^
/// utf-8   0   1   5   6
/// utf-16  0   1   3   4
/// utf-32  0   1   2   3
/// ```
///
/// Why is this nuance necessary? Because the Language Server Protocol operates on `utf-16` offsets by default, so
/// support for that encoding was mandatory when authoring this crate.
///
/// # Invariants
/// If this type is manually constructed or modified, the `end` position must be equal-to or greater than the
/// `start` position. If this invariant is not upheld then interacting with this span, for example to resolve the
/// cursor position, will result in logical bugs and incorrect behaviour but it will never cause a panic or memory
/// unsafety.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span {
	pub start: usize,
	pub end: usize,
}

pub type Spanned<T> = (T, Span);

impl Span {
	/// Constructs a new span between the two positions.
	pub fn new(start: usize, end: usize) -> Self {
		// Invariant: If this assertion is not met, the semantic meaning of this type will be incorrect, but it will
		// never cause any further panics or memory unsafety. Hence, I've made a decision to only perform this
		// check in debug builds; the tests should catch any potential misuses.
		debug_assert!(
			start <= end,
			"[Span::new] `start: {start}` is located after `end: {end}`"
		);

		Self { start, end }
	}

	/// Constructs a new span between the end of the first span and the beginning of the second span.
	pub fn new_between(a: Span, b: Span) -> Self {
		// Invariant: If this assertion is not met, the semantic meaning of this type will be incorrect, but it will
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

	/// Constructs a new single-width span at the position.
	pub fn new_single_width(position: usize) -> Self {
		Self {
			start: position,
			end: position.saturating_add(1),
		}
	}

	/// Constructs a new zero-width span at the position.
	pub fn new_zero_width(position: usize) -> Self {
		Self {
			start: position,
			end: position,
		}
	}

	/// Returns whether this span is zero-width.
	pub fn is_zero_width(&self) -> bool {
		self.start == self.end
	}

	/// Returns whether this span is located before the other span.
	pub fn is_before(&self, span: &Self) -> bool {
		self.end <= span.start
	}

	/// Returns whether this span is located after the other span.
	pub fn is_after(&self, span: &Self) -> bool {
		self.start >= span.end
	}

	/// Returns whether this span is located before the position.
	pub fn is_before_pos(&self, pos: usize) -> bool {
		self.end <= pos
	}

	/// Returns whether this span is located before the position.
	pub fn is_after_pos(&self, pos: usize) -> bool {
		self.start >= pos
	}

	/// Returns whether the beginning of this span is located at or after the specified position.
	pub fn starts_at_or_after(&self, position: usize) -> bool {
		self.start >= position
	}

	/// Returns whether a span lies within this span.
	pub fn contains(&self, span: Self) -> bool {
		self.start <= span.start && span.end <= self.end
	}

	/// Returns whether a position lies within this span.
	pub fn contains_pos(&self, position: usize) -> bool {
		self.start <= position && position <= self.end
	}

	/// Returns a new span which starts at the same position but ends at a previous position, i.e. `end:
	/// span.end - 1`.
	pub fn end_at_previous(self) -> Self {
		let new_end = self.end.saturating_sub(1);

		Self {
			// If this span has the same start and end positions, we need to set the new start to be the value of
			// the new end. If we didn't, we would break the invariant that the start must be before the end.
			start: usize::min(self.start, new_end),
			end: new_end,
		}
	}

	/// Returns a new span over the first character of this span.
	///
	/// If this span is zero-width, the new span will be identical.
	pub fn first_char(self) -> Self {
		Self {
			start: self.start,
			end: usize::min(self.start.saturating_add(1), self.end),
		}
	}

	/// Returns a new span over the last character of this span.
	///
	/// If this span is zero-width, the new span will be identical.
	pub fn last_char(self) -> Self {
		Self {
			start: usize::max(self.end.saturating_sub(1), self.start),
			end: self.end,
		}
	}

	/// Returns a new zero-width span located at the start of this span.
	pub fn start_zero_width(self) -> Self {
		Self {
			start: self.start,
			end: self.start,
		}
	}

	/// Returns a new zero-width span located at the end of this span.
	pub fn end_zero_width(self) -> Self {
		Self {
			start: self.end,
			end: self.end,
		}
	}

	/// Returns a new span one width long, beginning at the end of this span.
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

	/// Returns a new span one width long, ending at the beginning of this span.
	pub fn previous_single_width(self) -> Self {
		// Note: Unlike `next_single_width()`, this has a potential to overflow onto the previous line if the token
		// starts at the beginning on the line. Since this is used much less often, I don't think it's worth
		// fixing/dealing with this.
		Self {
			start: self.start.saturating_sub(1),
			end: self.start,
		}
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

/// The type of code units the `Span`s are counting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpanEncoding {
	/// Spans count `utf-8` code units.
	Utf8,
	/// Spans count `utf-16` code units.
	Utf16,
	/// Spans count `utf-32` code units, i.e. rust [`char`]s.
	Utf32,
}

/// Constructs a new [`Span`] from a start and end position.
///
/// This is just a shorthand for [`Span::new()`], since that becomes a bit verbose to type out again and again,
/// especially in the unit test assertions.
#[cfg(test)]
pub(crate) fn span(start: usize, end: usize) -> Span {
	Span { start, end }
}
