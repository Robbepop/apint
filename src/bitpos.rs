use errors::{Result};

/// Represents a bit position within an `ApInt`.
/// 
/// This utility might become useful later, for example
/// when we reduce the range of valid bit widths for some
/// optimization oportunities.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitPos(usize);

impl BitPos {
	/// Returns the `usize` representation of this `BitPos`.
	#[inline]
	pub fn to_usize(self) -> usize {
		self.0
	}

	/// Returns a `BitPos` representing the given bit position.
	/// 
	/// # Errors
	/// 
	/// - This operation cannot fail but may do so in future version of this library.
	#[inline]
	pub fn new(pos: usize) -> Result<BitPos> {
		Ok(BitPos(pos))
	}
}

impl From<usize> for BitPos {
	#[inline]
	fn from(pos: usize) -> BitPos {
		BitPos(pos)
	}
}
