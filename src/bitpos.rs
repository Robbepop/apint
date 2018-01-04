use errors::{Result};
use digit;

/// Represents a bit position within an `ApInt`.
/// 
/// This utility might become useful later, for example
/// when we reduce the range of valid bit widths for some
/// optimization oportunities.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitPos(usize);

/// A `DigitPos` represents the integer offset at which to find
/// a `Digit` within an `ApInt` instance.
pub type DigitPos = usize;

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

	/// Converts this `BitPos` into its associated `BitPos` that is usable to operate
	/// on `Digit` instances.
	#[inline]
	pub fn to_pos_within_digit(self) -> BitPos {
		BitPos(self.0 % digit::BITS)
	}

	/// Splits this `BitPos` that may range over several `Digit`s within an `ApInt`
	/// into the associated `Digit` offset and its `Digit`-relative bit position.
	#[inline]
	pub fn to_digit_and_bit_pos(self) -> (DigitPos, BitPos) {
		let digit_pos = DigitPos::from(self.0 / digit::BITS);
		let bit_pos = BitPos::from(self.0 % digit::BITS);
		(digit_pos, bit_pos)
	}
}

impl From<usize> for BitPos {
	#[inline]
	fn from(pos: usize) -> BitPos {
		BitPos(pos)
	}
}
