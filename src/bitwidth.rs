use digit;
use storage::Storage;
use bitpos::BitPos;
use apint::{ShiftAmount};
use errors::{Result, Error};

/// The `BitWidth` represents the length of an `ApInt`.
/// 
/// Its invariant restricts it to always be a positive, non-zero value.
/// Code that built's on top of `BitWidth` may and should use this invariant.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitWidth(usize);

//  ===========================================================================
///  Constructors
/// ===========================================================================
impl BitWidth {
	/// Creates a `BitWidth` that represents a bit-width of `1` bit.
	#[inline]
	pub fn w1() -> Self { BitWidth(1) }

	/// Creates a `BitWidth` that represents a bit-width of `8` bits.
	#[inline]
	pub fn w8() -> Self { BitWidth(8) }

	/// Creates a `BitWidth` that represents a bit-width of `16` bits.
	#[inline]
	pub fn w16() -> Self { BitWidth(16) }

	/// Creates a `BitWidth` that represents a bit-width of `32` bits.
	#[inline]
	pub fn w32() -> Self { BitWidth(32) }

	/// Creates a `BitWidth` that represents a bit-width of `64` bits.
	#[inline]
	pub fn w64() -> Self { BitWidth(64) }

	/// Creates a `BitWidth` that represents a bit-width of `128` bits.
	#[inline]
	pub fn w128() -> Self { BitWidth(128) }

	/// Creates a `BitWidth` from the given `usize`.
	/// 
	/// # Errors
	/// 
	/// - If the given `width` is equal to zero.
	pub fn new(width: usize) -> Result<Self> {
		if width == 0 {
			return Err(Error::invalid_zero_bitwidth())
		}
		Ok(BitWidth(width))
	}

	/// Returns `true` if the given `BitPos` is valid for this `BitWidth`.
	#[inline]
	pub(crate) fn is_valid_pos<P>(self, pos: P) -> bool
		where P: Into<BitPos>
	{
		pos.into().to_usize() < self.0
	}

	/// Returns `true` if the given `ShiftAmount` is valid for this `BitWidth`.
	#[inline]
	pub(crate) fn is_valid_shift_amount<S>(self, shift_amount: S) -> bool
		where S: Into<ShiftAmount>
	{
		shift_amount.into().to_usize() < self.0
	}

	/// Returns a `BitPos` at the given position if the position is valid for this `BitWidth`;
	/// returns a corresponding error otherwise.
	fn pos_at(self, pos: usize) -> Result<BitPos> {
		if !(pos < self.0) {
			return Err(Error::invalid_bit_access(pos, self.0))
		}
		BitPos::new(pos)
	}

	/// Returns the maximum possible `BitPos` for this `BitWidth`.
	#[inline]
	pub(crate) fn max_bit_pos(self) -> BitPos {
		BitPos::from(self.to_usize() - 1)
	}

	/// Returns the `BitPos` for the sign bit of an `ApInt` with this `BitWidth`.
	#[inline]
	pub(crate) fn sign_bit_pos(self) -> BitPos {
		BitPos::from(self.max_bit_pos().to_usize() % digit::BITS)
	}
}

impl From<usize> for BitWidth {
	fn from(width: usize) -> BitWidth {
		BitWidth::new(width).unwrap()
	}
}

//  ===========================================================================
///  API
/// ===========================================================================
impl BitWidth {
	/// Converts this `BitWidth` into a `usize`.
	#[inline]
	pub fn to_usize(self) -> usize {
		self.0
	}

	/// Returns the number of exceeding bits that is implied for `ApInt`
	/// instances with this `BitWidth`.
	/// 
	/// For example for an `ApInt` with a `BitWidth` of `140` bits requires
	/// exactly `3` digits (each with its `64` bits). The third however,
	/// only requires `140 - 128 = 12` bits of its `64` bits in total to
	/// represent the `ApInt` instance. So `excess_bits` returns `12` for
	/// a `BitWidth` that is equal to `140`.
	/// 
	/// *Note:* A better name for this method has yet to be found!
	pub(crate) fn excess_bits(self) -> Option<usize> {
		match self.to_usize() % digit::BITS {
			0 => None,
			n => Some(n)
		}
	}

	/// Returns the exceeding `BitWidth` of this `BitWidth`.
	/// 
	/// *Note:* This is just a simple wrapper around the `excess_bits` method.
	///         Read the documentation of `excess_bits` for more information 
	///         about what is actually returned by this.
	pub(crate) fn excess_width(self) -> Option<BitWidth> {
		self.excess_bits().map(BitWidth::from)
	}

	/// Returns a storage specifier that tells the caller if `ApInt`'s 
	/// associated with this bitwidth require an external memory (`Ext`) to store 
	/// their digits or may use inplace memory (`Inl`).
	/// 
	/// *Note:* Maybe this method should be removed. A constructor for
	///         `Storage` fits better for this purpose.
	#[inline]
	pub(crate) fn storage(self) -> Storage {
		Storage::from(self)
	}

	/// Returns the number of digits that are required to represent an
	/// `ApInt` with this `BitWidth`.
	/// 
	/// *Note:* Maybe we should move this method somewhere else?
	#[inline]
	pub(crate) fn required_digits(&self) -> usize {
		((self.to_usize() - 1) / digit::BITS) + 1
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BitWidthIter {
	total: usize,
	cur  : usize
}

impl BitWidthIter {
	pub fn new(total: usize) -> BitWidthIter {
		BitWidthIter{total, cur: 0}
	}
}

impl Iterator for BitWidthIter {
	type Item = BitWidth;

	fn next(&mut self) -> Option<Self::Item> {
		if self.cur >= self.total { return None; }
		use std::cmp;
		let cur = cmp::max(self.total - self.cur, digit::BITS);
		self.cur += digit::BITS;
		Some(BitWidth(cur))
	}
}
