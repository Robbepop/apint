use digit;
use errors::{Result, Error};
use errors;

use std::convert::TryFrom;

/// The `BitWidth` represents the length of an `APInt`.
/// 
/// Its invariant restricts it to always be a positive, non-zero value.
/// Code that built's on top of `BitWidth` may and should use this invariant.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitWidth(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Storage { Inl, Ext }

//  ===========================================================================
///  Constructors & 
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

	/// Creates a `BitWidth` from the given `usize`.
	/// 
	/// # Errors
	/// 
	/// - When encountering a given bitwidth of zero (`0`).
	pub fn from_usize(val: usize) -> Result<Self> {
		if val == 0 {
			return Err(Error::invalid_zero_bitwidth())
		}
		Ok(BitWidth(val))
	}
}

impl TryFrom<usize> for BitWidth {
	type Error = errors::Error;

	fn try_from(val: usize) -> Result<BitWidth> {
		BitWidth::from_usize(val)
	}
}

impl TryFrom<BitWidth> for BitWidth {
	type Error = errors::Error;

	fn try_from(bw: BitWidth) -> Result<BitWidth> {
		Ok(bw)
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

	pub(crate) fn excess_bits(self) -> Option<usize> {
		match self.to_usize() % digit::BITS {
			0 => None,
			n => Some(n)
		}
	}

	/// Returns a storage specifier that tells the caller if `APInt`'s 
	/// associated with this bitwidth require an external memory (`Ext`) to store 
	/// their digits or may use inplace memory (`Inl`).
	#[inline]
	pub(crate) fn storage(self) -> Storage {
		if self.to_usize() < digit::BITS { Storage::Inl } else { Storage::Ext }
	}

	/// Returns the number of digit-blocks that are required to represent any 
	/// value with a bit-width equal to `self`.
	#[inline]
	pub(crate) fn required_blocks(&self) -> usize {
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
