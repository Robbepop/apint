use bitwidth::BitWidth;
use errors::{Error, Result};

use std::ops::{
	Not,
	BitAnd,
	BitOr,
	BitXor,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};

pub(crate) const BITS: usize = 64;

const U64_ZEROS: u64 = 0x0000_0000_0000_0000_u64;
const U64_ONES : u64 = 0xFFFF_FFFF_FFFF_FFFF_u64;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bit { Unset = 0, Set = 1 }

impl From<bool> for Bit {
	#[inline]
	fn from(flag: bool) -> Bit {
		if flag { Bit::Set } else { Bit::Unset }
	}
}

impl From<Bit> for bool {
	#[inline]
	fn from(bit: Bit) -> bool {
		match bit {
			Bit::Set   => true,
			Bit::Unset => false
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Digit(pub u64);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DoubleDigit(pub u128);

impl From<u64> for Digit {
	#[inline]
	fn from(val: u64) -> Digit {
		Digit::from_u64(val)
	}
}

//  =======================================================================
///  Constructors
/// =======================================================================
impl Digit {
	/// Creates a digit from a `u64` representation.
	#[inline]
	pub fn from_u64(val: u64) -> Digit {
		Digit(val)
	}

	/// Creates a digit that only has the nth bit set to '1'.
	#[inline]
	pub fn one_at(n: usize) -> Result<Digit> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(Digit::from_u64(1 << n))
	}

	/// Creates a digit that represents the value `1`.
	#[inline]
	pub fn one() -> Digit {
		Digit::from_u64(1)
	}

	/// Creates a digit where all bits are initialized to `0`.
	#[inline]
	pub fn zeros() -> Digit {
		Digit::from_u64(U64_ZEROS)
	}

	/// Creates a digit where all bits are initialized to `1`.
	#[inline]
	pub fn ones() -> Digit {
		Digit::from_u64(U64_ONES)
	}
}

//  ===========================================================================
///  Utility & helper methods.
/// ===========================================================================
impl Digit {
	/// Returns the internal representation as `u64` value.
	#[inline]
	pub fn to_u64(self) -> u64 { 
		self.0
	}
}

// //  =======================================================================
// ///  Deprecated. To be removed.
// /// =======================================================================
impl Digit {
	#[inline]
	pub fn truncated<W>(mut self, bitwidth: W) -> Result<Digit>
		where W: Into<BitWidth>
	{
		let bitwidth = bitwidth.into();
		self.truncate(bitwidth)?;
		Ok(self)
	}

	#[inline]
	pub fn truncate<W>(&mut self, bitwidth: W) -> Result<()>
		where W: Into<BitWidth>
	{
		let bitwidth = bitwidth.into();
		if bitwidth.to_usize() > self::BITS {
			return Err(Error::invalid_bit_access(bitwidth.to_usize(), self::BITS))
		}
		Ok(self.0 &= U64_ONES >> ((self::BITS as u64) - (bitwidth.to_usize() as u64)))
	}
}

//  ===========================================================================
///  Bitwise access
/// ===========================================================================
impl Digit {
	/// Returns `true` if the `n`th bit is set to `1`, else returns `false`.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn get(&self, n: usize) -> Result<Bit> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(Bit::from(((self.to_u64() >> n) & 0x01) == 1))
	}

	/// Sets the `n`th bit in the digit to `1`.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn set(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 |= 0x01 << n)
	}

	/// Sets the `n`th bit in the digit to `0`.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn unset(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 &= !(0x01 << n))
	}

	/// Flips `n`th bit.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn flip(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 ^= 0x01 << n)
	}

	/// Sets all bits in this digit to `1`.
	#[inline]
	pub fn set_all(&mut self) {
		self.0 |= U64_ONES
	}

	/// Sets all bits in this digit to `0`.
	#[inline]
	pub fn unset_all(&mut self) {
		self.0 &= U64_ZEROS
	}

	/// Flips all bits in this digit.
	#[inline]
	pub fn flip_all(&mut self) {
		self.0 ^= U64_ONES
	}

	/// Sets the first `n` bits in the digit to `1`.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn set_first_n(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 |= !(U64_ONES >> n))
	}

	/// Sets the first `n` bits in the digit to `0`.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn unset_first_n(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 &= U64_ONES >> (self::BITS - n))
	}

}

//  ===========================================================================
///  Bitwise operations
/// ===========================================================================
impl Not for Digit {
	type Output = Self;

	fn not(self) -> Self::Output {
		Digit(!self.to_u64())
	}
}

impl Digit {
	pub fn not_inplace(&mut self) {
		self.0 = !self.to_u64()
	}
}

impl BitAnd for Digit {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Digit(self.to_u64() & rhs.to_u64())
	}
}

impl BitOr for Digit {
	type Output = Self;

	fn bitor(self, rhs: Self) -> Self::Output {
		Digit(self.to_u64() | rhs.to_u64())
	}
}

impl BitXor for Digit {
	type Output = Self;

	fn bitxor(self, rhs: Self) -> Self::Output {
		Digit(self.to_u64() ^ rhs.to_u64())
	}
}

// ============================================================================
// Bitwise assign operations
// ============================================================================
impl BitAndAssign for Digit {
	fn bitand_assign(&mut self, rhs: Self) {
		self.0 &= rhs.to_u64()
	}
}

impl BitOrAssign for Digit {
	fn bitor_assign(&mut self, rhs: Self) {
		self.0 |= rhs.to_u64()
	}
}

impl BitXorAssign for Digit {
	fn bitxor_assign(&mut self, rhs: Self) {
		self.0 ^= rhs.to_u64()
	}
}
