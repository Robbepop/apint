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

/// The type for the internal `Digit` representation.
/// 
/// Must be exactly half the size of `DoubleDigitRepr`.
type DigitRepr = u64;

/// The type for the internal `DoubleDigit` representation.
/// 
/// Must be exactly double the size of `DigitRepr`.
type DoubleDigitRepr = u128;

/// The amount of bits within a single `Digit`.
pub(crate) const BITS: usize = 64;

/// The `DoubleDigit` base offset.
pub(crate) const BASE: DoubleDigitRepr = 1 << BITS;

const REPR_ZEROS: DigitRepr = 0x0000_0000_0000_0000;
const REPR_ONES : DigitRepr = 0xFFFF_FFFF_FFFF_FFFF;

/// Represents the set or unset state of a bit within an `APInt`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bit {
	/// Unset, or `false` or `off` state.
	Unset = 0,
	/// Set, or `true` or `on` state.
	Set = 1
}

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

impl DoubleDigit {
	/// Returns the hi part of this `DoubleDigit` as `Digit`.
	#[inline]
	fn hi(self) -> Digit {
		Digit((self.0 >> BITS) as u64)
	}

	/// Returns the hi part of this `DoubleDigit` as `Digit`.
	#[inline]
	fn lo(self) -> Digit {
		Digit(self.0 as u64)
	}

	/// Returns the hi and lo parts of this `DoubleDigit` as `Digit` each.
	#[inline]
	fn hi_lo(self) -> (Digit, Digit) {
		(self.hi(), self.lo())
	}

	/// Returns a `DoubleDigit` from the given hi and lo raw `Digit` parts.
	#[inline]
	fn from_hi_lo(hi: Digit, lo: Digit) -> DoubleDigit {
		DoubleDigit(((hi.to_u64() as u128) << BITS) | (lo.to_u64() as u128))
	}
}

impl From<u64> for Digit {
	#[inline]
	fn from(val: u64) -> Digit {
		Digit::from_u64(val)
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct DigitAndCarry {
	digit: Digit,
	carry: Digit
}

impl DigitAndCarry {
	/// Creates a new `DigitAndCarry` from the given `Digit` a zero carry.
	#[inline]
	fn new(digit: Digit) -> DigitAndCarry {
		DigitAndCarry{digit, carry: Digit(0)}
	}
}

/// Add `a + b` with carry.
/// 
/// Returns the result (`a + b`) and the implied carry of the operation.
fn carry_add(a: Digit, b: DigitAndCarry) -> DigitAndCarry {
	let (hi, lo) = DoubleDigit(a.to_u128() + b.digit.to_u128() + b.carry.to_u128()).hi_lo();
	DigitAndCarry{
		digit: lo,
		carry: hi
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct DigitAndBorrow {
	digit: Digit,
	borrow: Digit
}

impl DigitAndBorrow {
	/// Creates a new `DigitAndBorrow` from the given `Digit` a zero borrow.
	#[inline]
	fn new(digit: Digit) -> DigitAndBorrow {
		DigitAndBorrow{digit, borrow: Digit(0)}
	}
}

/// Subtract `a - b` with borrow.
/// 
/// Returns the result (`a - b`) and the implied carry of the operation.
fn borrow_sub(a: Digit, b: DigitAndBorrow) -> DigitAndBorrow {
	let (hi, lo) = DoubleDigit(BASE + a.to_u128() - b.digit.to_u128() - b.borrow.to_u128()).hi_lo();

    //     hi * (base) + lo        ==    1 * (base) + ai - bi - borrow
    // =>  ai - bi - borrow < 0   <==>   hi == 0

	DigitAndBorrow{
		digit: lo,
		borrow: Digit((hi == Digit::zero()) as DigitRepr)
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

	/// Creates a digit that represents the value `0`.
	/// 
	/// **Note:** Equivalent to `Digit::zeros()`.
	#[inline]
	pub fn zero() -> Digit {
		Digit::from_u64(0)
	}

	/// Creates a digit where all bits are initialized to `0`.
	/// 
	/// **Note:** Equivalent to `Digit::zero()`.
	#[inline]
	pub fn zeros() -> Digit {
		Digit::from_u64(REPR_ZEROS)
	}

	/// Creates a digit where all bits are initialized to `1`.
	#[inline]
	pub fn ones() -> Digit {
		Digit::from_u64(REPR_ONES)
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

	/// Returns the internal representation as `u128` value.
	#[inline]
	pub fn to_u128(self) -> u128 { 
		self.to_u64() as u128
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
		Ok(self.0 &= REPR_ONES >> ((self::BITS as u64) - (bitwidth.to_usize() as u64)))
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
		self.0 |= REPR_ONES
	}

	/// Sets all bits in this digit to `0`.
	#[inline]
	pub fn unset_all(&mut self) {
		self.0 &= REPR_ZEROS
	}

	/// Flips all bits in this digit.
	#[inline]
	pub fn flip_all(&mut self) {
		self.0 ^= REPR_ONES
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
		Ok(self.0 |= !(REPR_ONES >> n))
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
		Ok(self.0 &= REPR_ONES >> (self::BITS - n))
	}

	/// Unsets all bits but the last `n` ones.
	/// 
	/// # Errors
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn retain_last_n(&mut self, n: usize) -> Result<()> {
		if n >= self::BITS {
			return Err(Error::invalid_bit_access(n, self::BITS))
		}
		Ok(self.0 &= !(REPR_ONES << n))
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

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn retain_last_n() {
		let mut d = Digit::from(0xFFFF_FFFF_FFFF_FFFF);
		d.retain_last_n(32).unwrap();
		assert_eq!(d, Digit::from(0x0000_0000_FFFF_FFFF));
	}
}
