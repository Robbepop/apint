use apint::{ApInt};
use digit::{Bit};
use digit;
use errors::{Result};
use apint::utils::{
	DataAccess,
	DataAccessMut,
	ZipDataAccessMut
};
use bitpos::{BitPos};
use traits::{Width};
use checks;

use std::ops::{
	BitAnd,
	BitOr,
	BitXor,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};

//  ===========================================================================
///  Bitwise Operations
/// ===========================================================================
impl ApInt {

	/// Flip all bits of this `ApInt` inplace.
	pub fn bitnot(&mut self) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => {
				digit.not_inplace()
			}
			DataAccessMut::Ext(digits) => {
				digits.into_iter()
				      .for_each(|digit| digit.not_inplace())
			}
		}
		self.clear_unused_bits();
	}

	/// Tries to bit-and assign this `ApInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitand`](struct.ApInt.html#method.checked_bitand).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitand(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_bitand_assign(rhs)?;
		Ok(this)
	}

	/// Bit-and assigns all bits of this `ApInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitand_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(lhs, rhs) => {
				*lhs &= rhs
			}
			ZipDataAccessMut::Ext(lhs, rhs) => {
				lhs.into_iter()
				   .zip(rhs.into_iter())
				   .for_each(|(l, r)| *l &= *r)
			}
		}
		Ok(())
	}

	/// Tries to bit-and assign this `ApInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitor`](struct.ApInt.html#method.checked_bitor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitor(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_bitor_assign(rhs)?;
		Ok(this)
	}

	/// Bit-or assigns all bits of this `ApInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitor_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(lhs, rhs) => {
				*lhs |= rhs
			}
			ZipDataAccessMut::Ext(lhs, rhs) => {
				lhs.into_iter()
				   .zip(rhs.into_iter())
				   .for_each(|(l, r)| *l |= *r)
			}
		}
		Ok(())
	}

	/// Tries to bit-xor assign this `ApInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitxor`](struct.ApInt.html#method.checked_bitxor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitxor(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_bitor_assign(rhs)?;
		Ok(this)
	}

	/// Bit-xor assigns all bits of this `ApInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitxor_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(lhs, rhs) => {
				*lhs ^= rhs
			}
			ZipDataAccessMut::Ext(lhs, rhs) => {
				lhs.into_iter()
				   .zip(rhs.into_iter())
				   .for_each(|(l, r)| *l ^= *r)
			}
		}
		Ok(())
	}
}

//  ===========================================================================
///  Bitwise Access
/// ===========================================================================
impl ApInt {
	/// Returns the bit at the given bit position `pos`.
	/// 
	/// This returns
	/// 
	/// - `Bit::Set` if the bit at `pos` is `1`
	/// - `Bit::Unset` otherwise
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `ApInt`.
	pub fn get_bit_at<P>(&self, pos: P) -> Result<Bit>
		where P: Into<BitPos>
	{
		let pos = pos.into();
		checks::verify_bit_access(self, pos)?;
		match self.access_data() {
			DataAccess::Inl(digit) => digit.get(pos),
			DataAccess::Ext(digits) => {
				let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
				digits[digit_pos].get(bit_pos)
			}
		}
	}

	/// Sets the bit at the given bit position `pos` to one (`1`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `ApInt`.
	pub fn set_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		let pos = pos.into();
		checks::verify_bit_access(self, pos)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.set(pos),
			DataAccessMut::Ext(digits) => {
				let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
				digits[digit_pos].set(bit_pos)
			}
		}
	}

	/// Sets the bit at the given bit position `pos` to zero (`0`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `ApInt`.
	pub fn unset_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		let pos = pos.into();
		checks::verify_bit_access(self, pos)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.unset(pos),
			DataAccessMut::Ext(digits) => {
				let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
				digits[digit_pos].unset(bit_pos)
			}
		}
	}

	/// Flips the bit at the given bit position `pos`.
	/// 
	/// # Note
	/// 
	/// - If the bit at the given position was `0` it will be `1`
	///   after this operation and vice versa.
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `ApInt`.
	pub fn flip_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		let pos = pos.into();
		checks::verify_bit_access(self, pos)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.flip(pos),
			DataAccessMut::Ext(digits) => {
				let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
				digits[digit_pos].flip(bit_pos)
			}
		}
	}

	/// Sets all bits of this `ApInt` to one (`1`).
	pub fn set_all(&mut self) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.set_all(),
			DataAccessMut::Ext(digits) => {
				digits.into_iter()
				      .for_each(|digit| digit.set_all())
			}
		}
	}

	/// Sets all bits of this `ApInt` to zero (`0`).
	pub fn unset_all(&mut self) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.unset_all(),
			DataAccessMut::Ext(digits) => {
				digits.into_iter()
				      .for_each(|digit| digit.unset_all())
			}
		}
	}

	/// Flips all bits of this `ApInt`.
	pub fn flip_all(&mut self) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit.flip_all(),
			DataAccessMut::Ext(digits) => {
				digits.into_iter()
				      .for_each(|digit| digit.flip_all())
			}
		}
	}

	/// Returns the sign bit of this `ApInt`.
	/// 
	/// **Note:** This is equal to the most significant bit of this `ApInt`.
	pub fn sign_bit(&self) -> Bit {
		self.most_significant_bit()
	}

	/// Sets the sign bit of this `ApInt` to one (`1`).
	pub fn set_sign_bit(&mut self) {
		let sign_bit_pos = self.width().sign_bit_pos();
		self.set_bit_at(sign_bit_pos)
		    .expect("`BitWidth::sign_bit_pos` always returns a valid `BitPos`
			         for usage in the associated `ApInt` for operating on bits.")
	}

	/// Sets the sign bit of this `ApInt` to zero (`0`).
	pub fn unset_sign_bit(&mut self) {
		let sign_bit_pos = self.width().sign_bit_pos();
		self.unset_bit_at(sign_bit_pos)
		    .expect("`BitWidth::sign_bit_pos` always returns a valid `BitPos`
			         for usage in the associated `ApInt` for operating on bits.")
	}

	/// Flips the sign bit of this `ApInt`.
	/// 
	/// # Note
	/// 
	/// - If the sign bit was `0` it will be `1` after this operation and vice versa.
	/// - Depending on the interpretation of the `ApInt` this
	///   operation changes its signedness.
	pub fn flip_sign_bit(&mut self) {
		let sign_bit_pos = self.width().sign_bit_pos();
		self.flip_bit_at(sign_bit_pos)
		    .expect("`BitWidth::sign_bit_pos` always returns a valid `BitPos`
			         for usage in the associated `ApInt` for operating on bits.")
	}
}

//  ===========================================================================
///  Bitwise utility methods.
/// ===========================================================================
impl ApInt {
	/// Returns the number of ones in the binary representation of this `ApInt`.
	pub fn count_ones(&self) -> usize {
		self.as_digit_slice()
		    .into_iter()
		    .map(|d| d.repr().count_ones() as usize)
		    .sum::<usize>()
	}

	/// Returns the number of zeros in the binary representation of this `ApInt`.
	pub fn count_zeros(&self) -> usize {
		let zeros = self.as_digit_slice()
			.into_iter()
		    .map(|d| d.repr().count_ones() as usize)
			.sum::<usize>();
		// Since `ApInt` instances with width's that are no powers of two
		// have unused excess bits that are always zero we need to cut them off
		// for a correct implementation of this operation.
		zeros - self.width().excess_bits().unwrap_or(0)
	}

	/// Returns the number of leading zeros in the binary representation of this `ApInt`.
	pub fn leading_zeros(&self) -> usize {
		let mut zeros = 0;
		for d in self.as_digit_slice().into_iter().rev() {
			let leading_zeros = d.repr().leading_zeros() as usize;
			zeros += leading_zeros;
			if leading_zeros != digit::BITS {
				break;
			}
		}
		zeros
	}

	/// Returns the number of trailing zeros in the binary representation of this `ApInt`.
	pub fn trailing_zeros(&self) -> usize {
		let mut zeros = 0;
		for d in self.as_digit_slice() {
			let trailing_zeros = d.repr().trailing_zeros() as usize;
			zeros += trailing_zeros;
			if trailing_zeros != digit::BITS {
				break;
			}
		}
		zeros
	}
}

//  ===========================================================================
//  `BitAnd` impls
//  ===========================================================================

impl<'a> BitAnd<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitOr` impls
//  ===========================================================================

impl<'a> BitOr<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitXor` impls
//  ===========================================================================

impl<'a> BitXor<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitAndAssign`, `BitOrAssign` and `BitXorAssign` impls
//  ===========================================================================

impl<'a> BitAndAssign<&'a ApInt> for ApInt {
    fn bitand_assign(&mut self, rhs: &'a ApInt) {
        self.checked_bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a ApInt> for ApInt {
    fn bitor_assign(&mut self, rhs: &'a ApInt) {
        self.checked_bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a ApInt> for ApInt {
    fn bitxor_assign(&mut self, rhs: &'a ApInt) {
        self.checked_bitxor_assign(rhs).unwrap();
    }
}
