
use storage::{Storage};
use digit::{Digit, Bit};
use apint::{ApInt};
use errors::{Error, Result};
use traits::Width;
use bitwidth::BitWidth;
use digit_seq::{
	AsDigitSeq,
	AsDigitSeqMut,
	ContiguousDigitSeq,
	ContiguousDigitSeqMut
};

use std::fmt;

impl fmt::Debug for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("ApInt")
		 .field("len", &self.width())
		 .field("digits", &self.as_digit_slice())
		 .finish()
	}
}

// ============================================================================

impl<'a> AsDigitSeq<'a> for &'a ApInt {
	type Seq = ContiguousDigitSeq<'a>;

	fn digits(self) -> Self::Seq {
		ContiguousDigitSeq::from(self.as_digit_slice())
	}
}

impl<'a> AsDigitSeqMut<'a> for &'a mut ApInt {
	type SeqMut = ContiguousDigitSeqMut<'a>;

	fn digits_mut(self) -> Self::SeqMut {
		ContiguousDigitSeqMut::from(self.as_digit_slice_mut())
	}
}

// ============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum DataAccess<'a> {
	Inl(Digit),
	Ext(&'a [Digit])
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DataAccessMut<'a> {
	Inl(&'a mut Digit),
	Ext(&'a mut [Digit])
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum ZipDataAccess<'a, 'b> {
	Inl(Digit, Digit),
	Ext(&'a [Digit], &'b [Digit])
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ZipDataAccessMut<'a, 'b> {
	Inl(&'a mut Digit, Digit),
	Ext(&'a mut [Digit], &'b [Digit])
}

// ============================================================================

impl Width for ApInt {
	/// Returns the `BitWidth` of this `ApInt`.
	#[inline]
	fn width(&self) -> BitWidth {
		BitWidth::new(self.len_bits()).unwrap()
	}
}

//  ===========================================================================
///  Utility & Helper Methods
/// ===========================================================================
impl ApInt {
	/// Returns the number of bits of the bit width of this `ApInt`.
	#[inline]
	pub(in apint) fn len_bits(&self) -> usize {
		self.len.to_usize()
	}

	/// Returns the number of digits used internally for the value
	/// representation of this `ApInt`.
	#[inline]
	pub(in apint) fn len_digits(&self) -> usize {
		self.len.required_digits()
	}

	/// Returns the storage specifier of this `ApInt`.
	/// 
	/// This is `Storage::Inl` for `ApInt` instances that can be stored
	/// entirely on the stack and `Storage::Ext` otherwise.
	#[inline]
	pub(in apint) fn storage(&self) -> Storage {
		self.len.storage()
	}

	/// Accesses the internal `Digit` data of this `ApInt` in a safe way.
	#[inline]
	pub(in apint) fn access_data(&self) -> DataAccess {
		match self.storage() {
			Storage::Inl => DataAccess::Inl(unsafe{self.data.inl}),
			Storage::Ext => DataAccess::Ext(self.as_digit_slice())
		}
	}

	/// Mutably accesses the internal `Digit` data of this `ApInt` in a safe way.
	#[inline]
	pub(in apint) fn access_data_mut(&mut self) -> DataAccessMut {
		match self.storage() {
			Storage::Inl => DataAccessMut::Inl(unsafe{&mut self.data.inl}),
			Storage::Ext => DataAccessMut::Ext(self.as_digit_slice_mut())
		}
	}

	/// Zips both given `ApInt` instances and tries to access their data in a safe way.
	/// 
	/// # Errors
	/// 
	/// - If both given `ApInt` instances have non-matching bit widths.
	pub(in apint) fn zip_access_data<'a, 'b>(&'a self, other: &'b ApInt) -> Result<ZipDataAccess<'a, 'b>> {
		if self.width() != other.width() {
			return Error::unmatching_bitwidths(self.width(), other.width()).into()
		}
		Ok(match self.storage() {
			Storage::Inl => {
				ZipDataAccess::Inl(
					unsafe{ self.data.inl},
					unsafe{other.data.inl})
			},
			Storage::Ext => {
				ZipDataAccess::Ext(
					self.as_digit_slice(),
					other.as_digit_slice())
			}
		})
	}

	/// Zips both given `ApInt` instances and tries to mutably access their data in a safe way.
	/// 
	/// # Errors
	/// 
	/// - If both given `ApInt` instances have non-matching bit widths.
	pub(in apint) fn zip_access_data_mut<'a, 'b>(&'a mut self, other: &'b ApInt) -> Result<ZipDataAccessMut<'a, 'b>> {
		if self.width() != other.width() {
			return Error::unmatching_bitwidths(self.width(), other.width()).into()
		}
		Ok(match self.storage() {
			Storage::Inl => {
				ZipDataAccessMut::Inl(
					unsafe{&mut self.data.inl},
					unsafe{other.data.inl})
			},
			Storage::Ext => {
				ZipDataAccessMut::Ext(
					self.as_digit_slice_mut(),
					other.as_digit_slice())
			}
		})
	}

	/// Computes the given operation on all digits of this `ApInt`.
	/// 
	/// # Note
	/// 
	/// Prefer this utility method if you want to perform the same
	/// operation for all digits within this `ApInt` as this operation
	/// uses the most efficient way to do so.
	pub(in apint) fn modify_digits<F>(&mut self, f: F)
		where F: Fn(&mut Digit)
	{
		use self::DataAccessMut::*;
		match self.access_data_mut() {
			Inl(digit) => f(digit),
			Ext(digits) => {
				for digit in digits {
					f(digit)
				}
			}
		}
	}

	/// Computes the given operation on all digits of this `ApInt`
	/// zipped with the digits of `rhs`.
	/// 
	/// # Note
	/// 
	/// Prefer this utility method for these use cases since this operation
	/// uses the most efficient way to perform the specified task.
	pub(in apint) fn modify_zipped_digits<F>(&mut self, rhs: &ApInt, f: F) -> Result<()>
		where F: Fn(&mut Digit, Digit)
	{
		use self::ZipDataAccessMut::*;
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => f(lhs, rhs),
			Ext(lhs, rhs) => {
				for (l, &r) in lhs.into_iter().zip(rhs) {
					f(l, r)
				}
			}
		}
		Ok(())
	}

	/// Returns a slice over the `Digit`s of this `ApInt` in little-endian order.
	pub(in apint) fn as_digit_slice(&self) -> &[Digit] {
		use std::slice;
		match self.len.storage() {
			Storage::Inl => unsafe {
				slice::from_raw_parts(&self.data.inl, 1)
			},
			Storage::Ext => unsafe {
				slice::from_raw_parts(self.data.ext.as_ptr(), self.len_digits())
			}
		}
	}

	/// Returns a mutable slice over the `Digit`s of this `ApInt` in little-endian order.
	pub(in apint) fn as_digit_slice_mut(&mut self) -> &mut [Digit] {
		use std::slice;
		match self.len.storage() {
			Storage::Inl => unsafe {
				slice::from_raw_parts_mut(&mut self.data.inl, 1)
			},
			Storage::Ext => unsafe {
				slice::from_raw_parts_mut(self.data.ext.as_ptr(), self.len_digits())
			}
		}
	}

	/// Returns the most significant `Digit` of this `ApInt`.
	pub(in apint) fn most_significant_digit(&self) -> Digit {
		match self.access_data() {
			DataAccess::Inl(digit) => digit,
			DataAccess::Ext(digits) => {
				*digits.last().unwrap()
			}
		}
	}

	/// Returns a mutable reference to the most significant `Digit` of this `ApInt`.
	pub(in apint) fn most_significant_digit_mut(&mut self) -> &mut Digit {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit,
			DataAccessMut::Ext(digits) => {
				digits.last_mut().unwrap()
			}
		}
	}

	/// Returns the least significant `Digit` of this `ApInt`.
	pub(in apint) fn least_significant_digit(&self) -> Digit {
		match self.access_data() {
			DataAccess::Inl(digit) => digit,
			DataAccess::Ext(digits) => digits[0]
		}
	}

	/// Returns a mutable reference to the least significant `Digit` of this `ApInt`.
	pub(in apint) fn least_significant_digit_mut(&mut self) -> &mut Digit {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => digit,
			DataAccessMut::Ext(digits) => {
				digits.first_mut().unwrap()
			}
		}
	}

	/// Returns `Bit::Set` if the most significant bit of this `ApInt` is set
	/// and `Bit::Unset` otherwise.
	pub(in apint) fn most_significant_bit(&self) -> Bit {
		let sign_bit_pos = self.width().sign_bit_pos();
		self.most_significant_digit()
			.get(sign_bit_pos.to_pos_within_digit())
			.expect("`BitWidth::excess_bits` returns a number that \
						is always a valid `BitPos` for a `Digit` so this \
						operation cannot fail.")
	}

	/// Returns `Bit::Set` if the least significant bit of this `ApInt` is set
	/// and `Bit::Unset` otherwise.
	pub(in apint) fn least_significant_bit(&self) -> Bit {
		self.least_significant_digit().least_significant_bit()
	}

	/// Clears unused bits of this `ApInt`.
	/// 
	/// # Example
	/// 
	/// An `ApInt` with a `BitWidth` of `100` bits requires
	/// 2 `Digit`s for its internal value representation,
	/// each having 64-bits which totals in `128` bits for the
	/// `ApInt` instance.
	/// So upon a call to `ApInt::clear_unused_bits` the upper
	/// `128-100 = 28` bits are cleared (set to zero (`0`)).
	pub(in apint) fn clear_unused_bits(&mut self) {
		if let Some(bits) = self.width().excess_bits() {
			self.most_significant_digit_mut()
			    .retain_last_n(bits)
			    .expect("`BitWidth::excess_bits` always returns a number of \
				         bits that can safely forwarded to `Digit::retain_last_n`.");
		}
	}

	/// Returns `true` if this `ApInt` represents the value zero (`0`).
	/// 
	/// # Note
	/// 
	/// - Zero (`0`) is also called the additive neutral element.
	/// - This operation is more efficient than comparing two instances
	///   of `ApInt` for the same reason.
	pub fn is_zero(&self) -> bool {
		match self.access_data() {
			DataAccess::Inl(digit) => digit.is_zero(),
			DataAccess::Ext(digits) => {
				digits.into_iter().all(|digit| digit.is_zero())
			}
		}
	}

	/// Returns `true` if this `ApInt` represents the value one (`1`).
	/// 
	/// # Note
	/// 
	/// - One (`1`) is also called the multiplicative neutral element.
	/// - This operation is more efficient than comparing two instances
	///   of `ApInt` for the same reason.
	pub fn is_one(&self) -> bool {
		match self.access_data() {
			DataAccess::Inl(digit) => digit == Digit::one(),
			DataAccess::Ext(digits) => {
				let (last, rest) = digits.split_last()
					.expect("An `ApInt` always has at least one digit so calling \
					         `split_last` on a slice of its digits will never \
					         return `None`.");
				last.is_one() && rest.into_iter().all(|digit| digit.is_zero())
			}
		}
	}

	/// Returns `true` if this `ApInt` represents an even number.
	#[inline]
	pub fn is_even(&self) -> bool {
		self.least_significant_bit() == Bit::Unset
	}

	/// Returns `true` if this `ApInt` represents an odd number.
	#[inline]
	pub fn is_odd(&self) -> bool {
		self.least_significant_bit() == Bit::Set
	}

	/// Splits the least significant digits from the rest of the digit slice
	/// and returns it as well as the remaining part of the digit slice.
	pub(in apint) fn split_least_significant_digit(&self) -> (Digit, &[Digit]) {
		match self.access_data() {
			DataAccess::Inl(digit) => (digit, &[]),
			DataAccess::Ext(digits) => {
				let (lsd, rest) = digits.split_first()
					.expect("An `ApInt` always has at least one digit so calling \
					         `split_first` on a slice of its digits will never \
					         return `None`.");
				(*lsd, rest)
			}
		}
	}

	/// Splits the least significant digits from the rest of the digit slice
	/// and returns it as well as the remaining part of the digit slice.
	pub(in apint) fn split_least_significant_digit_mut(&mut self) -> (&mut Digit, &mut [Digit]) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => (digit, &mut []),
			DataAccessMut::Ext(digits) => {
				digits.split_first_mut()
					.expect("An `ApInt` always has at least one digit so calling \
					         `split_first_mut` on a slice of its digits will never \
					         return `None`.")
			}
		}
	}

	/// Splits the most significant digits from the rest of the digit slice
	/// and returns it as well as the remaining part of the digit slice.
	pub(in apint) fn split_most_significant_digit(&self) -> (Digit, &[Digit]) {
		match self.access_data() {
			DataAccess::Inl(digit) => (digit, &[]),
			DataAccess::Ext(digits) => {
				let (lsd, rest) = digits.split_last()
					.expect("An `ApInt` always has at least one digit so calling \
					         `split_last` on a slice of its digits will never \
					         return `None`.");
				(*lsd, rest)
			}
		}
	}

	/// Splits the most significant digits from the rest of the digit slice
	/// and returns it as well as the remaining part of the digit slice.
	pub(in apint) fn split_most_significant_digit_mut(&mut self) -> (&mut Digit, &mut [Digit]) {
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => (digit, &mut []),
			DataAccessMut::Ext(digits) => {
				digits.split_last_mut()
					.expect("An `ApInt` always has at least one digit so calling \
					         `split_last_mut` on a slice of its digits will never \
					         return `None`.")
			}
		}
	}

}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn most_significant_bit() {
		assert_eq!(Bit::Unset,
			ApInt::from_bit(false).most_significant_bit());
		assert_eq!(Bit::Set,
			ApInt::from_bit(true).most_significant_bit());
		assert_eq!(Bit::Unset,
			ApInt::from_u8(0b0101_0101).most_significant_bit());
		assert_eq!(Bit::Set,
			ApInt::from_u8(0b1101_0101).most_significant_bit());
		assert_eq!(Bit::Unset,
			ApInt::from_u16(0b0111_1000_1101_0101).most_significant_bit());
		assert_eq!(Bit::Set,
			ApInt::from_u16(0b1011_0001_0101_0101).most_significant_bit());
		assert_eq!(Bit::Unset,
			ApInt::from_u32(0x7000_0000).most_significant_bit());
		assert_eq!(Bit::Set,
			ApInt::from_u32(0x8000_0000).most_significant_bit());
		assert_eq!(Bit::Unset,
			ApInt::from_u64(0x70FC_A875_4321_1234).most_significant_bit());
		assert_eq!(Bit::Set,
			ApInt::from_u64(0x8765_4321_5555_6666).most_significant_bit());
	}
}
