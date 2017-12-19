
use storage::{Storage};
use digit::{Digit, Bit};
use apint::{ApInt};
use small_apint::{SmallApInt, SmallApIntMut};
use large_apint::{LargeApInt, LargeApIntMut};
use errors::{Error, Result};
use traits::Width;
use bitwidth::BitWidth;
use small_apint::DigitWrapper;
use digit_seq::{
	AsDigitSeq,
	AsDigitSeqMut,
	ContiguousDigitSeq,
	ContiguousDigitSeqMut
};

use std::fmt;

impl fmt::Debug for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.model() {
			Model::Inl(small) => {
				f.debug_struct("ApInt")
					.field("len", &small.width())
					.field("digit", &small.digit())
					.finish()
			},
			Model::Ext(large) => {
				f.debug_struct("ApInt")
					.field("len", &large.width())
					.field("digits", &large.digits())
					.finish()
			}
		}
	}
}

// ============================================================================

impl<'a> AsDigitSeq<'a> for &'a ApInt {
	type Seq = ContiguousDigitSeq<'a>;

	fn digits(self) -> Self::Seq {
		match self.model() {
			Model::Inl(small) => small.digits(),
			Model::Ext(large) => large.digits()
		}
	}
}

impl<'a> AsDigitSeqMut<'a> for &'a mut ApInt {
	type SeqMut = ContiguousDigitSeqMut<'a>;

	fn digits_mut(self) -> Self::SeqMut {
		match self.model_mut() {
			ModelMut::Inl(small) => small.digits_mut(),
			ModelMut::Ext(large) => large.digits_mut()
		}
	}
}

// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Model<'a> {
	Inl(SmallApInt<'a>),
	Ext(LargeApInt<'a>)
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ModelMut<'a> {
	Inl(SmallApIntMut<'a>),
	Ext(LargeApIntMut<'a>)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ZipModel<'a, 'b> {
	Inl(SmallApInt<'a>, SmallApInt<'b>),
	Ext(LargeApInt<'a>, LargeApInt<'b>)
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ZipModelMut<'a, 'b> {
	Inl(SmallApIntMut<'a>, SmallApInt<'b>),
	Ext(LargeApIntMut<'a>, LargeApInt<'b>)
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

//  =======================================================================
///  Utility & Helper Methods
/// =======================================================================
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

	#[inline]
	pub(in apint) fn model(&self) -> Model {
		match self.storage() {
			Storage::Inl => Model::Inl(SmallApInt::new(self.len, unsafe{self.data.inl})),
			Storage::Ext => Model::Ext(LargeApInt::new(self.len, self.as_digit_slice()))
		}
	}

	#[inline]
	pub(in apint) fn model_mut(&mut self) -> ModelMut {
		match self.storage() {
			Storage::Inl => ModelMut::Inl(SmallApIntMut::new(self.len, unsafe{&mut self.data.inl})),
			Storage::Ext => ModelMut::Ext(LargeApIntMut::new(self.len, self.as_digit_slice_mut()))
		}
	}

	/// Zips both given `ApInt` instances to simplify access to their data.
	/// 
	/// # Errors
	/// 
	/// - If both given `ApInt` instances have non-matching bit widths.
	pub(in apint) fn zip_model<'a, 'b>(&'a self, other: &'b ApInt) -> Result<ZipModel<'a, 'b>> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits()).into()
		}
		Ok(match self.storage() {
			Storage::Inl => ZipModel::Inl(
				SmallApInt::new( self.len, unsafe{ self.data.inl}),
				SmallApInt::new(other.len, unsafe{other.data.inl})),
			Storage::Ext => ZipModel::Ext(
				LargeApInt::new( self.len,  self.as_digit_slice()),
				LargeApInt::new(other.len, other.as_digit_slice()))
		})
	}

	/// Mutably zips both given `ApInt` instances to simplify access to their data.
	/// 
	/// # Errors
	/// 
	/// - If both given `ApInt` instances have non-matching bit widths.
	pub(in apint) fn zip_model_mut<'a, 'b>(&'a mut self, other: &'b ApInt) -> Result<ZipModelMut<'a, 'b>> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits()).into()
		}
		Ok(match self.storage() {
			Storage::Inl => ZipModelMut::Inl(
				SmallApIntMut::new( self.len, unsafe{&mut  self.data.inl}),
				SmallApInt::new(other.len, unsafe{other.data.inl})),
			Storage::Ext => ZipModelMut::Ext(
				LargeApIntMut::new( self.len,  self.as_digit_slice_mut()),
				LargeApInt::new(other.len, other.as_digit_slice()))
		})
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
				digits.last().unwrap().clone()
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
		match self.access_data() {
			DataAccess::Inl(digit) => digit.most_significant_bit(),
			DataAccess::Ext(_) => {
				self.most_significant_digit().most_significant_bit()
			}
		}
	}

	/// Returns `Bit::Set` if the least significant bit of this `ApInt` is set
	/// and `Bit::Unset` otherwise.
	pub(in apint) fn least_significant_bit(&self) -> Bit {
		match self.access_data() {
			DataAccess::Inl(digit) => digit.least_significant_bit(),
			DataAccess::Ext(_) => {
				self.least_significant_digit().least_significant_bit()
			}
		}
	}
}
