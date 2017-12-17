
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

// ============================================================================

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

impl Width for ApInt {
	fn width(&self) -> BitWidth {
		BitWidth::new(self.len_bits()).unwrap()
	}
}

//  =======================================================================
///  Utility & Helper Methods
/// =======================================================================
impl ApInt {
	/// Returns the bit-width of this `ApInt` as `usize`.
	#[inline]
	pub(in apint) fn len_bits(&self) -> usize {
		self.len.to_usize()
	}

	/// Returns the number of digits used internally for value representation.
	/// 
	/// # Note
	/// 
	/// - This method should not be part of the public interface.
	/// - The returned values are valid for bit-block sizes of 32 bit.
	#[inline]
	pub(in apint) fn len_digits(&self) -> usize {
		self.len.required_digits()
	}

	#[inline]
	pub(in apint) fn storage(&self) -> Storage {
		self.len.storage()
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

	/// Returns a slice over the digits stored within this `ApInt`.
	/// 
	/// # Note
	/// 
	/// This might be less of a help when implementing algorithms since `Digit`
	/// does not have a proper knowledge of its actually used bits.
	/// Refer to `ComputeBlocks` instead which is returned by some iterators.
	pub(crate) fn as_digit_slice(&self) -> &[Digit] {
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

	/// Returns a slice over the mutable digits stored within this `ApInt`.
	/// 
	/// # Note
	/// 
	/// This might be less of a help when implementing algorithms since `Digit`
	/// does not have a proper knowledge of its actually used bits.
	/// Refer to `ComputeBlocks` instead which is returned by some iterators.
	pub(crate) fn as_digit_slice_mut(&mut self) -> &mut [Digit] {
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

	/// Returns a slice to the underlying bytes of the digits of this `ApInt`.
	pub(crate) fn digits_as_bytes(&self) -> &[u8] {
		use std::slice;
		use std::mem;
		match self.len.storage() {
			Storage::Inl => unsafe {
				slice::from_raw_parts(
					&self.data.inl as *const Digit as *const u8,
					mem::size_of::<Digit>()
				)
			},
			Storage::Ext => unsafe {
				slice::from_raw_parts(
					self.data.ext.as_ptr() as *const u8,
					self.len_digits() * mem::size_of::<Digit>()
				)
			}
		}
	}

	/// Returns a mutable slice to the underlying bytes of the digits of this `ApInt`.
	pub(crate) fn digits_as_bytes_mut(&mut self) -> &mut [u8] {
		use std::slice;
		use std::mem;
		match self.len.storage() {
			Storage::Inl => unsafe {
				slice::from_raw_parts_mut(
					&mut self.data.inl as *mut Digit as *mut u8,
					mem::size_of::<Digit>()
				)
			},
			Storage::Ext => unsafe {
				slice::from_raw_parts_mut(
					self.data.ext.as_ptr() as *mut u8,
					self.len_digits() * mem::size_of::<Digit>()
				)
			}
		}
	}

	/// Returns a reference to the internal `Block` that is representing the
	/// most significant bits of the represented value.
	/// 
	/// The `Block` is returned as a `ComputeBlock` that adds an associated bit-width to it.
	pub(in apint) fn most_significant_digit(&self) -> Digit {
		match self.model() {
			Model::Inl(small) => small.most_significant_digit(),
			Model::Ext(large) => large.most_significant_digit()
		}
	}

	pub(in apint) fn most_significant_digit_mut(&mut self) -> &mut Digit {
		match self.model_mut() {
			ModelMut::Inl(small) => small.into_most_significant_digit_mut(),
			ModelMut::Ext(large) => large.into_most_significant_digit_mut()
		}
	}

	/// Returns `true` if the most significant bit of the `ApInt` is set, `false` otherwise.
	pub(in apint) fn most_significant_bit(&self) -> Bit {
		match self.model() {
			Model::Inl(small) => small.most_significant_bit(),
			Model::Ext(large) => large.most_significant_bit()
		}
	}
}
