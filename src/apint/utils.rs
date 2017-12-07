
use storage::{Storage};
use digit::{Digit};
use apint::{ApInt};
use small_apint::{SmallApInt, SmallApIntMut};
use large_apint::{LargeApInt, LargeApIntMut};
use errors::{Error, Result};

use std::fmt;

impl fmt::Debug for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.model() {
			Model::Inl(small) => small.fmt(f),
			Model::Ext(large) => large.fmt(f)
		}
	}
}

// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Model<'a> {
	Inl(SmallApInt),
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
	Inl(SmallApInt, SmallApInt),
	Ext(LargeApInt<'a>, LargeApInt<'b>)
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ZipModelMut<'a, 'b> {
	Inl(SmallApIntMut<'a>, SmallApInt),
	Ext(LargeApIntMut<'a>, LargeApInt<'b>)
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
		self.len.required_blocks()
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

	/// Returns a reference to the internal `Block` that is representing the
	/// most significant bits of the represented value.
	/// 
	/// The `Block` is returned as a `ComputeBlock` that adds an associated bit-width to it.
	pub(in apint) fn most_significant_digit(&self) -> Digit {
		unimplemented!()
	}

	/// Returns `true` if the most significant bit of the `ApInt` is set, `false` otherwise.
	pub(in apint) fn most_significant_bit(&self) -> bool {
		unimplemented!()
	}

}
