use apint::{ApInt};
use apint::utils::{ZipModelMut};
use traits::{ApIntMutImpl};
use errors::{Result};

/// Represents an amount of bits to shift a value like an `ApInt`.
/// 
/// The purpose of this type is to create a generic abstraction
/// over input types that may act as a `ShiftAmount` for shift
/// operations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShiftAmount(usize);

impl ShiftAmount {
	/// Returns the internal shift amount representation as `usize`.
	#[inline]
	pub(crate) fn to_usize(self) -> usize {
		self.0
	}
}

impl From<usize> for ShiftAmount {
	/// Returns a new `ShiftAmount` from the given `usize`.
	#[inline]
	fn from(val: usize) -> ShiftAmount {
		ShiftAmount(val)
	}
}

//  =======================================================================
///  Shift Operations
/// =======================================================================
impl ApInt {

	/// Creates a new `ApInt` that represents the result of this `ApInt` left-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_shl(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_shl_assign(other)?;
		Ok(cloned)
	}

	/// Left-shifts this `ApInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_shl_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.shl_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.shl_inplace(&right)
			}
		}
	}

	/// Creates a new `ApInt` that represents the result of this `ApInt` logically right-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_lshr(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_lshr_assign(other)?;
		Ok(cloned)
	}

	/// Logically right-shifts this `ApInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_lshr_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.lshr_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.lshr_inplace(&right)
			}
		}
	}

	/// Creates a new `ApInt` that represents the result of this `ApInt` arithmetically right-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_ashr(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_ashr_assign(other)?;
		Ok(cloned)
	}

	/// Arithmetically right-shifts this `ApInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_ashr_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.ashr_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.ashr_inplace(&right)
			}
		}
	}

}
