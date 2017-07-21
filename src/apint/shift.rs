use apint::{APInt};
use apint::utils::{ZipModelMut};
use traits::{APIntMutImpl};
use errors::{Result};

//  =======================================================================
///  Shift Operations
/// =======================================================================
impl APInt {

	/// Creates a new `APInt` that represents the result of this `APInt` left-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_shl(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_shl_assign(other)?;
		Ok(cloned)
	}

	/// Left-shifts this `APInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_shl_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.shl_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.shl_inplace(&right)
			}
		}
	}

	/// Creates a new `APInt` that represents the result of this `APInt` logically right-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_lshr(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_lshr_assign(other)?;
		Ok(cloned)
	}

	/// Logically right-shifts this `APInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_lshr_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.lshr_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.lshr_inplace(&right)
			}
		}
	}

	/// Creates a new `APInt` that represents the result of this `APInt` arithmetically right-shifted by the other one.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_ashr(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_ashr_assign(other)?;
		Ok(cloned)
	}

	/// Arithmetically right-shifts this `APInt` by the amount represented by `other`.
	/// 
	/// # Errors
	/// 
	/// - When `self` and `other` have different bit-widths.
	pub fn checked_ashr_assign(&mut self, other: &APInt) -> Result<()> {
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
