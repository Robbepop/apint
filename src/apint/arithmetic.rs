use apint::{APInt};
use apint::utils::{ModelMut, ZipModelMut};
use traits::{APIntMutImpl};
use errors::{Result};

use std::ops::{
	Neg,
	Add,
	Mul,
	AddAssign,
	MulAssign
};

impl Neg for APInt {
	type Output = APInt;

	fn neg(mut self) -> Self::Output {
		self.negate_inplace();
		self
	}
}

impl<'a> Add<&'a APInt> for APInt {
	type Output = APInt;

	fn add(mut self, rhs: &'a APInt) -> Self::Output {
		self.checked_add_assign(rhs).unwrap();
		self
	}
}

impl<'a, 'b> Add<&'a APInt> for &'b APInt {
	type Output = APInt;

	fn add(self, rhs: &'a APInt) -> Self::Output {
		let mut cloned = self.clone();
		cloned.checked_add_assign(rhs).unwrap();
		cloned
	}
}

impl<'a> AddAssign<&'a APInt> for APInt {
	fn add_assign(&mut self, rhs: &'a APInt) {
		self.checked_add_assign(rhs).unwrap();
	}
}

impl<'a> Mul<&'a APInt> for APInt {
	type Output = APInt;

	fn mul(mut self, rhs: &'a APInt) -> Self::Output {
		self.checked_mul_assign(rhs).unwrap();
		self
	}
}

impl<'a, 'b> Mul<&'a APInt> for &'b APInt {
	type Output = APInt;

	fn mul(self, rhs: &'a APInt) -> Self::Output {
		let mut cloned = self.clone();
		cloned.checked_mul_assign(rhs).unwrap();
		cloned
	}
}

impl<'a> MulAssign<&'a APInt> for APInt {
	fn mul_assign(&mut self, rhs: &'a APInt) {
		self.checked_mul_assign(rhs).unwrap();
	}
}

//  =======================================================================
///  Arithmetic Operations
/// =======================================================================
impl APInt {

	/// Returns a new `APInt` that represents the negation of this `APInt`.
	/// 
	/// This may allocate heap memory!
	pub fn negate(&self) -> APInt {
		let mut cloned = self.clone();
		cloned.negate_inplace();
		cloned
	}

	/// Negates this `APInt` inplace as if it was a signed integer.
	/// 
	/// This does not allocate heap memory!
	pub fn negate_inplace(&mut self) {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.neg_inplace()
			}
			ModelMut::Ext(mut large) => {
				large.neg_inplace()
			}
		}
	}

	/// Creates a new `APInt` that represents the addition of both given `APInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned addition of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_add(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_add_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_add_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.add_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.add_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the signed subtraction of both given `APInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_sub(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_sub_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_sub_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.sub_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.sub_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the multiplication of both given `APInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_mul(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_mul_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_mul_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.mul_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.mul_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the unsigned multiplication of both given `APInt`s.
	pub fn checked_udiv(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_udiv_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_udiv_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.udiv_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.udiv_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the signed multiplication of both given `APInt`s.
	pub fn checked_sdiv(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_sdiv_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_sdiv_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.sdiv_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.sdiv_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the unsigned remainder of both given `APInt`s.
	pub fn checked_urem(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_urem_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_urem_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.urem_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.urem_inplace(&rhs)
			}
		}
	}

	/// Creates a new `APInt` that represents the signed remainder of both given `APInt`s.
	pub fn checked_srem(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_srem_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_srem_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.srem_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.srem_inplace(&rhs)
			}
		}
	}

}
