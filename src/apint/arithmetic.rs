use apint::{ApInt};
use apint::utils::{ModelMut, ZipModelMut};
use traits::{ApIntMutImpl};
use errors::{Result};

use std::ops::{
	Neg,
	Add,
	Mul,
	AddAssign,
	MulAssign
};

impl Neg for ApInt {
	type Output = ApInt;

	fn neg(mut self) -> Self::Output {
		self.negate_inplace();
		self
	}
}

impl<'a> Add<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn add(mut self, rhs: &'a ApInt) -> Self::Output {
		self.checked_add_assign(rhs).unwrap();
		self
	}
}

impl<'a, 'b> Add<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn add(self, rhs: &'a ApInt) -> Self::Output {
		let mut cloned = self.clone();
		cloned.checked_add_assign(rhs).unwrap();
		cloned
	}
}

impl<'a> AddAssign<&'a ApInt> for ApInt {
	fn add_assign(&mut self, rhs: &'a ApInt) {
		self.checked_add_assign(rhs).unwrap();
	}
}

impl<'a> Mul<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn mul(mut self, rhs: &'a ApInt) -> Self::Output {
		self.checked_mul_assign(rhs).unwrap();
		self
	}
}

impl<'a, 'b> Mul<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn mul(self, rhs: &'a ApInt) -> Self::Output {
		let mut cloned = self.clone();
		cloned.checked_mul_assign(rhs).unwrap();
		cloned
	}
}

impl<'a> MulAssign<&'a ApInt> for ApInt {
	fn mul_assign(&mut self, rhs: &'a ApInt) {
		self.checked_mul_assign(rhs).unwrap();
	}
}

//  =======================================================================
///  Arithmetic Operations
/// =======================================================================
impl ApInt {

	/// Returns a new `ApInt` that represents the negation of this `ApInt`.
	/// 
	/// This may allocate heap memory!
	pub fn negate(&self) -> ApInt {
		let mut cloned = self.clone();
		cloned.negate_inplace();
		cloned
	}

	/// Negates this `ApInt` inplace as if it was a signed integer.
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

	/// Creates a new `ApInt` that represents the addition of both given `ApInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned addition of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_add(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_add_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_add_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.add_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.add_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the signed subtraction of both given `ApInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_sub(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_sub_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_sub_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.sub_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.sub_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the multiplication of both given `ApInt`s.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	pub fn checked_mul(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_mul_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_mul_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.mul_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.mul_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the unsigned multiplication of both given `ApInt`s.
	pub fn checked_udiv(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_udiv_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_udiv_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.udiv_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.udiv_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the signed multiplication of both given `ApInt`s.
	pub fn checked_sdiv(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_sdiv_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_sdiv_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.sdiv_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.sdiv_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the unsigned remainder of both given `ApInt`s.
	pub fn checked_urem(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_urem_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_urem_assign(&mut self, other: &ApInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut lhs, rhs) => {
				lhs.urem_inplace(&rhs)
			}
			ZipModelMut::Ext(mut lhs, rhs) => {
				lhs.urem_inplace(&rhs)
			}
		}
	}

	/// Creates a new `ApInt` that represents the signed remainder of both given `ApInt`s.
	pub fn checked_srem(&self, other: &ApInt) -> Result<ApInt> {
		let mut cloned = self.clone();
		cloned.checked_srem_assign(other)?;
		Ok(cloned)
	}

	pub fn checked_srem_assign(&mut self, other: &ApInt) -> Result<()> {
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
