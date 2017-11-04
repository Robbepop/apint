use apint::{APInt};
use apint::utils::{Model, ModelMut, ZipModelMut};
use digit::{Bit};
use traits::{APIntImpl, APIntMutImpl};
use errors::{Result};

use std::ops::{
	BitAnd,
	BitOr,
	BitXor,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};

//  ===========================================================================

impl<'a> BitAnd<&'a APInt> for APInt {
    type Output = APInt;

    fn bitand(self, rhs: &'a APInt) -> Self::Output {
        self.checked_bitand(rhs).unwrap()
    }
}

impl<'a> BitOr<&'a APInt> for APInt {
    type Output = APInt;

    fn bitor(self, rhs: &'a APInt) -> Self::Output {
        self.checked_bitor(rhs).unwrap()
    }
}

impl<'a> BitXor<&'a APInt> for APInt {
    type Output = APInt;

    fn bitxor(self, rhs: &'a APInt) -> Self::Output {
        self.checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a APInt> for &'b APInt {
    type Output = APInt;

    fn bitand(self, rhs: &'a APInt) -> Self::Output {
        self.clone().checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a APInt> for &'b APInt {
    type Output = APInt;

    fn bitor(self, rhs: &'a APInt) -> Self::Output {
        self.clone().checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a APInt> for &'b APInt {
    type Output = APInt;

    fn bitxor(self, rhs: &'a APInt) -> Self::Output {
        self.clone().checked_bitxor(rhs).unwrap()
    }
}

//  ===========================================================================

impl<'a> BitAndAssign<&'a APInt> for APInt {
    fn bitand_assign(&mut self, rhs: &'a APInt) {
        self.checked_bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a APInt> for APInt {
    fn bitor_assign(&mut self, rhs: &'a APInt) {
        self.checked_bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a APInt> for APInt {
    fn bitxor_assign(&mut self, rhs: &'a APInt) {
        self.checked_bitxor_assign(rhs).unwrap();
    }
}

//  ===========================================================================
///  Bitwise Operations
/// ===========================================================================
impl APInt {

	/// Creates a new bitvev that represents the bitwise-not of the given `APInt`.
	pub fn bitnot(&self) -> APInt {
		let mut cloned = self.clone();
		cloned.bitnot_inplace();
		cloned
	}

	/// Flip all bits of the given `APInt` inplace.
	/// 
	/// This operation operates in-place on `self` and thus does not require dynamic memory allocation.
	pub fn bitnot_inplace(&mut self) {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.bitnot_inplace()
			}
			ModelMut::Ext(mut large) => {
				large.bitnot_inplace()
			}
		}
	}

	/// Creates a new bitvec that represents the bitwise-and of both given `APInt`s.
	pub fn checked_bitand(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_bitand_assign(other)?;
		Ok(cloned)
	}

	/// Computes bitwise-and of self and other and stores the result in self.
	/// 
	/// This operation operates in-place on `self` and thus does not require dynamic memory allocation.
	pub fn checked_bitand_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.bitand_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.bitand_inplace(&right)
			}
		}
	}

	/// Creates a new bitvec that represents the bitwise-or of both given `APInt`s.
	pub fn checked_bitor(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_bitor_assign(other)?;
		Ok(cloned)
	}

	/// Computes bitwise-or of self and other and stores the result in self.
	/// 
	/// This operation operates in-place on `self` and thus does not require dynamic memory allocation.
	pub fn checked_bitor_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.bitor_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.bitor_inplace(&right)
			}
		}
	}

	/// Creates a new bitvec that represents the bitwise-xor of both given `APInt`s.
	pub fn checked_bitxor(&self, other: &APInt) -> Result<APInt> {
		let mut cloned = self.clone();
		cloned.checked_bitxor_assign(other)?;
		Ok(cloned)
	}

	/// Computes bitwise-xor of self and other and stores the result in self.
	/// 
	/// This operation operates in-place on `self` and thus does not require dynamic memory allocation.
	pub fn checked_bitxor_assign(&mut self, other: &APInt) -> Result<()> {
		match self.zip_model_mut(other)? {
			ZipModelMut::Inl(mut left, right) => {
				left.bitxor_inplace(&right)
			}
			ZipModelMut::Ext(mut left, right) => {
				left.bitxor_inplace(&right)
			}
		}
	}
}

//  ===========================================================================
///  Bitwise Access
/// ===========================================================================
impl APInt {
	pub fn get(&self, n: usize) -> Result<Bit> {
		match self.model() {
			Model::Inl(small) => {
				small.get(n)
			}
			Model::Ext(large) => {
				large.get(n)
			}
		}
	}

	pub fn sign_bit(&self) -> Bit {
		match self.model() {
			Model::Inl(small) => {
				small.sign_bit()
			}
			Model::Ext(large) => {
				large.sign_bit()
			}
		}
	}

	pub fn set(&mut self, n: usize) -> Result<()> {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.set(n)
			}
			ModelMut::Ext(mut large) => {
				large.set(n)
			}
		}
	}

	pub fn set_all(&mut self) {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.set_all()
			}
			ModelMut::Ext(mut large) => {
				large.set_all()
			}
		}
	}

	pub fn unset(&mut self, n: usize) -> Result<()> {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.unset(n)
			}
			ModelMut::Ext(mut large) => {
				large.unset(n)
			}
		}
	}

	pub fn unset_all(&mut self) {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.unset_all()
			}
			ModelMut::Ext(mut large) => {
				large.unset_all()
			}
		}
	}

	pub fn flip(&mut self, n: usize) -> Result<()> {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.flip(n)
			}
			ModelMut::Ext(mut large) => {
				large.flip(n)
			}
		}
	}

	pub fn flip_all(&mut self) {
		match self.model_mut() {
			ModelMut::Inl(mut small) => {
				small.flip_all()
			}
			ModelMut::Ext(mut large) => {
				large.flip_all()
			}
		}
	}
}
