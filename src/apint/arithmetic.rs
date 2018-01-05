use apint::{ApInt};
use apint::utils::{
	ZipDataAccessMut
};
use traits::{Width};
use errors::{Result};

use std::ops::{
	Neg,
	Add,
	Sub,
	Mul,
	AddAssign,
	SubAssign,
	MulAssign
};

//  =======================================================================
///  Arithmetic Operations
/// =======================================================================
impl ApInt {

	/// Negates this `ApInt` inplace and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn into_negate(self) -> ApInt {
		let mut this = self;
		this.negate();
		this
	}

	/// Negates this `ApInt` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn negate(&mut self) {
		let width = self.width();
		self.bitnot();
		// self.increment_by(1); // This is not implemented, yet.
									// Replace `self.checked_add_assign(..)` with this
									// as soon as possible for avoiding temporary
									// expensive copies of `self`.
		self.checked_add_assign(&ApInt::one(width))
			.expect("This operation cannot fail since the temporary `ApInt`\
						and `self` are ensured to always have the same bit width.");
		self.clear_unused_bits();
	}

	/// Adds `rhs` to `self` and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_add(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_add_assign(rhs)?;
		Ok(this)
	}

	/// Add-assigns `rhs` to `self` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_add_assign(&mut self, rhs: &ApInt) -> Result<()> {
		let width = self.width();
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(lhs, rhs) => {
				*lhs.repr_mut() += rhs.repr();
				if let Some(bits) = width.excess_bits() {
					lhs.retain_last_n(bits)
					     .expect("`width.excess_bits` will always return a number \
					              of bits that is compatible for use in a `Digit`.");
				}
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
		Ok(())
	}

	/// Subtracts `rhs` from `self` and returns the result.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_sub(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_add_assign(rhs)?;
		Ok(this)
	}

	/// Subtract-assigns `rhs` from `self` inplace.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_sub_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

	/// Subtracts `rhs` from `self` and returns the result.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_mul(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_mul_assign(rhs)?;
		Ok(this)
	}

	/// Multiply-assigns `rhs` to `self` inplace.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_mul_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

	/// Divides `self` by `rhs` using **unsigned** interpretation and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_udiv(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_udiv_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the division of `self` by `rhs` using **unsigned**
	/// interpretation of the values.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_udiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

	/// Divides `self` by `rhs` using **signed** interpretation and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_sdiv(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_sdiv_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the division of `self` by `rhs` using **signed**
	/// interpretation of the values.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_sdiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

	/// Calculates the **unsigned** remainder of `self` by `rhs` and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_urem(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_urem_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the **unsigned** remainder of `self` by `rhs`.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_urem_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

	/// Calculates the **signed** remainder of `self` by `rhs` and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_srem(self, rhs: &ApInt) -> Result<ApInt> {
		let mut this = self;
		this.checked_urem_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the **signed** remainder of `self` by `rhs`.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_srem_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			ZipDataAccessMut::Inl(_lhs, _rhs) => {
				unimplemented!()
			}
			ZipDataAccessMut::Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
	}

}

// ============================================================================
//  Standard `ops` trait implementations.
// ----------------------------------------------------------------------------
// 
//  `ApInt` implements some `std::ops` traits for improved usability.
//  Only traits for operations that do not depend on the signedness
//  interpretation of the specific `ApInt` instance are actually implemented.
//  Operations like `mul`, `div` and `rem` are not expected to have an
//  implementation since a favor in unsigned or signed cannot be decided.
// ============================================================================

// ============================================================================
//  Unary arithmetic negation: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl Neg for ApInt {
	type Output = ApInt;

	fn neg(self) -> Self::Output {
		self.into_negate()
	}
}

impl<'a> Neg for &'a ApInt {
	type Output = ApInt;

	fn neg(self) -> Self::Output {
		self.clone().into_negate()
	}
}

impl<'a> Neg for &'a mut ApInt {
	type Output = &'a mut ApInt;

	fn neg(self) -> Self::Output {
		self.negate();
		self
	}
}

// ============================================================================
//  Add and Add-Assign: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl<'a> Add<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn add(self, rhs: &'a ApInt) -> Self::Output {
		self.into_checked_add(rhs).unwrap()
	}
}

impl<'a, 'b> Add<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn add(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_checked_add(rhs).unwrap()
	}
}

impl<'a> AddAssign<&'a ApInt> for ApInt {
	fn add_assign(&mut self, rhs: &'a ApInt) {
		self.checked_add_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Sub and Sub-Assign: `std::ops::Sub` and `std::ops::SubAssign`
// ============================================================================

impl<'a> Sub<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn sub(self, rhs: &'a ApInt) -> Self::Output {
		self.into_checked_sub(rhs).unwrap()
	}
}

impl<'a, 'b> Sub<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn sub(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_checked_sub(rhs).unwrap()
	}
}

impl<'a> SubAssign<&'a ApInt> for ApInt {
	fn sub_assign(&mut self, rhs: &'a ApInt) {
		self.checked_sub_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Mul and Mul-Assign: `std::ops::Mul` and `std::ops::MulAssign`
// ============================================================================

impl<'a> Mul<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn mul(self, rhs: &'a ApInt) -> Self::Output {
		self.into_checked_mul(rhs).unwrap()
	}
}

impl<'a, 'b> Mul<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn mul(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_checked_mul(rhs).unwrap()
	}
}

impl<'a> MulAssign<&'a ApInt> for ApInt {
	fn mul_assign(&mut self, rhs: &'a ApInt) {
		self.checked_mul_assign(rhs).unwrap();
	}
}
