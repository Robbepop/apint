use apint::{ApInt};
use apint::utils::DataAccessMut;
use apint::utils::ZipDataAccessMut::{Inl, Ext};
use traits::{Width};
use errors::{DivOp, Error, Result};
use digit::{Digit, DoubleDigit, DigitRepr};
use ll;
use utils::{try_forward_bin_mut_impl, forward_mut_impl};

use std::ops::{
	Neg,
	Add,
	Sub,
	Mul,
	AddAssign,
	SubAssign,
	MulAssign
};

/// # Arithmetic Operations
impl ApInt {

	/// Increments this `ApInt` by one inplace and returns the result
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn into_wrapping_inc(self) -> ApInt {
		forward_mut_impl(self, ApInt::wrapping_inc)
	}

	/// Increments this `ApInt` by one inplace and returns the result
	/// 
	/// **Note:** This will **not** allocate memory
	pub fn wrapping_inc(&mut self) {
		match self.access_data_mut() {
			DataAccessMut::Inl(x) => {
				*x = x.wrapping_add(Digit::one());
			}
			DataAccessMut::Ext(x) => {
				for i in 0..x.len() {
					match x[i].repr().overflowing_add(1) {
						(v,false) => {
							x[i] = Digit(v);
							break;
						}
						(v,true) => {
							//if the ApInt was relatively random this should rarely happen
							x[i] = Digit(v);
						}
					}
				}
			}
		}
		self.clear_unused_bits();
	}

	/// Negates this `ApInt` inplace and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn into_wrapping_neg(self) -> ApInt {
		forward_mut_impl(self, ApInt::wrapping_neg)
	}

	/// Negates this `ApInt` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn wrapping_neg(&mut self) {
		self.bitnot();
		self.wrapping_inc();
		//`wrapping_inc` handles clearing the unused bits
	}

	/// Adds `rhs` to `self` and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_wrapping_add(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_add_assign)
	}

	/// Add-assigns `rhs` to `self` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn wrapping_add_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let lval = lhs.repr();
				let rval = rhs.repr();
				let result = lval.wrapping_add(rval);
				*lhs = Digit(result);
			}
			Ext(lhs, rhs) => {
				let mut carry = Digit::zero();
				for (l, r) in lhs.into_iter().zip(rhs) {
					*l = ll::carry_add(*l, *r, &mut carry);
				}
			}
		}
		self.clear_unused_bits();
		// Maybe we should return a recoverable error upon carry != 0 at this point.
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
	pub fn into_wrapping_sub(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sub_assign)
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
	pub fn wrapping_sub_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let lval = lhs.repr();
				let rval = rhs.repr();
				let result = lval.wrapping_sub(rval);
				*lhs = Digit(result);
			}
			Ext(lhs, rhs) => {
				let mut borrow = Digit::zero();
				for (l, r) in lhs.into_iter().zip(rhs) {
					*l = ll::borrow_sub(*l, *r, &mut borrow);
				}
			}
		}
		self.clear_unused_bits();
		// Maybe we should return a recoverable error upon borrow != 0 at this point.
		Ok(())
	}

	/// Multiplies `rhs` with `self` and returns the result.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_wrapping_mul(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_mul_assign)
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
	/// 
	/// # Performance
	/// 
	/// If the function detects a large string of zeros in front of the most significant 1 bit,
	/// it will apply optimizations so that wasted multiplications and additions of zero are avoided.
	/// This function is designed to efficiently handle 5 common kinds of multiplication.
	/// Small here means both small ApInt size and/or small numerical significance 
	/// 	- multiplication of zero by any size integer (no allocation)
	/// 	- multiplication of small (<= 64 bits) integers (no allocation)
	/// 	- wrapping multiplication of medium size (<= 512 bits) integers
	/// 	- multiplication of medium size integers that will not overflow
	/// 	- multiplication of small integers by large integers
	/// 	  (or large integers multiplied by small integers) (no allocation)
	/// Currently, Karatsuba multiplication is not implemented, so large integer multiplication 
	/// may be very slow compared to other algorithms.
	pub fn wrapping_mul_assign(&mut self, rhs: &ApInt) -> Result<()> {
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				*lhs = lhs.wrapping_mul(rhs);
			}
			//NOTE: this part assumes that an Ext ApInt will always have at least 2 digits
			Ext(lhs, rhs) => {
				//wrapping long multiplication, in the future we could have karatsuba multiplication for larger ints (wikipedia says 320-640 bits is about where karatsuba multiplication algorithms become faster)

				//finds the most significant nonzero digit (for later optimizations) and handles early return of multiplication by zero.

				let rhs_sig_nonzero: usize = match rhs.iter().rposition(|x| x != &Digit::zero()) {
					Some(x) => x,
					None => {
						for x in lhs.iter_mut() {
							x.unset_all()
						}
						return Ok(());
					}
				};
				let lhs_sig_nonzero: usize = match lhs.iter().rposition(|x| x != &Digit::zero()) {
					Some(x) => x,
					None => {
						for x in lhs.iter_mut() {
							x.unset_all()
						}
						return Ok(());
					}
				};
				//for several routines below there was a nested loop that had its first and last iterations unrolled (and the unrolled loops had their first and last iterations unrolled), and then some if statements are added for overflow checks.
				//This is done because the compiler probably cannot properly unroll the carry system, overflow system, and figure out that only digit multiplications were needed instead of doubledigit mults in some places.
				match (lhs_sig_nonzero == 0, rhs_sig_nonzero == 0) {
					(false, false) => {
						if lhs_sig_nonzero + rhs_sig_nonzero + 2 <= lhs.len() {
							//no possibility of overflow
							//first digit of first row
							let mult = lhs[0];
							let temp = mult.carrying_mul(rhs[0]);
							//middle digits of first row
							//the goal here with `sum` is to allocate and initialize it only once here.
							let mut sum = Vec::with_capacity(lhs_sig_nonzero + rhs_sig_nonzero + 2);
							sum.push(temp.0);
							let mut mul_carry = temp.1;
							for rhs_i in 1..rhs_sig_nonzero {
								let temp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
								sum.push(temp.0);
								mul_carry = temp.1;
							}
							let temp = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
							sum.push(temp.0);
							sum.push(temp.1);
							//middle rows
							for lhs_i in 1..lhs_sig_nonzero {
								let mult = lhs[lhs_i];
								//first digit of this row
								let temp0 = mult.carrying_mul(rhs[0]);
								let mut mul_carry = temp0.1;
								let temp1 = sum[lhs_i].carrying_add(temp0.0);
								sum[lhs_i] = temp1.0;
								let mut add_carry = temp1.1;
								//middle digits of this row
								for rhs_i in 1..rhs_sig_nonzero {
									let temp0 = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
									mul_carry = temp0.1;
									let temp1: DoubleDigit = sum[lhs_i + rhs_i]
										.dd()
										.wrapping_add(temp0.0.dd())
										.wrapping_add(add_carry.dd());
									sum[lhs_i + rhs_i] = temp1.lo();
									add_carry = temp1.hi();
								}
								//final digits of this row
								let temp0 = mult.carrying_mul_add(rhs[rhs_sig_nonzero],mul_carry);
								let temp1: DoubleDigit = sum[lhs_i + rhs_sig_nonzero]
									.dd()
									.wrapping_add(temp0.0.dd())
									.wrapping_add(add_carry.dd());
								sum[lhs_i + rhs_sig_nonzero] = temp1.lo();
								sum.push(temp1.hi().wrapping_add(temp0.1));
							}
							let mult = lhs[lhs_sig_nonzero];
							//first digit of final row
							let temp0 = mult.carrying_mul(rhs[0]);
							let mut mul_carry = temp0.1;
							let temp1 = sum[lhs_sig_nonzero].carrying_add(temp0.0);
							sum[lhs_sig_nonzero] = temp1.0;
							let mut add_carry = temp1.1;
							//middle digits of final row
							println!("{:?}",sum);
							for rhs_i in 1..rhs_sig_nonzero {
								let temp0 = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
								mul_carry = temp0.1;
								let temp1: DoubleDigit = sum[lhs_sig_nonzero + rhs_i]
									.dd()
									.wrapping_add(temp0.0.dd())
									.wrapping_add(add_carry.dd());
								sum[lhs_sig_nonzero + rhs_i] = temp1.lo();
								add_carry = temp1.hi();
							}
							let temp0 = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
							let temp1: DoubleDigit = sum[lhs_sig_nonzero + rhs_sig_nonzero]
								.dd()
								.wrapping_add(temp0.0.dd())
								.wrapping_add(add_carry.dd());
							sum[lhs_sig_nonzero + rhs_sig_nonzero] = temp1.lo();
							sum.push(temp1.hi().wrapping_add(temp0.1));
							for i in 0..sum.len() {
								lhs[i] = sum[i];
							}
							return Ok(())
						} else {
							//wrapping (modular) multiplication
							let sig_nonzero = lhs.len() - 1;
							//first digit done and carry
							let temp = lhs[0].carrying_mul(rhs[0]);
							//the goal here with `sum` is to allocate and initialize it only once here.
							//first row
							let mut sum = Vec::with_capacity(lhs.len());
							sum.push(temp.0);
							let mut mul_carry = temp.1;
							for rhs_i in 1..sig_nonzero {
								let temp = lhs[0].carrying_mul_add(rhs[rhs_i], mul_carry);
								sum.push(temp.0);
								mul_carry = temp.1;
							}
							//final digit of first row
							sum.push(lhs[0].wrapping_mul_add(rhs[sig_nonzero], mul_carry));
							//middle rows
							for lhs_i in 1..sig_nonzero {
								//first digit of this row
								let temp0 = lhs[lhs_i].carrying_mul(rhs[0]);
								mul_carry = temp0.1;
								let temp1 = sum[lhs_i].carrying_add(temp0.0);
								//sum[lhs_i] does not need to be used again
								sum[lhs_i] = temp1.0;
								let mut add_carry = temp1.1;
								//as we get to the higher lhs digits, the higher rhs digits do not need to be considered
								let rhs_i_upper = sig_nonzero.wrapping_sub(lhs_i);
								//middle digits of this row
								for rhs_i in 1..rhs_i_upper {
									let temp0 = lhs[lhs_i].carrying_mul_add(rhs[rhs_i], mul_carry);
									mul_carry = temp0.1;
									let temp1: DoubleDigit = sum[lhs_i + rhs_i]
										.dd()
										.wrapping_add(temp0.0.dd())
										.wrapping_add(add_carry.dd());
									sum[lhs_i + rhs_i] = temp1.lo();
									add_carry = temp1.hi();
									}
								//final digit of this row
								sum[sig_nonzero] = lhs[lhs_i]
									.wrapping_mul(rhs[rhs_i_upper])
									.wrapping_add(mul_carry)
									.wrapping_add(sum[sig_nonzero])
									.wrapping_add(add_carry);
							}
							for i in 0..sig_nonzero {
								lhs[i] = sum[i];
							}
							//final digit (the only one in its row)
							lhs[sig_nonzero] = lhs[sig_nonzero].wrapping_mul_add(rhs[0], sum[sig_nonzero]);
							return Ok(())
						}
					},
					(true, false) => {
						let mult = lhs[0];
						//first digit done and carry
						let temp = mult.carrying_mul(rhs[0]);
						lhs[0] = temp.0;
						let mut mul_carry = temp.1;
						//middle of row
						for rhs_i in 1..rhs_sig_nonzero {
							let temp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
							lhs[rhs_i] = temp.0;
							mul_carry = temp.1;
						}
						//final digit
						if rhs_sig_nonzero == lhs.len() - 1 {
							lhs[rhs_sig_nonzero] = mult.wrapping_mul_add(rhs[rhs_sig_nonzero], mul_carry);
						} else {
							let temp = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
							lhs[rhs_sig_nonzero] = temp.0;
							lhs[rhs_sig_nonzero + 1] = temp.1;
						}
					},
					(false, true) => {
						//first digit done and carry
						let temp = rhs[0].carrying_mul(lhs[0]);
						lhs[0] = temp.0;
						let mut mul_carry = temp.1;
						//middle of row
						for lhs_i in 1..lhs_sig_nonzero {
							let temp = rhs[0].carrying_mul_add(lhs[lhs_i], mul_carry);
							lhs[lhs_i] = temp.0;
							mul_carry = temp.1;
						}
						//final digit
						if lhs_sig_nonzero == lhs.len() - 1 {
							lhs[lhs_sig_nonzero] = rhs[0].wrapping_mul_add(lhs[lhs_sig_nonzero], mul_carry);
						} else {
							let temp = rhs[0].carrying_mul_add(lhs[lhs_sig_nonzero], mul_carry);
							lhs[lhs_sig_nonzero] = temp.0;
							lhs[lhs_sig_nonzero + 1] = temp.1;
						}
					},
					(true, true) => {
						let temp0 = lhs[0].carrying_mul(rhs[0]);
						lhs[0] = temp0.0;
						lhs[1] = temp0.1;
					}
				}
			}
		}
		self.clear_unused_bits();
		Ok(())
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
	pub fn into_wrapping_udiv(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_udiv_assign)
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
	pub fn wrapping_udiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
		if rhs.is_zero() {
			return Err(Error::division_by_zero(DivOp::UnsignedDiv, self.clone()))
		}
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let lval = lhs.repr();
				let rval = rhs.repr();
				let result = lval.wrapping_div(rval);
				*lhs = Digit(result);
			}
			Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
		Ok(())
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
	pub fn into_wrapping_sdiv(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sdiv_assign)
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
	pub fn wrapping_sdiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
		if rhs.is_zero() {
			return Err(Error::division_by_zero(DivOp::SignedDiv, self.clone()))
		}
		let width = self.width();
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let mut l = lhs.clone();
				let mut r = rhs.clone();
				l.sign_extend_from(width).unwrap();
				r.sign_extend_from(width).unwrap();
				let lval = l.repr() as i64;
				let rval = r.repr() as i64;
				let result = lval.wrapping_div(rval) as DigitRepr;
				*lhs = Digit(result);
			}
			Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
		self.clear_unused_bits();
		Ok(())
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
	pub fn into_wrapping_urem(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_urem_assign)
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
	pub fn wrapping_urem_assign(&mut self, rhs: &ApInt) -> Result<()> {
		if rhs.is_zero() {
			return Err(Error::division_by_zero(DivOp::UnsignedRem, self.clone()))
		}
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let lval = lhs.repr();
				let rval = rhs.repr();
				let result = lval.wrapping_rem(rval);
				*lhs = Digit(result);
			}
			Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
		Ok(())
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
	pub fn into_wrapping_srem(self, rhs: &ApInt) -> Result<ApInt> {
		try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_srem_assign)
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
	pub fn wrapping_srem_assign(&mut self, rhs: &ApInt) -> Result<()> {
		if rhs.is_zero() {
			return Err(Error::division_by_zero(DivOp::SignedRem, self.clone()))
		}
		let width = self.width();
		match self.zip_access_data_mut(rhs)? {
			Inl(lhs, rhs) => {
				let mut l = lhs.clone();
				let mut r = rhs.clone();
				l.sign_extend_from(width).unwrap();
				r.sign_extend_from(width).unwrap();
				let lval = l.repr() as i64;
				let rval = r.repr() as i64;
				let result = lval.wrapping_rem(rval) as DigitRepr;
				*lhs = Digit(result);
			}
			Ext(_lhs, _rhs) => {
				unimplemented!()
			}
		}
		self.clear_unused_bits();
		Ok(())
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
		self.into_wrapping_neg()
	}
}

impl<'a> Neg for &'a ApInt {
	type Output = ApInt;

	fn neg(self) -> Self::Output {
		self.clone().into_wrapping_neg()
	}
}

impl<'a> Neg for &'a mut ApInt {
	type Output = &'a mut ApInt;

	fn neg(self) -> Self::Output {
		self.wrapping_neg();
		self
	}
}

// ============================================================================
//  Add and Add-Assign: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl<'a> Add<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn add(self, rhs: &'a ApInt) -> Self::Output {
		self.into_wrapping_add(rhs).unwrap()
	}
}

impl<'a, 'b> Add<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn add(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_wrapping_add(rhs).unwrap()
	}
}

impl<'a> AddAssign<&'a ApInt> for ApInt {
	fn add_assign(&mut self, rhs: &'a ApInt) {
		self.wrapping_add_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Sub and Sub-Assign: `std::ops::Sub` and `std::ops::SubAssign`
// ============================================================================

impl<'a> Sub<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn sub(self, rhs: &'a ApInt) -> Self::Output {
		self.into_wrapping_sub(rhs).unwrap()
	}
}

impl<'a, 'b> Sub<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn sub(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_wrapping_sub(rhs).unwrap()
	}
}

impl<'a> SubAssign<&'a ApInt> for ApInt {
	fn sub_assign(&mut self, rhs: &'a ApInt) {
		self.wrapping_sub_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Mul and Mul-Assign: `std::ops::Mul` and `std::ops::MulAssign`
// ============================================================================

impl<'a> Mul<&'a ApInt> for ApInt {
	type Output = ApInt;

	fn mul(self, rhs: &'a ApInt) -> Self::Output {
		self.into_wrapping_mul(rhs).unwrap()
	}
}

impl<'a, 'b> Mul<&'a ApInt> for &'b ApInt {
	type Output = ApInt;

	fn mul(self, rhs: &'a ApInt) -> Self::Output {
		self.clone().into_wrapping_mul(rhs).unwrap()
	}
}

impl<'a> MulAssign<&'a ApInt> for ApInt {
	fn mul_assign(&mut self, rhs: &'a ApInt) {
		self.wrapping_mul_assign(rhs).unwrap();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	mod inc {
		use super::*;
		use std::u64;

		#[test]
		fn test() {
			assert_eq!(ApInt::from(14u8).into_wrapping_inc(),ApInt::from(15u8));
			assert_eq!(ApInt::from(15u8).into_wrapping_inc(),ApInt::from(16u8));
			assert_eq!(ApInt::from(16u8).into_wrapping_inc(),ApInt::from(17u8));
			assert_eq!(ApInt::from(17u8).into_wrapping_inc(),ApInt::from(18u8));
			assert_eq!(ApInt::from([0u64,0,0]).into_wrapping_inc(),ApInt::from([0u64,0,1]));			
			assert_eq!(ApInt::from([0,7,u64::MAX]).into_wrapping_inc(),ApInt::from([0u64,8,0]));
			assert_eq!(ApInt::from([u64::MAX,u64::MAX]).into_wrapping_inc(),ApInt::from([0u64,0]));
			assert_eq!(ApInt::from([0,u64::MAX,u64::MAX - 1]).into_wrapping_inc(),ApInt::from([0,u64::MAX,u64::MAX]));
			assert_eq!(ApInt::from([0,u64::MAX,0]).into_wrapping_inc(),ApInt::from([0,u64::MAX,1]));	
		}
	}

	mod wrapping_neg {
		use super::*;
		use bitwidth::{BitWidth};

		fn assert_symmetry(input: ApInt, expected: ApInt) {
			assert_eq!(input.clone().into_wrapping_neg(), expected.clone());
			assert_eq!(expected.into_wrapping_neg(), input);
		}

		fn test_vals() -> impl Iterator<Item = i128> {
			[0_i128, 1, 2, 4, 5, 7, 10, 42, 50, 100, 128, 150,
			 1337, 123123, 999999, 987432, 77216417].into_iter().map(|v| *v)
		}

		#[test]
		fn simple() {
			assert_symmetry(ApInt::zero(BitWidth::w1()), ApInt::zero(BitWidth::w1()));
			assert_symmetry(ApInt::one(BitWidth::w1()), ApInt::all_set(BitWidth::w1()));
		}

		#[test]
		fn range() {
			for v in test_vals() {
				assert_symmetry(ApInt::from_i8(v as i8), ApInt::from_i8(-v as i8));
				assert_symmetry(ApInt::from_i16(v as i16), ApInt::from_i16(-v as i16));
				assert_symmetry(ApInt::from_i32(v as i32), ApInt::from_i32(-v as i32));
				assert_symmetry(ApInt::from_i64(v as i64), ApInt::from_i64(-v as i64));
				assert_symmetry(ApInt::from_i128(v), ApInt::from_i128(-v));
			}
		}
	}

	mod mul {
		use super::*;
		use bitwidth::BitWidth;
		use std::{u8,u64};

		#[test]
		fn rigorous() {
			//there are many special case and size optimization paths, so this test must be very rigorous.

			//multiplication of apints composed of only u8::MAX in their least significant digits
			//only works for num_u8 > 1
			fn nine_test(num_u8: usize) {
				let mut lhs;
				let mut rhs = ApInt::from(0u8).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
				let nine =
					ApInt::from(u8::MAX).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
				for rhs_nine in 1..=num_u8 {
					rhs.wrapping_shl_assign(8).unwrap();
					rhs |= &nine;
					lhs = ApInt::from(0u8).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
					'outer: for lhs_nine in 1..=num_u8 {
						lhs.wrapping_shl_assign(8).unwrap();
						lhs |= &nine;
						//imagine multiplying a string of base 10 nines together.
						//It will produce things like 998001, 8991, 98901, 9989001.
						//this uses a formula for the number of nines, eights, and zeros except here nine is u8::MAX, eight is u8::MAX - 1, and zero is 0u8
						let mut zeros_after_one = if lhs_nine < rhs_nine {
							lhs_nine - 1
						} else {
							rhs_nine - 1
						};
						let mut nines_before_eight = if lhs_nine > rhs_nine {
							lhs_nine - rhs_nine
						} else {
							rhs_nine - lhs_nine
						};
						let mut nines_after_eight = if lhs_nine < rhs_nine {
							lhs_nine - 1
						} else {
							rhs_nine - 1
						};
						let mut result = lhs.clone().into_wrapping_mul(&rhs).unwrap();
						assert_eq!(result.clone().resize_to_u8(), 1u8);
						for i in 0..zeros_after_one {
							if i >= num_u8 - 1 {
								continue 'outer;
							}
							result.wrapping_lshr_assign(8).unwrap();
							let temp = result.clone().resize_to_u8();
							if temp != 0 {
								panic!(
									"\nlhs_nine:{}\nrhs_nine:{}\nresult:{:?}\nzeros_after_one:{}\nnines_before_eight:{}\nnines_after_eight:{}\n",
									lhs_nine, rhs_nine, result,zeros_after_one,nines_before_eight,nines_after_eight
								);
							}
						}
						for i in 0..nines_before_eight {
							if zeros_after_one + i >= num_u8 - 1 {
								continue 'outer;
							}
							result.wrapping_lshr_assign(8).unwrap();
							assert_eq!(result.clone().resize_to_u8(), u8::MAX);
						}
						if zeros_after_one + nines_before_eight >= num_u8 - 1 {
							continue 'outer;
						}
						result.wrapping_lshr_assign(8).unwrap();
						let temp = result.clone().resize_to_u8();
						if temp != u8::MAX - 1 {
							panic!(
								"\nlhs_nine:{}\nrhs_nine:{}\nresult:{:?}\nzeros_after_one:{}\nnines_before_eight:{}\nnines_after_eight:{}\n",
								lhs_nine, rhs_nine, result,zeros_after_one,nines_before_eight,nines_after_eight
							);
						}
						for i in 0..nines_after_eight {
							if 1 + zeros_after_one + nines_before_eight + i >= num_u8 - 1 {
								continue 'outer;
							}
							result.wrapping_lshr_assign(8).unwrap();
							if result.clone().resize_to_u8() != u8::MAX {
								panic!(
									"\nlhs_nine:{}\nrhs_nine:{}\nresult:{:?}\nzeros_after_one:{}\nnines_before_eight:{}\nnines_after_eight:{}\n",
									lhs_nine, rhs_nine, result,zeros_after_one,nines_before_eight,nines_after_eight
								);
							}
						}
					}
				}
			}
			//test inl apints
			assert_eq!(
				ApInt::from(u8::MAX)
					.into_wrapping_mul(&ApInt::from(u8::MAX))
					.unwrap(),
				ApInt::from(1u8)
			);
			nine_test(2);
			nine_test(3);
			nine_test(4);
			nine_test(7);
			nine_test(8);
			//test ext apints
			nine_test(9);
			nine_test(16);
			//5 digits wide
			nine_test(40);
			nine_test(63);
			//non overflowing test
			let resize = [
				7usize, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 137, 200, 255,
				256, 700, 907, 1024, 2018, 2019,
			];
			let lhs_shl = [
				0usize, 1, 0, 1, 4, 7, 4, 10, 13, 0, 31, 25, 7, 17, 32, 50, 0, 64, 249, 8, 777, 0,
				1000, 0,
			];
			let rhs_shl = [
				0usize, 0, 1, 1, 3, 6, 4, 14, 10, 0, 0, 25, 0, 18, 32, 49, 100, 64, 0, 256, 64,
				900, 1000, 0,
			];
			for (i, _) in resize.iter().enumerate() {
				let mut lhs = ApInt::from(5u8)
					.into_zero_resize(BitWidth::new(resize[i]).unwrap())
					.into_wrapping_shl(lhs_shl[i])
					.unwrap();
				let mut rhs = ApInt::from(11u8)
					.into_zero_resize(BitWidth::new(resize[i]).unwrap())
					.into_wrapping_shl(rhs_shl[i])
					.unwrap();
				let mut zero = ApInt::from(0u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
				let mut one = ApInt::from(1u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
				let mut expected = ApInt::from(55u8)
					.into_zero_resize(BitWidth::new(resize[i]).unwrap())
					.into_wrapping_shl(rhs_shl[i] + lhs_shl[i])
					.unwrap();
				assert_eq!(lhs.clone().into_wrapping_mul(&zero).unwrap(), zero);
				assert_eq!(zero.clone().into_wrapping_mul(&rhs).unwrap(), zero);
				assert_eq!(lhs.clone().into_wrapping_mul(&one).unwrap(), lhs);
				assert_eq!(one.clone().into_wrapping_mul(&rhs).unwrap(), rhs);
				assert_eq!(lhs.clone().into_wrapping_mul(&rhs).unwrap(), expected);
			}
			assert_eq!(
				ApInt::from([0,0,0,0,u64::MAX,0,u64::MAX,u64::MAX])
				.into_wrapping_mul(&ApInt::from([0,0,0,0,u64::MAX,u64::MAX,0,u64::MAX])).unwrap()
				,ApInt::from([u64::MAX,0,1,u64::MAX - 3,1,u64::MAX,u64::MAX,1]));
		}
	}

	mod udiv {
		use super::*;

		#[test]
		fn simple() {
			let lhs = ApInt::from(56_u32);
			let rhs = ApInt::from(7_u32);
			let result = lhs.into_wrapping_udiv(&rhs).unwrap();
			assert_eq!(result, ApInt::from(8_u32));
		}
	}

	mod sdiv {
		use super::*;

		#[test]
		fn simple() {
			let lhs = ApInt::from(72_i32);
			let rhs = ApInt::from(12_i32);
			let result = lhs.into_wrapping_sdiv(&rhs).unwrap();
			assert_eq!(result, ApInt::from(6_u32));
		}

		#[test]
		fn with_neg() {
			let lhs = ApInt::from(72_i32);
			let rhs = ApInt::from(-12_i32);
			let result = lhs.into_wrapping_sdiv(&rhs).unwrap();
			assert_eq!(result, ApInt::from(-6_i32));
		}
	}

	mod urem {
		use super::*;

		#[test]
		fn simple() {
			let lhs = ApInt::from(15_u32);
			let rhs = ApInt::from(4_u32);
			let result = lhs.into_wrapping_urem(&rhs).unwrap();
			assert_eq!(result, ApInt::from(3_u32));
		}
	}

	mod srem {
		use super::*;

		#[test]
		fn simple() {
			let lhs = ApInt::from(23_i32);
			let rhs = ApInt::from(7_i32);
			let result = lhs.into_wrapping_srem(&rhs).unwrap();
			assert_eq!(result, ApInt::from(2_u32));
		}

		#[test]
		fn with_neg() {
			let lhs = ApInt::from(-23_i32);
			let rhs = ApInt::from(7_i32);
			let result = lhs.into_wrapping_srem(&rhs).unwrap();
			assert_eq!(result, ApInt::from(-2_i32));
		}
	}

}
