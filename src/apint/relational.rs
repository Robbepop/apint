use apint::{ApInt};
use apint::utils::{
	ZipDataAccess
};
use errors::{Result};
use traits::Width;
use digit;
use digit::{Bit};

use std::cmp::Ordering;
use std::ops::Not;

impl PartialEq for ApInt {
	fn eq(&self, other: &ApInt) -> bool {
		if self.len_bits() != other.len_bits() {
			return false
		}
		self.as_digit_slice() == other.as_digit_slice()
	}
}

impl Eq for ApInt {}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl ApInt {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, rhs: &ApInt) -> Result<bool> {
		match self
			.zip_access_data(rhs)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on unsigned less-than (slt) comparison with `lhs < rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))?
		{
			ZipDataAccess::Inl(lhs, rhs) => {
				Ok(lhs.repr() < rhs.repr())
			}
			ZipDataAccess::Ext(lhs, rhs) => {
				for (l, r) in lhs.into_iter()
				                 .zip(rhs.into_iter())
				{
					match l.cmp(r) {
						Ordering::Less    => return Ok(true),
						Ordering::Greater => return Ok(false),
						Ordering::Equal   => ()
					}
				}
				Ok(false)
			}
		}
	}

	/// Unsigned less-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn ule(&self, rhs: &ApInt) -> Result<bool> {
		rhs.ult(self).map(Not::not)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on unsigned less-than or equals (ule) comparison with `lhs <= rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	#[inline]
	pub fn ugt(&self, rhs: &ApInt) -> Result<bool> {
		rhs.ult(self)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on unsigned greater-than (ugt) comparison with `lhs > rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn uge(&self, rhs: &ApInt) -> Result<bool> {
		self.ult(rhs).map(Not::not)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on unsigned greater-than or equals (ule) comparison with `lhs >= rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, rhs: &ApInt) -> Result<bool> {
		let lhs = self;
		lhs.zip_access_data(rhs).and_then(|zipped| {
			match zipped {
				ZipDataAccess::Inl(lhs, rhs) => {
					let infate_abs = digit::BITS - self.width().to_usize();
					let lhs = (lhs.repr() << infate_abs) as i64;
					let rhs = (rhs.repr() << infate_abs) as i64;
					Ok(lhs < rhs)
				}
				ZipDataAccess::Ext(_, _) => {
					match (lhs.sign_bit(), rhs.sign_bit()) {
						(Bit::Unset, Bit::Unset) => lhs.ult(rhs),
						(Bit::Unset, Bit::Set  ) => Ok(false),
						(Bit::Set  , Bit::Unset) => Ok(true),
						(Bit::Set  , Bit::Set  ) => rhs.ugt(lhs)
					}
				}
			}
		})
		.map_err(|err| err.with_annotation(format!(
			"Error occured on signed less-than (slt) comparison with `lhs < rhs` where \
				\n\tlhs = {:?}\
				\n\trhs = {:?}",
			self, rhs)
		))
	}

	/// Signed less-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn sle(&self, rhs: &ApInt) -> Result<bool> {
		rhs.slt(self).map(Not::not)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on signed less-than or equals (ule) comparison with `lhs <= rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

	/// Signed greater-than comparison with the other bitvec.
	#[inline]
	pub fn sgt(&self, rhs: &ApInt) -> Result<bool> {
		rhs.slt(self)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on signed greater-than (ugt) comparison with `lhs > rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn sge(&self, rhs: &ApInt) -> Result<bool> {
		self.slt(rhs).map(Not::not)
			.map_err(|err| err.with_annotation(format!(
				"Error occured on signed greater-than or equals (ule) comparison with `lhs >= rhs` where \
				 \n\tlhs = {:?}\
				 \n\trhs = {:?}",
				self, rhs)
			))
	}

}

#[cfg(test)]
mod tests {
	use super::*;

	mod partial_eq {
		use super::*;

		#[test]
		fn simple_small() {
			let a = ApInt::from_u8(42);
			let b = ApInt::from_u8(42);
			let c = ApInt::from_u8(77);
			let d = ApInt::from_u16(42);
			assert_eq!(a, b);
			assert_ne!(a, c);
			assert_ne!(a, d);
			assert_ne!(b, c);
			assert_ne!(b, d);
			assert_ne!(c, d);
		}

		#[test]
		fn simple_large() {
			let a = ApInt::from_u128(42);
			let b = ApInt::from_u128(42);
			let c = ApInt::from_u128(1337);
			let d = ApInt::from_u64(42);
			assert_eq!(a, b);
			assert_ne!(a, c);
			assert_ne!(a, d);
			assert_ne!(b, c);
			assert_ne!(b, d);
			assert_ne!(c, d);
		}
	}
}
