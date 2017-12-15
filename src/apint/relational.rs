use apint::{ApInt};
use apint::utils::{ZipModel};
use traits::{ApIntImpl};
use errors::{Error, Result};

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
	pub fn ult(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than (ult) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		match self.zip_model(other)? {
			ZipModel::Inl(left, right) => {
				left.ult(&right)
			}
			ZipModel::Ext(left, right) => {
				left.ult(&right)
			}
		}
	}

	/// Unsigned less-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn ule(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than or equals (ule) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(other.ult(self)?))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	#[inline]
	pub fn ugt(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than (ugt) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		other.ult(self)
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn uge(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than or equals (uge) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(self.ult(other)?))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than (slt) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		match self.zip_model(other)? {
			ZipModel::Inl(left, right) => {
				left.slt(&right)
			}
			ZipModel::Ext(left, right) => {
				left.slt(&right)
			}
		}
	}

	/// Signed less-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn sle(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than or equals (sle) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(other.slt(self)?))
	}

	/// Signed greater-than comparison with the other bitvec.
	#[inline]
	pub fn sgt(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than (sgt) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		other.slt(self)
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn sge(&self, other: &ApInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than or equals (sge) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(self.slt(other)?))
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
