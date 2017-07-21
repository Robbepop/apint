use apint::{APInt};
use apint::utils::{ZipModel};
use traits::{APIntImpl};
use errors::{Error, Result};

impl PartialEq for APInt {
	fn eq(&self, other: &APInt) -> bool {
		if self.len_bits() != other.len_bits() {
			return false
		}
		self.as_digit_slice() == other.as_digit_slice()
	}
}

impl Eq for APInt {}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl APInt {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &APInt) -> Result<bool> {
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
	pub fn ule(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than or equals (ule) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(other.ult(self)?))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	#[inline]
	pub fn ugt(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than (ugt) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		other.ult(self)
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn uge(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than or equals (uge) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(self.ult(other)?))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &APInt) -> Result<bool> {
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
	pub fn sle(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned less-than or equals (sle) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(other.slt(self)?))
	}

	/// Signed greater-than comparison with the other bitvec.
	#[inline]
	pub fn sgt(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than (sgt) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		other.slt(self)
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	#[inline]
	pub fn sge(&self, other: &APInt) -> Result<bool> {
		if self.len_bits() != other.len_bits() {
			return Error::unmatching_bitwidths(self.len_bits(), other.len_bits())
				.with_annotation(format!("Error occured on unsigned greater-than or equals (sge) comparison with {:?} and {:?}.", self, other))
				.into()
		}
		Ok(!(self.slt(other)?))
	}

}
