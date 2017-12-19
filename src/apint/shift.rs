use apint::{ApInt};
use apint::utils::{DataAccessMut};
use errors::{Result};
use checks;

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

	/// Shift this `ApInt` left by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn checked_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		let shift_amount = shift_amount.into();
		checks::verify_shift_amount(self, shift_amount)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => {
				*digit.repr_mut() <<= shift_amount.to_usize();
			}
			DataAccessMut::Ext(_digits) => {
				unimplemented!()
			}
		}
		Ok(())
	}

	/// Shift this `ApInt` left by the given `shift_amount` bits and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn into_checked_shl<S>(self, shift_amount: S) -> Result<ApInt>
		where S: Into<ShiftAmount>
	{
		let mut this = self;
		this.checked_shl_assign(shift_amount)?;
		Ok(this)
	}

	/// Logically right-shifts this `ApInt` by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn checked_lshr_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		let shift_amount = shift_amount.into();
		checks::verify_shift_amount(self, shift_amount)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => {
				*digit.repr_mut() >>= shift_amount.to_usize();
			}
			DataAccessMut::Ext(_digits) => {
				unimplemented!()
			}
		}
		Ok(())
	}

	/// Logically right-shifts this `ApInt` by the given `shift_amount` bits
	/// and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn into_checked_lshr<S>(self, shift_amount: S) -> Result<ApInt>
		where S: Into<ShiftAmount>
	{
		let mut this = self;
		this.checked_lshr_assign(shift_amount)?;
		Ok(this)
	}

	/// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn checked_ashr_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		let shift_amount = shift_amount.into();
		checks::verify_shift_amount(self, shift_amount)?;
		match self.access_data_mut() {
			DataAccessMut::Inl(digit) => {
				let signed = digit.repr() as i64;
				let shifted = signed >> shift_amount.to_usize();
				*digit.repr_mut() = shifted as u64;
			}
			DataAccessMut::Ext(_digits) => {
				unimplemented!()
			}
		}
		Ok(())
	}

	/// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits
	/// and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
	pub fn into_checked_ashr<S>(self, shift_amount: S) -> Result<ApInt>
		where S: Into<ShiftAmount>
	{
		let mut this = self;
		this.checked_ashr_assign(shift_amount)?;
		Ok(this)
	}

}
