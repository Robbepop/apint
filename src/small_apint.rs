use digit;
use digit::{Bit, Digit};
use bitwidth::BitWidth;
use errors::{Result};
use traits::{
	Width,
	ApIntImpl,
	ApIntMutImpl,
};
use std::ops::{
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SmallApInt {
	len  : BitWidth,
	digit: Digit
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct SmallApIntMut<'a> {
	len  : BitWidth,
	digit: &'a mut Digit
}

impl SmallApInt {
	#[inline]
	pub(crate) fn new<W>(width: W, digit: Digit) -> SmallApInt
		where W: Into<BitWidth>
	{
		SmallApInt{len: width.into(), digit}
	}

	#[inline]
	pub(crate) fn one<W>(width: W) -> SmallApInt
		where W: Into<BitWidth>
	{
		SmallApInt::new(width, Digit::one())
	}

	#[inline]
	pub(crate) fn zero<W>(width: W) -> SmallApInt
		where W: Into<BitWidth>
	{
		SmallApInt::new(width, Digit::zero())
	}
}

impl<'a> SmallApIntMut<'a> {
	#[inline]
	pub(crate) fn new(len: BitWidth, digit: &'a mut Digit) -> SmallApIntMut {
		SmallApIntMut{len, digit}
	}
}

// ============================================================================

pub(crate) trait DigitWrapper {
	fn digit(&self) -> Digit;
}

pub(crate) trait DigitMutWrapper {
	fn digit_mut(&mut self) -> &mut Digit;
}

// ============================================================================

impl Width for SmallApInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a SmallApInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a mut SmallApInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for SmallApIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a SmallApIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a mut SmallApIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

// ============================================================================

impl DigitWrapper for SmallApInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a SmallApInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a mut SmallApInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for SmallApIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

impl<'a> DigitWrapper for &'a SmallApIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

impl<'a> DigitWrapper for &'a mut SmallApIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

// ============================================================================

impl<'a> DigitMutWrapper for SmallApIntMut<'a> {
	fn digit_mut(&mut self) -> &mut Digit { self.digit }
}

impl<'a> DigitMutWrapper for &'a mut SmallApIntMut<'a> {
	fn digit_mut(&mut self) -> &mut Digit { self.digit }
}

// ============================================================================

use checks;

impl<T> ApIntImpl<SmallApInt> for T
	where T: Width + DigitWrapper
{
	#[inline]
	fn get(&self, n: usize) -> Result<Bit> {
		checks::verify_bit_access(self, n)?;
		self.digit().get(n)
	}

	#[inline]
	fn sign_bit(&self) -> Bit {
		self.get(self.width().to_usize() - 1).unwrap()
	}

	#[inline]
	fn ult(&self, other: &SmallApInt) -> Result<bool> {
		checks::verify_common_bitwidth(self, &other)?;
		Ok(self.digit().repr() < other.digit().repr())
	}

	#[inline]
	fn slt(&self, other: &SmallApInt) -> Result<bool> {
		checks::verify_common_bitwidth(self, &other)?;
		let infate_abs = digit::BITS - self.width().to_usize();
		let left       = ( self.digit().repr() << infate_abs) as i64;
		let right      = (other.digit().repr() << infate_abs) as i64;
		Ok(left < right)
	}
}

impl<T> ApIntMutImpl<SmallApInt> for T
	where T: Width + DigitMutWrapper
{

	#[inline]
	fn set(&mut self, n: usize) -> Result<()> {
		checks::verify_bit_access(self, n)?;
		self.digit_mut().set(n)
	}

	#[inline]
	fn set_all(&mut self) {
		self.digit_mut().set_all();
		let valid_bits = self.width().to_usize();
		self.digit_mut().retain_last_n(valid_bits).unwrap();
	}

	#[inline]
	fn unset(&mut self, n: usize) -> Result<()> {
		checks::verify_bit_access(self, n)?;
		self.digit_mut().unset(n)
	}

	#[inline]
	fn unset_all(&mut self) {
		self.digit_mut().unset_all()
	}

	#[inline]
	fn flip(&mut self, n: usize) -> Result<()> {
		checks::verify_bit_access(self, n)?;
		self.digit_mut().flip(n)
	}

	#[inline]
	fn flip_all(&mut self) {
		self.digit_mut().flip_all();
		let valid_bits = self.width().to_usize();
		self.digit_mut().retain_last_n(valid_bits).unwrap();
	}


	#[inline]
	fn bitnot_inplace(&mut self) {
		let width = self.width().to_usize();
		self.digit_mut().not_inplace();
		self.digit_mut().retain_last_n(width).unwrap();
	}

	#[inline]
	fn bitand_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		Ok(self.digit_mut().bitand_assign(other.digit()))
	}

	#[inline]
	fn bitor_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		Ok(self.digit_mut().bitor_assign(other.digit()))
	}

	#[inline]
	fn bitxor_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		Ok(self.digit_mut().bitxor_assign(other.digit()))
	}


	fn neg_inplace(&mut self) {
		// Negating a twos-complement number is accomplished by inverting all bits and adding 1.
		unimplemented!()
	}

	fn add_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn sub_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn mul_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn sdiv_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn udiv_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn srem_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn urem_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}


	fn shl_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn lshr_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn ashr_inplace(&mut self, other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

}
