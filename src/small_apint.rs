use digit;
use digit::{Bit, Digit};
use bitwidth::BitWidth;
use errors::{Result};
use traits::{
	Width,
	APIntImpl,
	APIntMutImpl,
};
use std::ops::{
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SmallAPInt {
	len  : BitWidth,
	digit: Digit
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct SmallAPIntMut<'a> {
	len  : BitWidth,
	digit: &'a mut Digit
}

impl SmallAPInt {
	#[inline]
	pub(crate) fn new(len: BitWidth, digit: Digit) -> SmallAPInt {
		SmallAPInt{len, digit}
	}
}

impl<'a> SmallAPIntMut<'a> {
	#[inline]
	pub(crate) fn new(len: BitWidth, digit: &'a mut Digit) -> SmallAPIntMut {
		SmallAPIntMut{len, digit}
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

impl Width for SmallAPInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a SmallAPInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a mut SmallAPInt {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for SmallAPIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a SmallAPIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a mut SmallAPIntMut<'a> {
	fn width(&self) -> BitWidth { self.len }
}

// ============================================================================

impl DigitWrapper for SmallAPInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a SmallAPInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a mut SmallAPInt {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for SmallAPIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

impl<'a> DigitWrapper for &'a SmallAPIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

impl<'a> DigitWrapper for &'a mut SmallAPIntMut<'a> {
	fn digit(&self) -> Digit { *self.digit }
}

// ============================================================================

impl<'a> DigitMutWrapper for SmallAPIntMut<'a> {
	fn digit_mut(&mut self) -> &mut Digit { self.digit }
}

impl<'a> DigitMutWrapper for &'a mut SmallAPIntMut<'a> {
	fn digit_mut(&mut self) -> &mut Digit { self.digit }
}

// ============================================================================

impl<T> APIntImpl<SmallAPInt> for T
	where T: Width + DigitWrapper
{
	#[inline]
	fn get(&self, n: usize) -> Result<Bit> {
		self.verify_bit_access(n)?;
		self.digit().get(n)
	}

	#[inline]
	fn sign_bit(&self) -> Bit {
		self.get(self.width().to_usize() - 1).unwrap().into()
	}

	#[inline]
	fn ult(&self, other: &SmallAPInt) -> Result<bool> {
		self.verify_common_bitwidth(&other)?;
		Ok(self.digit().to_u64() < other.digit().to_u64())
	}

	#[inline]
	fn slt(&self, other: &SmallAPInt) -> Result<bool> {
		self.verify_common_bitwidth(&other)?;
		let infate_abs = digit::BITS - self.width().to_usize();
		let left       = ( self.digit().to_u64() << infate_abs) as i64;
		let right      = (other.digit().to_u64() << infate_abs) as i64;
		Ok(left < right)
	}
}

impl<T> APIntMutImpl<SmallAPInt> for T
	where T: Width + DigitMutWrapper
{

	#[inline]
	fn set(&mut self, n: usize) -> Result<()> {
		self.verify_bit_access(n)?;
		self.digit_mut().set(n)
	}

	#[inline]
	fn set_all(&mut self) {
		self.digit_mut().set_all()
	}

	#[inline]
	fn unset(&mut self, n: usize) -> Result<()> {
		self.verify_bit_access(n)?;
		self.digit_mut().unset(n)
	}

	#[inline]
	fn unset_all(&mut self) {
		self.digit_mut().unset_all()
	}

	#[inline]
	fn flip(&mut self, n: usize) -> Result<()> {
		self.verify_bit_access(n)?;
		self.digit_mut().flip(n)
	}

	#[inline]
	fn flip_all(&mut self) {
		self.digit_mut().flip_all()
	}


	#[inline]
	fn bitnot_inplace(&mut self) {
		let width = self.width().to_usize();
		self.digit_mut().not_inplace();
		self.digit_mut().unset_first_n(digit::BITS - width);
	}

	#[inline]
	fn bitand_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		Ok(self.digit_mut().bitand_assign(other.digit()))
	}

	#[inline]
	fn bitor_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		Ok(self.digit_mut().bitor_assign(other.digit()))
	}

	#[inline]
	fn bitxor_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		Ok(self.digit_mut().bitxor_assign(other.digit()))
	}


	fn neg_inplace(&mut self) {
		unimplemented!()
	}

	fn add_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn sub_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn mul_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn sdiv_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn udiv_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn srem_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn urem_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}


	fn shl_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn lshr_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

	fn ashr_inplace(&mut self, other: &SmallAPInt) -> Result<()> {
		unimplemented!()
	}

}
