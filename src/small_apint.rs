use digit;
use digit::{Bit, Digit};
use bitwidth::BitWidth;
use errors::{Result};
use traits::{
	Width,
	ApIntImpl,
	ApIntMutImpl,
};
use digit_seq::{
	AsDigitSeq,
	AsDigitSeqMut,
	ContiguousDigitSeq,
	ContiguousDigitSeqMut
};

use std::ops::{
	BitAndAssign,
	BitOrAssign,
	BitXorAssign
};
use std::marker::PhantomData;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SmallApInt<'a> {
	len  : BitWidth,
	digit: Digit,
	life : PhantomData<&'a ()>
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct SmallApIntMut<'a> {
	len  : BitWidth,
	digit: &'a mut Digit
}

impl<'a> SmallApInt<'a> {
	pub fn most_significant_digit(&self) -> Digit {
		self.digit
	}

	pub fn most_significant_bit(&self) -> Bit {
		self.digit.most_significant_bit()
	}
}

impl<'a> SmallApIntMut<'a> {
	pub fn into_most_significant_digit_mut(self) -> &'a mut Digit {
		self.digit
	}
}

// ============================================================================

impl<'a> AsDigitSeq<'a> for SmallApInt<'a> {
	type Seq = ContiguousDigitSeq<'a>;

	fn digits(self) -> Self::Seq {
		use std::slice;
		ContiguousDigitSeq::from(unsafe{
			slice::from_raw_parts(&self.digit as *const Digit, 1)})
	}
}

impl<'a> AsDigitSeq<'a> for SmallApIntMut<'a> {
	type Seq = ContiguousDigitSeq<'a>;

	fn digits(self) -> Self::Seq {
		use std::slice;
		ContiguousDigitSeq::from(unsafe{
			slice::from_raw_parts(self.digit as *const Digit, 1)})
	}
}
impl<'a> AsDigitSeqMut<'a> for SmallApIntMut<'a> {
	type SeqMut = ContiguousDigitSeqMut<'a>;

	fn digits_mut(self) -> Self::SeqMut {
		use std::slice;
		ContiguousDigitSeqMut::from(unsafe{
			slice::from_raw_parts_mut(self.digit as *mut Digit, 1)})
	}
}

// ============================================================================

impl<'a> SmallApInt<'a> {
	#[inline]
	pub(crate) fn new<W>(width: W, digit: Digit) -> SmallApInt<'a>
		where W: Into<BitWidth>
	{
		SmallApInt{len: width.into(), digit, life: PhantomData}
	}

	#[inline]
	pub(crate) fn one<W>(width: W) -> SmallApInt<'a>
		where W: Into<BitWidth>
	{
		SmallApInt::new(width, Digit::one())
	}

	#[inline]
	pub(crate) fn zero<W>(width: W) -> SmallApInt<'a>
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

impl<'a> Width for SmallApInt<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a SmallApInt<'a> {
	fn width(&self) -> BitWidth { self.len }
}

impl<'a> Width for &'a mut SmallApInt<'a> {
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

impl<'a> DigitWrapper for SmallApInt<'a> {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a SmallApInt<'a> {
	fn digit(&self) -> Digit { self.digit }
}

impl<'a> DigitWrapper for &'a mut SmallApInt<'a> {
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

impl<'a, T> ApIntImpl<SmallApInt<'a>> for T
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

impl<'a, T> ApIntMutImpl<SmallApInt<'a>> for T
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

	fn add_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn sub_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn mul_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn sdiv_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn udiv_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn srem_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn urem_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}


	fn shl_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn lshr_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

	fn ashr_inplace(&mut self, _other: &SmallApInt) -> Result<()> {
		unimplemented!()
	}

}
