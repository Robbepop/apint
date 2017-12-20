use digit::{Digit};
use bitwidth::BitWidth;
use traits::{
	Width,
};
use digit_seq::{
	AsDigitSeq,
	AsDigitSeqMut,
	ContiguousDigitSeq,
	ContiguousDigitSeqMut
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
