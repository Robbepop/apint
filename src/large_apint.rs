use errors::{Result};
use digit::{Digit};
use bitwidth::BitWidth;
use traits::{Width, ApIntMutImpl};
use digit_seq::{
	AsDigitSeq,
	AsDigitSeqMut,
	ContiguousDigitSeq,
	ContiguousDigitSeqMut
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LargeApInt<'a> {
	len   : BitWidth,
	digits: &'a [Digit]
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct LargeApIntMut<'a> {
	len   : BitWidth,
	digits: &'a mut [Digit]
}

// ============================================================================

impl<'a> AsDigitSeq<'a> for LargeApInt<'a> {
	type Seq = ContiguousDigitSeq<'a>;

	fn digits(self) -> Self::Seq {
		ContiguousDigitSeq::from(self.digits)
	}
}

impl<'a> AsDigitSeqMut<'a> for LargeApIntMut<'a> {
	type SeqMut = ContiguousDigitSeqMut<'a>;

	fn digits_mut(self) -> Self::SeqMut {
		ContiguousDigitSeqMut::from(self.digits)
	}
}

// ============================================================================

impl<'a> LargeApInt<'a> {
	pub(crate) fn new(len: BitWidth, digits: &'a [Digit]) -> LargeApInt {
		LargeApInt{len, digits}
	}
}

impl<'a> LargeApIntMut<'a> {
	pub(crate) fn new(len: BitWidth, digits: &'a mut [Digit]) -> LargeApIntMut {
		LargeApIntMut{len, digits}
	}
}

// ============================================================================

pub(crate) trait DigitSliceWrapper {
	fn digits_slice(&self) -> &[Digit];
}

pub(crate) trait DigitMutSliceWrapper {
	fn digits_slice_mut(&mut self) -> &mut [Digit];
}

impl<'a> DigitSliceWrapper for LargeApInt<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a LargeApInt<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a mut LargeApInt<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for LargeApIntMut<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a LargeApIntMut<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a mut LargeApIntMut<'a> {
	fn digits_slice(&self) -> &[Digit] {
		self.digits
	}
}

// ============================================================================

impl<'a> DigitMutSliceWrapper for LargeApIntMut<'a> {
	fn digits_slice_mut(&mut self) -> &mut [Digit] {
		self.digits
	}
}

impl<'a> DigitMutSliceWrapper for &'a mut LargeApIntMut<'a> {
	fn digits_slice_mut(&mut self) -> &mut [Digit] {
		self.digits
	}
}

// ============================================================================

impl<'a> Width for LargeApInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a LargeApInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a mut LargeApInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for LargeApIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a LargeApIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a mut LargeApIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

// ============================================================================

impl<'a, T> ApIntMutImpl<LargeApInt<'a>> for T
	where T: Width + DigitMutSliceWrapper
{
	fn neg_inplace(&mut self) {
		unimplemented!()
	}

	fn add_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn sub_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn mul_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn sdiv_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn udiv_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn srem_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn urem_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}


	fn shl_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn lshr_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

	fn ashr_inplace(&mut self, _other: &LargeApInt) -> Result<()> {
		unimplemented!()
	}

}
