use errors::{Result};
use digit::{Bit, Digit};
use bitwidth::BitWidth;
use traits::{Width, APIntImpl, APIntMutImpl};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LargeAPInt<'a> {
	len   : BitWidth,
	digits: &'a [Digit]
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct LargeAPIntMut<'a> {
	len   : BitWidth,
	digits: &'a mut [Digit]
}

// ============================================================================

impl<'a> LargeAPInt<'a> {
	pub(crate) fn new(len: BitWidth, digits: &'a [Digit]) -> LargeAPInt {
		LargeAPInt{len, digits}
	}
}

impl<'a> LargeAPIntMut<'a> {
	pub(crate) fn new(len: BitWidth, digits: &'a mut [Digit]) -> LargeAPIntMut {
		LargeAPIntMut{len, digits}
	}
}

// ============================================================================

pub(crate) trait DigitSliceWrapper {
	fn digits(&self) -> &[Digit];
}

pub(crate) trait DigitMutSliceWrapper {
	fn digits_mut(&mut self) -> &mut [Digit];
}

impl<'a> DigitSliceWrapper for LargeAPInt<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a LargeAPInt<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a mut LargeAPInt<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for LargeAPIntMut<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a LargeAPIntMut<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

impl<'a> DigitSliceWrapper for &'a mut LargeAPIntMut<'a> {
	fn digits(&self) -> &[Digit] {
		self.digits
	}
}

// ============================================================================

impl<'a> DigitMutSliceWrapper for LargeAPIntMut<'a> {
	fn digits_mut(&mut self) -> &mut [Digit] {
		self.digits
	}
}

impl<'a> DigitMutSliceWrapper for &'a mut LargeAPIntMut<'a> {
	fn digits_mut(&mut self) -> &mut [Digit] {
		self.digits
	}
}

// ============================================================================

impl<'a> Width for LargeAPInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a LargeAPInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a mut LargeAPInt<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for LargeAPIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a LargeAPIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

impl<'a> Width for &'a mut LargeAPIntMut<'a> {
	fn width(&self) -> BitWidth {
		self.len
	}
}

// ============================================================================

impl<'a, T> APIntImpl<LargeAPInt<'a>> for T
	where T: Width + DigitSliceWrapper
{
	fn get(&self, n: usize) -> Result<bool> {
		unimplemented!()
	}

	fn sign_bit(&self) -> Bit {
		unimplemented!()
	}

	fn ult(&self, other: &LargeAPInt) -> Result<bool> {
		unimplemented!()
	}

	fn slt(&self, other: &LargeAPInt) -> Result<bool> {
		unimplemented!()
	}
}

impl<'a, T> APIntMutImpl<LargeAPInt<'a>> for T
	where T: Width + DigitMutSliceWrapper
{

	#[inline]
	fn set(&mut self, n: usize) -> Result<()> {
		unimplemented!()
	}

	#[inline]
	fn set_all(&mut self) {
		unimplemented!()
	}

	#[inline]
	fn unset(&mut self, n: usize) -> Result<()> {
		unimplemented!()
	}

	#[inline]
	fn unset_all(&mut self) {
		unimplemented!()
	}

	#[inline]
	fn flip(&mut self, n: usize) -> Result<()> {
		unimplemented!()
	}

	#[inline]
	fn flip_all(&mut self) {
		unimplemented!()
	}


	#[inline]
	fn bitnot_inplace(&mut self) {
		unimplemented!()
	}

	#[inline]
	fn bitand_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	#[inline]
	fn bitor_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	#[inline]
	fn bitxor_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}


	fn neg_inplace(&mut self) {
		unimplemented!()
	}

	fn add_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn sub_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn mul_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn sdiv_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn udiv_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn srem_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn urem_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}


	fn shl_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn lshr_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

	fn ashr_inplace(&mut self, other: &LargeAPInt) -> Result<()> {
		unimplemented!()
	}

}
