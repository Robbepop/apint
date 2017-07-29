use errors::{Error, Result};
use bitwidth::{BitWidth, Storage};
use digit::{Bit};
use digit;

pub(crate) trait Width {
	fn width(&self) -> BitWidth;

	#[inline]
	fn verify_bit_access(&self, n: usize) -> Result<()> {
		if n < self.width().to_usize() {
			Ok(())
		} else {
			Error::bit_access_out_of_bounds(n, self.width().to_usize()).into()
		}
	}

	#[inline]
	fn verify_small_bitwidth(&self) -> Result<()> {
		match self.width().storage() {
			Storage::Inl => Ok(()),
			Storage::Ext => Error::bitwidth_too_large(self.width().to_usize(), digit::BITS).into()
		}
	}

	#[inline]
	fn verify_large_bitwidth(&self) -> Result<()> {
		match self.width().storage() {
			Storage::Ext => Ok(()),
			Storage::Inl => Error::bitwidth_too_small(self.width().to_usize(), digit::BITS + 1).into()
		}
	}

	#[inline]
	fn verify_common_bitwidth<W>(&self, other: &W) -> Result<()>
		where W: Width
	{
		if self.width() == other.width() {
			Ok(())
		} else {
			Error::unmatching_bitwidths(self.width().to_usize(), digit::BITS + 1).into()
		}
	}
}

pub(crate) trait APIntImpl<I>
	where I: Width
{
	fn get(&self, n: usize) -> Result<Bit>;
	fn sign_bit(&self) -> Bit;

	fn ult(&self, other: &I) -> Result<bool>;
	fn slt(&self, other: &I) -> Result<bool>;
}

pub(crate) trait APIntMutImpl<I>
	where I: Width
{
	fn set(&mut self, n: usize) -> Result<()>;
	fn set_all(&mut self);
	fn unset(&mut self, n: usize) -> Result<()>;
	fn unset_all(&mut self);
	fn flip(&mut self, n: usize) -> Result<()>;
	fn flip_all(&mut self);

	fn bitnot_inplace(&mut self);
	fn bitand_inplace(&mut self, other: &I) -> Result<()>;
	fn bitor_inplace(&mut self, other: &I) -> Result<()>;
	fn bitxor_inplace(&mut self, other: &I) -> Result<()>;

	fn neg_inplace(&mut self);
	fn add_inplace(&mut self, other: &I) -> Result<()>;
	fn sub_inplace(&mut self, other: &I) -> Result<()>;
	fn mul_inplace(&mut self, other: &I) -> Result<()>;
	fn sdiv_inplace(&mut self, other: &I) -> Result<()>;
	fn udiv_inplace(&mut self, other: &I) -> Result<()>;
	fn srem_inplace(&mut self, other: &I) -> Result<()>;
	fn urem_inplace(&mut self, other: &I) -> Result<()>;

	fn shl_inplace(&mut self, other: &I) -> Result<()>;
	fn lshr_inplace(&mut self, other: &I) -> Result<()>;
	fn ashr_inplace(&mut self, other: &I) -> Result<()>;
}
