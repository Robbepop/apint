use errors::{Error, Result};
use traits::{Width};
use bitpos::{BitPos};
use apint::{ShiftAmount};

#[inline]
pub(crate) fn verify_bit_access<T, P>(a: &T, pos: P) -> Result<()>
	where T: Width,
	      P: Into<BitPos>
{
	let pos = pos.into();
	let width = a.width();
	if !width.is_valid_pos(pos) {
		return Err(Error::invalid_bit_access(pos, width))
	}
	Ok(())
}

#[inline]
pub(crate) fn assert_bis_access<T, P>(a: &T, pos: P)
	where T: Width,
	      P: Into<BitPos>
{
	verify_bit_access(a, pos).unwrap()
}

#[inline]
pub(crate) fn verify_shift_amount<W, S>(a: &W, shift_amount: S) -> Result<()>
	where W: Width,
	      S: Into<ShiftAmount>
{
	let shift_amount = shift_amount.into();
	let width = a.width();
	if !width.is_valid_shift_amount(shift_amount) {
		return Err(Error::invalid_shift_amount(shift_amount, width))
	}
	Ok(())
}

#[inline]
pub(crate) fn assert_shift_amount<W, S>(a: &W, shift_amount: S)
	where W: Width,
	      S: Into<BitPos>
{
	verify_bit_access(a, shift_amount).unwrap()
}

#[inline]
pub(crate) fn verify_common_bitwidth<L, R>(lhs: &L, rhs: &R) -> Result<()>
	where L: Width,
	      R: Width
{
	let lw = lhs.width();
	let rw = rhs.width();
	if lw != rw {
		return Err(Error::unmatching_bitwidths(lw, rw))
	}
	Ok(())
}

#[inline]
pub(crate) fn assert_common_bitwidth<L, R>(lhs: &L, rhs: &R)
	where L: Width,
	      R: Width
{
	verify_common_bitwidth(lhs, rhs).unwrap()
}
