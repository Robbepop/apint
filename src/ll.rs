use digit::{Digit};

/// Returns the result of a carry-add between `a` and `b` with
/// the given `carry`.
/// 
/// The carry acts as input and will also store the
/// carry of this operation after the carry-add computation.
#[inline]
pub(crate) fn carry_add_inout(a: Digit, b: Digit, carry: &mut Digit) -> Digit {
	let (hi, lo) = (a.dd() + b.dd() + carry.dd()).hi_lo();
	*carry = hi;
	lo
}
