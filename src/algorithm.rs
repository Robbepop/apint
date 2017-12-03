use digit::{Digit, DoubleDigit};
use digit;
use digit_seq::{AsDigitSeq, AsDigitSeqMut};
use traits::{Width};
use checks;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct DigitAndCarry {
	digit: Digit,
	carry: Digit
}

impl DigitAndCarry {
	/// Creates a new `DigitAndCarry` from the given `Digit` a zero carry.
	#[inline]
	fn new(digit: Digit) -> DigitAndCarry {
		DigitAndCarry{digit, carry: digit::ZERO}
	}
}

/// Returns the result of `(a + b) + carry` and its implied carry value.
#[inline]
fn carry_add(a: Digit, b: DigitAndCarry) -> DigitAndCarry {
	let (hi, lo) = (a.dd() + b.digit.dd() + b.carry.dd()).hi_lo();
	DigitAndCarry{
		digit: lo,
		carry: hi
	}
}

/// Returns the result of `(a * b) + carry` and its implied carry value.
#[inline]
fn carry_mul(a: Digit, b: DigitAndCarry) -> DigitAndCarry {
	let (hi, lo) = (a.dd() * b.digit.dd() + b.carry.dd()).hi_lo();
	DigitAndCarry{
		digit: lo,
		carry: hi
	}
}

/// Returns the result of `(a + (b * c)) + carry` and its implied carry value.
#[inline]
fn carry_mul_add(a: Digit, b: Digit, c: Digit, carry: Digit) -> DigitAndCarry {
	let (hi, lo) = (a.dd() + (b.dd() * c.dd()) + carry.dd()).hi_lo();
	DigitAndCarry{
		digit: lo,
		carry: hi
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct DigitAndBorrow {
	digit: Digit,
	borrow: Digit
}

impl DigitAndBorrow {
	/// Creates a new `DigitAndBorrow` from the given `Digit` a zero borrow.
	#[inline]
	fn new(digit: Digit) -> DigitAndBorrow {
		DigitAndBorrow{digit, borrow: digit::ZERO}
	}
}

/// Returns the result of `a - b - borrow` and its implied borrow value.
#[inline]
fn borrow_sub(a: Digit, b: DigitAndBorrow) -> DigitAndBorrow {
	let (hi, lo) = (digit::BASE + a.dd() - b.digit.dd() - b.borrow.dd()).hi_lo();

	//     hi * (base) + lo        ==    1 * (base) + ai - bi - borrow
	// =>  ai - bi - borrow < 0   <==>   hi == 0

	DigitAndBorrow{
		digit: lo,
		borrow: Digit((hi == Digit::zero()) as digit::DigitRepr)
	}
}

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder.
///
/// **Note:** The caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is **not** true for an arbitrary numerator and denominator.
///
/// **Note:** This function also matches what the x86 divide instruction does.
#[inline]
fn wide_div(hi: Digit, lo: Digit, divisor: Digit) -> (Digit, Digit) {
	debug_assert!(hi < divisor);

	let lhs = DoubleDigit::from_hi_lo(hi, lo);
	let rhs = divisor.dd();

	((lhs / rhs).lo(), (lhs % rhs).lo())
}

/// Divides a digit sequence by a single digit.
/// 
/// Returns the remainder.
/// 
/// **TODO**: Find out what this exactly does and why it exits.
fn div_rem_digits_by_digit<'a, D>(seq: D, divisor: Digit) -> Digit
	where D: AsDigitSeqMut<'a>,
	      D::SeqMut: DoubleEndedIterator
{
	let mut seq = seq;
	let mut rem = digit::ZERO;
	for digit in seq.digits_mut().rev() {
		let (q, r) = wide_div(rem, *digit, divisor);
		*digit = q;
		rem = r;
	}
	rem
}

/// Add-assigns `rhs` to `lhs`: `lhs += rhs` where `lhs` and `rhs` are
/// digit sequences with an associated bit-width.
/// 
/// Returns the carry bit of the addition.
/// 
/// This is a raw implementation that can be reused by concrete `ApInt` types.
/// 
/// # Panics
/// 
/// - If `lhs` and `rhs` do not have a common bit-width.
fn add_assign_digits<'l, DL, DR>(lhs: DL, rhs: DR) -> Digit
	where DL: AsDigitSeqMut<'l> + Width,
	      DR: AsDigitSeq + Width
{
	checks::assert_common_bitwidth(&lhs, &rhs);

	let mut lhs = lhs;
	let mut dac = DigitAndCarry::new(digit::ZERO);
	for (l, r) in lhs.digits_mut().zip(rhs.digits()) {
		dac.digit = r;
		dac = carry_add(*l, dac);
		*l = dac.digit;
	}
	dac.carry
}

/// Sub-assigns `rhs` from `lhs`: `lhs -= rhs` where `lhs` and `rhs` are
/// digit sequences with an associated bit-width.
/// 
/// Returns the borrow bit of the subtraction.
/// 
/// This is the implementation that can be reused by concrete `ApInt` types.
/// 
/// # Panics
/// 
/// - If `lhs` and `rhs` do not have a common bit-width.
fn sub_assign_digits<'l, DL, DR>(lhs: DL, rhs: DR) -> Digit
	where DL: AsDigitSeqMut<'l> + Width,
	      DR: AsDigitSeq + Width
{
	checks::assert_common_bitwidth(&lhs, &rhs);

	unimplemented!()

	// let mut borrow = 0;

	// let len = cmp::min(a.len(), b.len());
	// let (a_lo, a_hi) = a.split_at_mut(len);
	// let (b_lo, b_hi) = b.split_at(len);

	// for (a, b) in a_lo.iter_mut().zip(b_lo) {
	//     *a = sbb(*a, *b, &mut borrow);
	// }

	// if borrow != 0 {
	//     for a in a_hi {
	//         *a = sbb(*a, 0, &mut borrow);
	//         if borrow == 0 { break }
	//     }
	// }

	// // note: we're _required_ to fail on underflow
	// assert!(borrow == 0 && b_hi.iter().all(|x| *x == 0),
	//         "Cannot subtract b from a because b is larger than a.");
}
