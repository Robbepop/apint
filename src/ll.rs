use digit::{Digit};
use digit;

/// Returns the result of a carry-add between `a` and `b` with
/// the given `carry`.
/// 
/// # Computes & Returns
/// 
/// result = a + b + carry
/// 
/// # Note
/// 
/// - The carry acts as input and will also store the
///   carry of this addition after the carry-add computation.
#[inline]
pub(crate) fn carry_add(a: Digit, b: Digit, carry: &mut Digit) -> Digit {
    let (hi, lo) = (a.dd() + b.dd() + carry.dd()).hi_lo();
    *carry = hi;
    lo
}

/// Returns the result of a borrow-sub between `a` and `b` with
/// the given `borrow`.
/// 
/// # Computes & Returns
/// 
/// result = a - b - borrow
/// 
/// # Note
/// 
/// - Do not be confused: In subtraction the "carry" actually is called "borrow".
/// - The borrow acts as input and will also store the borrow of this subtraction
///   after the borrow-sub computation.
#[inline]
pub(crate) fn borrow_sub(a: Digit, b: Digit, borrow: &mut Digit) -> Digit {
    let (hi, lo) = (digit::BASE + a.dd() - b.dd() - borrow.dd()).hi_lo();

    // This is the actual computation:
    //
    // We subtract from the Digit's base which is equal to 2^64.
    // The hi part then is the borrow for the next pair of Digits
    // whereas the lo part is the actual wrapped result.
    // 
    //     hi * (base) + lo        ==    1 * (base) + ai - bi - borrow
    // =>  a_i - b_i - borrow < 0   <==>   hi == 0

    *borrow = if hi.is_zero() { Digit::ONE } else { Digit::ZERO };
    lo
}
