use crate::data::Digit;
use crate::info::{Error, Result, Width};

/// Represents an amount of bits to shift an `ApInt`.
/// 
/// The purpose of this type is to create a generic abstraction over input types that may act as a
/// `ShiftAmount` for shift operations.
/// 
/// Shift amounts can only be in the range [0, bit width of the `ApInt`) when used as arguments to
/// the shifting functions in this crate, otherwise they return errors. There is a good reason for
/// not allowing the shift amount to be an arbitrary amount and, for example, making a left shift
/// by 64 or more on a `ApInt` of width 64 simply make it zero.
///
/// One reason is that internally in all shift functions, there naturally arise expressions such as
/// `digit_val.wrapping_shl(shift_amount)` which will panic when that shift is equal to or greater
/// than the bitwidth of whatever `Digit` type the library is using.
///
/// Another reason is that shifts could be defined to be like
/// `apint.wrapping_shift(shift % apint.width())`, which is in fact how some CPUs shift their
/// machine integers. This is why Rust makes `1u32.wrapping_shl(32)` panic, since different CPUs
/// use different conventions on what happens when the shift is equal to or greater than the
/// bitwidth of a type.
///
/// Instead, it is almost always more performant and clearer on the User's side to prevent the shift
/// amount from going outside the range by using expressions like the following, depending on the
/// functionality desired:
///
/// if the shifting should go to zero when `shift >= apint.width()`:
/// ```
/// use apint::{ApInt, Width, BitWidth};
/// let w = BitWidth::new(42).unwrap();
/// let zero = ApInt::zero(w);
/// let shift = 50;
/// let mut lhs = ApInt::one(w);
/// if shift >= lhs.width().to_usize() {
///     lhs.strict_assign(&zero).unwrap();
/// } else {
///     lhs.wrapping_shl_assign(shift);
/// }
/// assert_eq!(lhs, zero);
/// ```
/// 
/// if the shifting should act like it wraps around (not like `rotate_left_assign`, but a wrapping
/// around of the `ShiftAmount`):
/// ```
/// use apint::{ApInt, Width, BitWidth};
/// let w = BitWidth::new(42).unwrap();
/// let shift = 50;
/// let mut lhs = ApInt::one(w);
/// lhs.wrapping_shl_assign(shift % 42);
/// assert_eq!(lhs, ApInt::from(256u64).into_truncate(w).unwrap());
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShiftAmount(usize);

impl From<usize> for ShiftAmount {
    /// Returns a new `ShiftAmount` from the given `usize`.
    #[inline]
    fn from(val: usize) -> ShiftAmount {
        ShiftAmount(val)
    }
}

impl ShiftAmount {
    /// Returns the internal shift amount representation as `usize`.
    pub fn to_usize(self) -> usize {
        self.0
    }

    /// Returns if the shift amount is zero
    pub(crate) fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Returns a tuple of the number of digits this `ShiftAmount` will leap over and the number of
    /// bits within a single digit this `ShiftAmount` will leap over.
    /// 
    /// # Examples
    /// 
    /// - `ShiftAmount(50)` leaps over 0 digits and 50 bits.
    /// - `ShiftAmount(64)` leaps over 1 digits and 0 bits.
    /// - `ShiftAmount(100)` leaps over 1 digits and 28 bits.
    /// - `ShiftAmount(150)` leaps over 2 digits and 22 bits.
    pub(crate) fn digit_bit_steps(self) -> (usize, usize) {
        (self.to_usize() / Digit::BITS, self.to_usize() % Digit::BITS)
    }

    #[inline]
    pub(crate) fn verify_shift_amount<W>(self, a: &W) -> Result<()>
        where W: Width,
    {
        let width = a.width();
        if !width.is_valid_shift_amount(self) {
            return Err(Error::invalid_shift_amount(self, width))
        }
        Ok(())
    }
}