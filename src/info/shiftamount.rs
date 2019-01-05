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
/// by 64 or more on a `ApInt` of width 64 simply make it zero. Internally in all shift functions,
/// there naturally arise expressions such as `subdigit.wrapping_shl(shift_amount)` which will panic
/// when that shift is equal to or greater than the bitwidth of whatever type the library is set to
/// use (typically `u32` or `u64`). Instead, it is almost always more performant on the User's side
/// to prevent the shift amount from going outside the range by using expressions like the
/// following, depending on the functionality desired:
/// 
/// (this is just pseudocode to get the idea through)
/// if the shifting should go to zero when `shift >= apint.width()`:
/// `if shift > apint.width {return zero} else {return apint.wrapping_shift(shift)}`
/// 
/// if the shifting should act like it is the remainder of the shift with the bit width:
/// `return apint.wrapping_shift(shift % apint.width())`
/// Note: the above is used more commonly with the circular shift functions like
/// `ApInt::into_rotate_left`, but can also happen to other kinds of shifting. The reason even
/// wrapping shifts on Rust integers like `1u32.wrapping_shl(32)` will panic is due to different
/// CPUs having different conventions.
/// 
/// The compiler will be hinted to by bounds checks and User side conditionals that checks can be
/// eliminated and improve code performance.
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
    #[inline]
    pub fn to_usize(self) -> usize {
        self.0
    }

    /// Returns the number of digits this `ShiftAmount` will leap over.
    /// 
    /// # Examples
    /// 
    /// - `ShiftAmount(50)` leaps over zero digits.
    /// - `ShiftAmount(64)` leaps exactly over one digit.
    /// - `ShiftAmount(100)` leaps over 1 digit.
    /// - `ShiftAmount(150)` leaps over 2 digits.
    #[inline]
    pub(crate) fn digit_steps(self) -> usize {
        self.to_usize() / Digit::BITS
    }

    /// Returns the number of bits within a single digit this
    /// `ShiftAmount` will leap over.
    /// 
    /// # TODO
    /// 
    /// Maybe adding `left_bit_steps` and `right_bit_steps` is better?
    /// 
    /// # Examples
    /// 
    /// - `ShiftAmount(50)` leaps over `50` bits.
    /// - `ShiftAmount(64)` leaps exactly over `0` bits.
    /// - `ShiftAmount(100)` leaps over `28` bits.
    /// - `ShiftAmount(150)` leaps over `22` bits.
    #[inline]
    pub(crate) fn bit_steps(self) -> usize {
        self.to_usize() % Digit::BITS
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