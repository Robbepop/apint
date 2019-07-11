use crate::data::Digit;
use crate::info::{Error, Result, Width};

/// Represents an amount of bits to shift an `ApInt`.
/// 
/// The purpose of this type is to create a generic abstraction
/// over input types that may act as a `ShiftAmount` for shift
/// operations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShiftAmount(usize);

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
    pub(in apint) fn digit_steps(self) -> usize {
        self.to_usize() / digit::BITS
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
    pub(in apint) fn bit_steps(self) -> usize {
        self.to_usize() % digit::BITS
    }
}

impl From<usize> for ShiftAmount {
    /// Returns a new `ShiftAmount` from the given `usize`.
    #[inline]
    fn from(val: usize) -> ShiftAmount {
        ShiftAmount(val)
    }
}