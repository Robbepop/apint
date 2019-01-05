use crate::data::{Digit, DoubleDigit, ApInt};
use crate::info::{BitWidth};

/// Types that have an associated bit width may implement `Width`.
pub trait Width {
    /// Returns the bit width of `self`.
    fn width(&self) -> BitWidth;
}

impl Width for Digit {
    fn width(&self) -> BitWidth {
        BitWidth::from(Digit::BITS)
    }
}

impl Width for DoubleDigit {
    fn width(&self) -> BitWidth {
        BitWidth::from(Digit::BITS * 2)
    }
}

impl Width for ApInt {
    /// Returns the `BitWidth` of this `ApInt`.
    #[inline]
    fn width(&self) -> BitWidth {
        BitWidth::new(self.len_bits()).unwrap()
    }
}