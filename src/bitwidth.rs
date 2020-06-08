use crate::{
    mem::{
        NonZeroUsize,
        TryFrom,
    },
    storage::Storage,
    BitPos,
    Digit,
    Result,
    ShiftAmount,
};

/// The `BitWidth` represents the length of an `ApInt`.
///
/// Its invariant restricts it to always be a positive, non-zero value.
/// Code that built's on top of `BitWidth` may and should use this invariant.
///
/// This is currently just a wrapper around `NonZeroUsize` (in case
/// future compiler optimizations can make use of it), but this is not
/// exposed because of the potential for feature flags and custom forks for
/// `apint` to use other internal types.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitWidth(NonZeroUsize);

impl From<NonZeroUsize> for BitWidth {
    /// Creates a `BitWidth` from the given `NonZeroUsize`.
    fn from(width: NonZeroUsize) -> Self {
        BitWidth(width)
    }
}

impl TryFrom<usize> for BitWidth {
    type Error = crate::Error;

    /// Creates a `BitWidth` from the given `usize`.
    ///
    /// # Errors
    ///
    /// - If the given `width` is equal to zero.
    fn try_from(width: usize) -> Result<BitWidth> {
        match NonZeroUsize::new(width) {
            Some(bitwidth) => Ok(BitWidth(bitwidth)),
            None => Err(crate::Error::invalid_zero_bitwidth()),
        }
    }
}

/// Convenience free function for converting a `usize` to a `BitWidth`.
///
/// # Panics
///
/// If `width == 0`, this function will panic
pub const fn bw(width: usize) -> BitWidth {
    // Ideally, the code here would be `width.try_into().ok().expect("tried to
    // ...");`, but we want this to be a `const` function.
    match NonZeroUsize::new(width) {
        None => {
            panic!(
                "Tried to construct an invalid BitWidth of 0 using the `apint::bw` \
                 function"
            )
        }
        Some(n) => BitWidth(n),
    }
}

impl BitWidth {
    // TODO: change to using `NonZeroUsize::new()` as soon as `unwrap`ing can be done.

    /// Width of a `Digit`
    pub(crate) const DIGIT: BitWidth =
        BitWidth(unsafe { NonZeroUsize::new_unchecked(Digit::BITS) });
    /// Width of a `DoubleDigit`
    pub(crate) const DOUBLE_DIGIT: BitWidth =
        BitWidth(unsafe { NonZeroUsize::new_unchecked(Digit::BITS * 2) });

    /// Returns `true` if the given `BitPos` is valid for this `BitWidth`.
    #[inline]
    pub(crate) fn is_valid_pos<P>(self, pos: P) -> bool
    where
        P: Into<BitPos>,
    {
        pos.into().to_usize() < self.to_usize()
    }

    /// Returns `true` if the given `ShiftAmount` is valid for this `BitWidth`.
    #[inline]
    pub(crate) fn is_valid_shift_amount<S>(self, shift_amount: S) -> bool
    where
        S: Into<ShiftAmount>,
    {
        shift_amount.into().to_usize() < self.to_usize()
    }

    /// Returns the `BitPos` for the most significant bit of an `ApInt` with
    /// this `BitWidth`.
    #[inline]
    pub(crate) fn msb_pos(self) -> BitPos {
        BitPos::from(self.to_usize() - 1)
    }
}

//  ===========================================================================
///  API
/// ===========================================================================
impl BitWidth {
    /// Converts this `BitWidth` into a `usize`.
    #[inline]
    pub fn to_usize(self) -> usize {
        self.0.get()
    }

    /// Returns the number of exceeding bits that is implied for `ApInt`
    /// instances with this `BitWidth`.
    ///
    /// For example for an `ApInt` with a `BitWidth` of `140` bits requires
    /// exactly `3` digits (assuming `Digit::BITS == 64` bits). The third
    /// however, only requires `140 - 128 = 12` bits of its `64` bits in
    /// total to represent the `ApInt` instance. So `excess_bits` returns
    /// `12` for a `BitWidth` that is equal to `140`.
    ///
    /// *Note:* A better name for this method has yet to be found!
    pub(crate) fn excess_bits(self) -> Option<usize> {
        match self.to_usize() % Digit::BITS {
            0 => None,
            n => Some(n),
        }
    }

    /// Returns the exceeding `BitWidth` of this `BitWidth`.
    ///
    /// *Note:* This is just a simple wrapper around the `excess_bits` method.
    ///         Read the documentation of `excess_bits` for more information
    ///         about what is actually returned by this.
    pub(crate) fn excess_width(self) -> Option<BitWidth> {
        match NonZeroUsize::new(self.to_usize() % Digit::BITS) {
            Some(bitwidth) => Some(BitWidth(bitwidth)),
            None => None,
        }
    }

    /// Returns a storage specifier that tells the caller if `ApInt`'s
    /// associated with this bitwidth require an external memory (`Ext`) to
    /// store their digits or may use inplace memory (`Inl`).
    ///
    /// *Note:* Maybe this method should be removed. A constructor for
    ///         `Storage` fits better for this purpose.
    #[inline]
    pub(crate) fn storage(self) -> Storage {
        Storage::from(self)
    }

    /// Returns the number of digits that are required to represent an
    /// `ApInt` with this `BitWidth`.
    ///
    /// *Note:* Maybe we should move this method somewhere else?
    #[inline]
    pub(crate) fn required_digits(self) -> usize {
        ((self.to_usize() - 1) / Digit::BITS) + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod excess_bits {
        use super::*;

        #[test]
        fn powers_of_two() {
            assert_eq!(bw(1).excess_bits(), Some(1));
            assert_eq!(bw(8).excess_bits(), Some(8));
            assert_eq!(bw(16).excess_bits(), Some(16));
            assert_eq!(bw(32).excess_bits(), Some(32));
            assert_eq!(bw(64).excess_bits(), None);
            assert_eq!(bw(128).excess_bits(), None);
        }

        #[test]
        fn multiples_of_50() {
            assert_eq!(bw(50).excess_bits(), Some(50));
            assert_eq!(bw(100).excess_bits(), Some(36));
            assert_eq!(bw(150).excess_bits(), Some(22));
            assert_eq!(bw(200).excess_bits(), Some(8));
            assert_eq!(bw(250).excess_bits(), Some(58));
            assert_eq!(bw(300).excess_bits(), Some(44));
        }
    }
}
