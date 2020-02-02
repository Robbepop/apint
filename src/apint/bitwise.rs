use crate::{
    apint::{
        utils::{
            DataAccess,
            DataAccessMut,
        },
        ApInt,
    },
    bitpos::BitPos,
    checks,
    digit::{
        Bit,
        Digit,
    },
    errors::Result,
    traits::Width,
    utils::{
        forward_mut_impl,
        try_forward_bin_mut_impl,
    },
};

use core::ops::{
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Not,
};

/// # Bitwise Operations
impl ApInt {
    /// Flips all bits of `self` and returns the result.
    pub fn into_bitnot(self) -> Self {
        forward_mut_impl(self, ApInt::bitnot)
    }

    /// Flip all bits of this `ApInt` inplace.
    pub fn bitnot(&mut self) {
        self.modify_digits(|digit| digit.not_inplace());
        self.clear_unused_bits();
    }

    /// Tries to bit-and assign this `ApInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitand(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::bitand_assign)
    }

    /// Bit-and assigns all bits of this `ApInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitand_assign(&mut self, rhs: &ApInt) -> Result<()> {
        self.modify_zipped_digits(rhs, |l, r| *l &= r)
    }

    /// Tries to bit-and assign this `ApInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitor(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::bitor_assign)
    }

    /// Bit-or assigns all bits of this `ApInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitor_assign(&mut self, rhs: &ApInt) -> Result<()> {
        self.modify_zipped_digits(rhs, |l, r| *l |= r)
    }

    /// Tries to bit-xor assign this `ApInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitxor(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::bitxor_assign)
    }

    /// Bit-xor assigns all bits of this `ApInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitxor_assign(&mut self, rhs: &ApInt) -> Result<()> {
        self.modify_zipped_digits(rhs, |l, r| *l ^= r)
    }
}

/// # Bitwise Access
impl ApInt {
    /// Returns the bit at the given bit position `pos`.
    ///
    /// This returns
    ///
    /// - `Bit::Set` if the bit at `pos` is `1`
    /// - `Bit::Unset` otherwise
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `ApInt`.
    pub fn get_bit_at<P>(&self, pos: P) -> Result<Bit>
    where
        P: Into<BitPos>,
    {
        let pos = pos.into();
        checks::verify_bit_access(self, pos)?;
        match self.access_data() {
            DataAccess::Inl(digit) => digit.get(pos),
            DataAccess::Ext(digits) => {
                let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
                digits[digit_pos].get(bit_pos)
            }
        }
    }

    /// Sets the bit at the given bit position `pos` to one (`1`).
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `ApInt`.
    pub fn set_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        let pos = pos.into();
        checks::verify_bit_access(self, pos)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => digit.set(pos),
            DataAccessMut::Ext(digits) => {
                let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
                digits[digit_pos].set(bit_pos)
            }
        }
    }

    /// Sets the bit at the given bit position `pos` to zero (`0`).
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `ApInt`.
    pub fn unset_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        let pos = pos.into();
        checks::verify_bit_access(self, pos)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => digit.unset(pos),
            DataAccessMut::Ext(digits) => {
                let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
                digits[digit_pos].unset(bit_pos)
            }
        }
    }

    /// Flips the bit at the given bit position `pos`.
    ///
    /// # Note
    ///
    /// - If the bit at the given position was `0` it will be `1` after this
    ///   operation and vice versa.
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `ApInt`.
    pub fn flip_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        let pos = pos.into();
        checks::verify_bit_access(self, pos)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => digit.flip(pos),
            DataAccessMut::Ext(digits) => {
                let (digit_pos, bit_pos) = pos.to_digit_and_bit_pos();
                digits[digit_pos].flip(bit_pos)
            }
        }
    }

    /// Sets all bits of this `ApInt` to one (`1`).
    pub fn set_all(&mut self) {
        self.modify_digits(|digit| digit.set_all());
        self.clear_unused_bits();
    }

    /// Returns``true` if all bits in the `ApInt` are set.
    pub fn is_all_set(&self) -> bool {
        let (msb, rest) = self.split_most_significant_digit();
        if let Some(excess_bits) = self.width().excess_bits() {
            if msb.repr().count_ones() as usize != excess_bits {
                return false
            }
        }
        rest.iter().all(|d| *d == Digit::ONES)
    }

    /// Sets all bits of this `ApInt` to zero (`0`).
    pub fn unset_all(&mut self) {
        self.modify_digits(|digit| digit.unset_all());
    }

    /// Returns `true` if all bits in the `ApInt` are unset.
    pub fn is_all_unset(&self) -> bool {
        self.is_zero()
    }

    /// Flips all bits of this `ApInt`.
    pub fn flip_all(&mut self) {
        // TODO: remove since equal to ApInt::bitnot_assign
        self.modify_digits(|digit| digit.flip_all());
        self.clear_unused_bits();
    }

    /// Returns the sign bit of this `ApInt`.
    ///
    /// **Note:** This is equal to the most significant bit of this `ApInt`.
    pub fn sign_bit(&self) -> Bit {
        self.most_significant_bit()
    }

    /// Sets the sign bit of this `ApInt` to one (`1`).
    pub fn set_sign_bit(&mut self) {
        let sign_bit_pos = self.width().sign_bit_pos();
        self.set_bit_at(sign_bit_pos).expect(
            "`BitWidth::sign_bit_pos` always returns a valid `BitPos`
                     for usage in the associated `ApInt` for operating on bits.",
        )
    }

    /// Sets the sign bit of this `ApInt` to zero (`0`).
    pub fn unset_sign_bit(&mut self) {
        let sign_bit_pos = self.width().sign_bit_pos();
        self.unset_bit_at(sign_bit_pos).expect(
            "`BitWidth::sign_bit_pos` always returns a valid `BitPos`
                     for usage in the associated `ApInt` for operating on bits.",
        )
    }

    /// Flips the sign bit of this `ApInt`.
    ///
    /// # Note
    ///
    /// - If the sign bit was `0` it will be `1` after this operation and vice
    ///   versa.
    /// - Depending on the interpretation of the `ApInt` this operation changes
    ///   its signedness.
    pub fn flip_sign_bit(&mut self) {
        let sign_bit_pos = self.width().sign_bit_pos();
        self.flip_bit_at(sign_bit_pos).expect(
            "`BitWidth::sign_bit_pos` always returns a valid `BitPos`
                     for usage in the associated `ApInt` for operating on bits.",
        )
    }
}

/// # Bitwise utility methods.
impl ApInt {
    /// Returns the number of ones in the binary representation of this `ApInt`.
    pub fn count_ones(&self) -> usize {
        self.as_digit_slice()
            .iter()
            .map(|d| d.repr().count_ones() as usize)
            .sum::<usize>()
    }

    /// Returns the number of zeros in the binary representation of this
    /// `ApInt`.
    pub fn count_zeros(&self) -> usize {
        let zeros = self
            .as_digit_slice()
            .iter()
            .map(|d| d.repr().count_zeros() as usize)
            .sum::<usize>();
        // Since `ApInt` instances with width's that are no powers of two
        // have unused excess bits that are always zero we need to cut them off
        // for a correct implementation of this operation.
        zeros - (Digit::BITS - self.width().excess_bits().unwrap_or(Digit::BITS))
    }

    /// Returns the number of leading zeros in the binary representation of this
    /// `ApInt`.
    pub fn leading_zeros(&self) -> usize {
        let mut zeros = 0;
        for d in self.as_digit_slice().iter().rev() {
            let leading_zeros = d.repr().leading_zeros() as usize;
            zeros += leading_zeros;
            if leading_zeros != Digit::BITS {
                break
            }
        }
        zeros - (Digit::BITS - self.width().excess_bits().unwrap_or(Digit::BITS))
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// this `ApInt`.
    pub fn trailing_zeros(&self) -> usize {
        let mut zeros = 0;
        for d in self.as_digit_slice() {
            let trailing_zeros = d.repr().trailing_zeros() as usize;
            zeros += trailing_zeros;
            if trailing_zeros != Digit::BITS {
                break
            }
        }
        if zeros >= self.width().to_usize() {
            zeros -= Digit::BITS - self.width().excess_bits().unwrap_or(Digit::BITS);
        }
        zeros
    }
}

//  ===========================================================================
//  `Not` (bitwise) impls
//  ===========================================================================

impl Not for ApInt {
    type Output = ApInt;

    fn not(self) -> Self::Output {
        forward_mut_impl(self, ApInt::bitnot)
    }
}

//  ===========================================================================
//  `BitAnd` impls
//  ===========================================================================

impl<'a> BitAnd<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitand(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitOr` impls
//  ===========================================================================

impl<'a> BitOr<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitXor` impls
//  ===========================================================================

impl<'a> BitXor<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitxor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitAndAssign`, `BitOrAssign` and `BitXorAssign` impls
//  ===========================================================================

impl<'a> BitAndAssign<&'a ApInt> for ApInt {
    fn bitand_assign(&mut self, rhs: &'a ApInt) {
        self.bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a ApInt> for ApInt {
    fn bitor_assign(&mut self, rhs: &'a ApInt) {
        self.bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a ApInt> for ApInt {
    fn bitxor_assign(&mut self, rhs: &'a ApInt) {
        self.bitxor_assign(rhs).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::bitwidth::BitWidth;

    #[test]
    fn count_ones() {
        assert_eq!(ApInt::zero(BitWidth::w1()).count_ones(), 0);
        assert_eq!(ApInt::zero(BitWidth::w8()).count_ones(), 0);
        assert_eq!(ApInt::zero(BitWidth::w16()).count_ones(), 0);
        assert_eq!(ApInt::zero(BitWidth::w32()).count_ones(), 0);
        assert_eq!(ApInt::zero(BitWidth::w64()).count_ones(), 0);
        assert_eq!(ApInt::zero(BitWidth::w128()).count_ones(), 0);

        assert_eq!(ApInt::one(BitWidth::w1()).count_ones(), 1);
        assert_eq!(ApInt::one(BitWidth::w8()).count_ones(), 1);
        assert_eq!(ApInt::one(BitWidth::w16()).count_ones(), 1);
        assert_eq!(ApInt::one(BitWidth::w32()).count_ones(), 1);
        assert_eq!(ApInt::one(BitWidth::w64()).count_ones(), 1);
        assert_eq!(ApInt::one(BitWidth::w128()).count_ones(), 1);

        assert_eq!(ApInt::signed_min_value(BitWidth::w1()).count_ones(), 1);
        assert_eq!(ApInt::signed_min_value(BitWidth::w8()).count_ones(), 1);
        assert_eq!(ApInt::signed_min_value(BitWidth::w16()).count_ones(), 1);
        assert_eq!(ApInt::signed_min_value(BitWidth::w32()).count_ones(), 1);
        assert_eq!(ApInt::signed_min_value(BitWidth::w64()).count_ones(), 1);
        assert_eq!(ApInt::signed_min_value(BitWidth::w128()).count_ones(), 1);

        assert_eq!(ApInt::signed_max_value(BitWidth::w1()).count_ones(), 0);
        assert_eq!(ApInt::signed_max_value(BitWidth::w8()).count_ones(), 8 - 1);
        assert_eq!(
            ApInt::signed_max_value(BitWidth::w16()).count_ones(),
            16 - 1
        );
        assert_eq!(
            ApInt::signed_max_value(BitWidth::w32()).count_ones(),
            32 - 1
        );
        assert_eq!(
            ApInt::signed_max_value(BitWidth::w64()).count_ones(),
            64 - 1
        );
        assert_eq!(
            ApInt::signed_max_value(BitWidth::w128()).count_ones(),
            128 - 1
        );
    }

    #[test]
    fn count_zeros() {
        assert_eq!(ApInt::zero(BitWidth::w1()).count_zeros(), 1);
        assert_eq!(ApInt::zero(BitWidth::w8()).count_zeros(), 8);
        assert_eq!(ApInt::zero(BitWidth::w16()).count_zeros(), 16);
        assert_eq!(ApInt::zero(BitWidth::w32()).count_zeros(), 32);
        assert_eq!(ApInt::zero(BitWidth::w64()).count_zeros(), 64);
        assert_eq!(ApInt::zero(BitWidth::w128()).count_zeros(), 128);

        assert_eq!(ApInt::one(BitWidth::w1()).count_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w8()).count_zeros(), 8 - 1);
        assert_eq!(ApInt::one(BitWidth::w16()).count_zeros(), 16 - 1);
        assert_eq!(ApInt::one(BitWidth::w32()).count_zeros(), 32 - 1);
        assert_eq!(ApInt::one(BitWidth::w64()).count_zeros(), 64 - 1);
        assert_eq!(ApInt::one(BitWidth::w128()).count_zeros(), 128 - 1);

        assert_eq!(ApInt::signed_min_value(BitWidth::w1()).count_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w8()).count_zeros(), 8 - 1);
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w16()).count_zeros(),
            16 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w32()).count_zeros(),
            32 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w64()).count_zeros(),
            64 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w128()).count_zeros(),
            128 - 1
        );

        assert_eq!(ApInt::signed_max_value(BitWidth::w1()).count_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w8()).count_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w16()).count_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w32()).count_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w64()).count_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w128()).count_zeros(), 1);
    }

    #[test]
    fn leading_zeros() {
        assert_eq!(ApInt::zero(BitWidth::w1()).leading_zeros(), 1);
        assert_eq!(ApInt::zero(BitWidth::w8()).leading_zeros(), 8);
        assert_eq!(ApInt::zero(BitWidth::w16()).leading_zeros(), 16);
        assert_eq!(ApInt::zero(BitWidth::w32()).leading_zeros(), 32);
        assert_eq!(ApInt::zero(BitWidth::w64()).leading_zeros(), 64);
        assert_eq!(ApInt::zero(BitWidth::w128()).leading_zeros(), 128);

        assert_eq!(ApInt::one(BitWidth::w1()).leading_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w8()).leading_zeros(), 8 - 1);
        assert_eq!(ApInt::one(BitWidth::w16()).leading_zeros(), 16 - 1);
        assert_eq!(ApInt::one(BitWidth::w32()).leading_zeros(), 32 - 1);
        assert_eq!(ApInt::one(BitWidth::w64()).leading_zeros(), 64 - 1);
        assert_eq!(ApInt::one(BitWidth::w128()).leading_zeros(), 128 - 1);

        assert_eq!(ApInt::signed_min_value(BitWidth::w1()).leading_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w8()).leading_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w16()).leading_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w32()).leading_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w64()).leading_zeros(), 0);
        assert_eq!(ApInt::signed_min_value(BitWidth::w128()).leading_zeros(), 0);

        assert_eq!(ApInt::signed_max_value(BitWidth::w1()).leading_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w8()).leading_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w16()).leading_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w32()).leading_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w64()).leading_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w128()).leading_zeros(), 1);
    }

    #[test]
    fn trailing_zeros() {
        assert_eq!(ApInt::zero(BitWidth::w1()).trailing_zeros(), 1);
        assert_eq!(ApInt::zero(BitWidth::w8()).trailing_zeros(), 8);
        assert_eq!(ApInt::zero(BitWidth::w16()).trailing_zeros(), 16);
        assert_eq!(ApInt::zero(BitWidth::w32()).trailing_zeros(), 32);
        assert_eq!(ApInt::zero(BitWidth::w64()).trailing_zeros(), 64);
        assert_eq!(ApInt::zero(BitWidth::w128()).trailing_zeros(), 128);

        assert_eq!(ApInt::one(BitWidth::w1()).trailing_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w8()).trailing_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w16()).trailing_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w32()).trailing_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w64()).trailing_zeros(), 0);
        assert_eq!(ApInt::one(BitWidth::w128()).trailing_zeros(), 0);

        assert_eq!(ApInt::signed_min_value(BitWidth::w1()).trailing_zeros(), 0);
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w8()).trailing_zeros(),
            8 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w16()).trailing_zeros(),
            16 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w32()).trailing_zeros(),
            32 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w64()).trailing_zeros(),
            64 - 1
        );
        assert_eq!(
            ApInt::signed_min_value(BitWidth::w128()).trailing_zeros(),
            128 - 1
        );

        assert_eq!(ApInt::signed_max_value(BitWidth::w1()).trailing_zeros(), 1);
        assert_eq!(ApInt::signed_max_value(BitWidth::w8()).trailing_zeros(), 0);
        assert_eq!(ApInt::signed_max_value(BitWidth::w16()).trailing_zeros(), 0);
        assert_eq!(ApInt::signed_max_value(BitWidth::w32()).trailing_zeros(), 0);
        assert_eq!(ApInt::signed_max_value(BitWidth::w64()).trailing_zeros(), 0);
        assert_eq!(
            ApInt::signed_max_value(BitWidth::w128()).trailing_zeros(),
            0
        );
    }

    mod is_all_set {
        use super::*;

        #[test]
        fn simple_false() {
            let input = ApInt::from(0b0001_1011_0110_0111_u16);
            assert_eq!(input.width(), BitWidth::w16());
            assert_eq!(input.count_ones(), 9);
            assert!(!input.is_all_set());
        }

        #[test]
        fn simple_true() {
            let input = ApInt::all_set(BitWidth::w32());
            assert_eq!(input.width(), BitWidth::w32());
            assert_eq!(input.count_ones(), 32);
            assert!(input.is_all_set());
        }
    }

    mod is_all_unset {
        use super::*;

        #[test]
        fn simple_false() {
            let input = ApInt::from(0b0001_1011_0110_0111_u16);
            assert_eq!(input.width(), BitWidth::w16());
            assert_eq!(input.count_ones(), 9);
            assert_eq!(input.is_zero(), input.is_all_unset());
        }

        #[test]
        fn simple_true() {
            let input = ApInt::all_unset(BitWidth::w32());
            assert_eq!(input.width(), BitWidth::w32());
            assert_eq!(input.count_ones(), 0);
            assert_eq!(input.is_zero(), input.is_all_unset());
        }
    }
}
