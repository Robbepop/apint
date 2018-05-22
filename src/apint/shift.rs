use apint::{ApInt};
use apint::utils::{DataAccessMut};
use errors::{Result};
use checks;
use digit;
use digit::{Bit, Digit};
use traits::{Width};
use utils::{try_forward_bin_mut_impl};

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

/// # Shift Operations
impl ApInt {

    /// Shift this `ApInt` left by the given `shift_amount` bits.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        let shift_amount = shift_amount.into();
        checks::verify_shift_amount(self, shift_amount)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                *digit.repr_mut() <<= shift_amount.to_usize();
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    let digits_len  = digits.len();
                    {
                        use std::ptr;
                        let src_ptr = digits.as_mut_ptr();
                        unsafe {
                            let dst_ptr = src_ptr.offset(digit_steps as isize);
                            ptr::copy(src_ptr, dst_ptr, digits_len - digit_steps)
                        }
                    }
                    digits.iter_mut()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::zero());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps != 0 {
                    let mut carry = 0;
                    for elem in digits[digit_steps..].iter_mut() {
                        let repr = elem.repr();
                        let new_carry = repr >> (digit::BITS - bit_steps);
                        *elem = Digit((repr << bit_steps) | carry);
                        carry = new_carry;
                    }
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Shift this `ApInt` left by the given `shift_amount` bits and returns the result.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_shl<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_shl_assign)
    }

    /// Logically right-shifts this `ApInt` by the given `shift_amount` bits.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_lshr_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        let shift_amount = shift_amount.into();
        checks::verify_shift_amount(self, shift_amount)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                *digit.repr_mut() >>= shift_amount.to_usize();
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    digits.rotate_left(digit_steps);
                    digits.iter_mut()
                          .rev()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::zero());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps > 0 {
                    let mut borrow = 0;
                    for elem in digits.iter_mut().rev() {
                        let repr = elem.repr();
                        let new_borrow = repr << (digit::BITS - bit_steps);
                        *elem = Digit((repr >> bit_steps) | borrow);
                        borrow = new_borrow;
                    }
                }
            }
        }
        Ok(())
    }

    /// Logically right-shifts this `ApInt` by the given `shift_amount` bits
    /// and returns the result.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_lshr<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_lshr_assign)
    }

    /// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Note
    /// 
    /// Arithmetic shifting copies the sign bit instead of filling up with zeros.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_ashr_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        if self.sign_bit() == Bit::Unset {
            return self.wrapping_lshr_assign(shift_amount)
        }
        let shift_amount = shift_amount.into();
        checks::verify_shift_amount(self, shift_amount)?;
        let width = self.width();
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                let mut signed = digit.clone();
                signed.sign_extend_from(width).unwrap();
                let signed = signed.repr() as i64;
                let shifted = signed >> shift_amount.to_usize();
                *digit.repr_mut() = shifted as u64;
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    digits.rotate_left(digit_steps);
                    digits.iter_mut()
                          .rev()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::all_set());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps > 0 {
                    let mut borrow = 0xFFFF_FFFF_FFFF_FFFF << (digit::BITS - bit_steps);
                    for elem in digits.iter_mut().rev().skip(digit_steps) {
                        let repr = elem.repr();
                        let new_borrow = repr << (digit::BITS - bit_steps);
                        *elem = Digit((repr >> bit_steps) | borrow);
                        borrow = new_borrow;
                    }
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits
    /// and returns the result.
    /// 
    /// This operation is inplace and will **not** allocate memory.
    /// 
    /// # Note
    /// 
    /// Arithmetic shifting copies the sign bit instead of filling up with zeros.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_ashr<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_ashr_assign)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_reprs_w64() -> impl Iterator<Item = u64> {
        vec![
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0x0000_0000_0000_0000,
            0x5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA,
            0xFFFF_FFFF_FFFF_FFFF,
        ]
        .into_iter()
    }

    fn test_apints_w64() -> impl Iterator<Item = ApInt> {
        test_reprs_w64().map(ApInt::from_u64)
    }

    fn test_reprs_w128() -> impl Iterator<Item = u128> {
        vec![
            0x0123_4567_89AB_CDEF_0011_2233_4455_6677,
            0xFEDC_BA98_7654_3210_7766_5544_3322_1100,
            0x0000_0000_0000_0000_0000_0000_0000_0001,
            0x8000_0000_0000_0000_0000_0000_0000_0000,
            0x0000_0000_0000_0000_0000_0000_0000_0000,
            0x5555_5555_5555_5555_5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        ]
        .into_iter()
    }

    fn test_apints_w128() -> impl Iterator<Item = ApInt> {
        test_reprs_w128().map(ApInt::from_u128)
    }

    mod shl {
        use super::*;

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_shl_assign(shamt).unwrap();
                    let expected = ApInt::from_u64(repr << shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_shl_assign(shamt).unwrap();
                    let expected = ApInt::from_u128(repr << shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_xtra_large_ok() {
            use digit;
            let d0 = 0xFEDC_BA98_7654_3210;
            let d1 = 0x5555_5555_4444_4444;
            let d2 = 0xAAAA_AAAA_CCCC_CCCC;
            let d3 = 0xFFFF_7777_7777_FFFF;
            let input: [u64; 4] = [d0, d1, d2, d3];
            {
                let shamt = 100;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 1);
                assert_eq!(bit_steps, 36);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d1 << bit_steps) | (d2 >> (digit::BITS - bit_steps)),
                    (d2 << bit_steps) | (d3 >> (digit::BITS - bit_steps)),
                    (d3 << bit_steps),
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
            {
                let shamt = 150;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 2);
                assert_eq!(bit_steps, 22);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d2 << bit_steps) | (d3 >> (digit::BITS - bit_steps)),
                    (d3 << bit_steps),
                    0,
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
            {
                let shamt = 200;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 3);
                assert_eq!(bit_steps, 8);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d3 << bit_steps),
                    0,
                    0,
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_shl_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_shl_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_shl_assign(shamt).unwrap();
                    let y = y.into_wrapping_shl(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_shl_assign(shamt).unwrap();
                    let y = y.into_wrapping_shl(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }

    mod lshr {
        use super::*;

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_lshr_assign(shamt).unwrap();
                    let expected = ApInt::from_u64(repr >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_lshr_assign(shamt).unwrap();
                    let expected = ApInt::from_u128(repr >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_lshr_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_lshr_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_lshr_assign(shamt).unwrap();
                    let y = y.into_wrapping_lshr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_lshr_assign(shamt).unwrap();
                    let y = y.into_wrapping_lshr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }

    mod ashr {
        use super::*;

        #[test]
        fn regression_stevia_01() {
            let input = ApInt::from_i32(-8);
            let expected = ApInt::from_u32(0x_FFFF_FFFE);
            assert_eq!(input.into_wrapping_ashr(ShiftAmount::from(2)).unwrap(), expected);
        }

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_ashr_assign(shamt).unwrap();
                    let expected = ApInt::from_i64((repr as i64) >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_ashr_assign(shamt).unwrap();
                    let expected = ApInt::from_i128((repr as i128) >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_ashr_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_ashr_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_ashr_assign(shamt).unwrap();
                    let y = y.into_wrapping_ashr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_ashr_assign(shamt).unwrap();
                    let y = y.into_wrapping_ashr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }
}
