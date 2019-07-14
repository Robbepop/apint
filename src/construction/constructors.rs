use crate::data::{ApInt, Digit, DigitRepr};
use crate::info::{BitWidth, Error, Result};

use smallvec::SmallVec;

/// # Constructors
impl ApInt {
    /// Creates a new `ApInt` from the given boolean value with a bit width of `1`.
    /// 
    /// When `bit` is `false`, the single bit in the `ApInt` is 0, otherwise it is 1.
    pub fn from_bool(bit: bool) -> ApInt {
        ApInt::new_inl(BitWidth::w1(), Digit(bit as DigitRepr))
    }

    /// Creates a new `ApInt` from a given `i8` value with a bit-width of 8.
    #[inline]
    pub fn from_i8(val: i8) -> ApInt {
        ApInt::from_u8(val as u8)
    }

    /// Creates a new `ApInt` from a given `u8` value with a bit-width of 8.
    #[inline]
    pub fn from_u8(val: u8) -> ApInt {
        ApInt::new_inl(BitWidth::w8(), Digit(u64::from(val)))
    }

    /// Creates a new `ApInt` from a given `i16` value with a bit-width of 16.
    #[inline]
    pub fn from_i16(val: i16) -> ApInt {
        ApInt::from_u16(val as u16)
    }

    /// Creates a new `ApInt` from a given `u16` value with a bit-width of 16.
    #[inline]
    pub fn from_u16(val: u16) -> ApInt {
        ApInt::new_inl(BitWidth::w16(), Digit(u64::from(val)))
    }

    /// Creates a new `ApInt` from a given `i32` value with a bit-width of 32.
    #[inline]
    pub fn from_i32(val: i32) -> ApInt {
        ApInt::from_u32(val as u32)
    }

    /// Creates a new `ApInt` from a given `u32` value with a bit-width of 32.
    #[inline]
    pub fn from_u32(val: u32) -> ApInt {
        ApInt::new_inl(BitWidth::w32(), Digit(u64::from(val)))
    }

    /// Creates a new `ApInt` from a given `i64` value with a bit-width of 64.
    #[inline]
    pub fn from_i64(val: i64) -> ApInt {
        ApInt::from_u64(val as u64)
    }

    /// Creates a new `ApInt` from a given `u64` value with a bit-width of 64.
    #[inline]
    pub fn from_u64(val: u64) -> ApInt {
        ApInt::new_inl(BitWidth::w64(), Digit(val))
    }

    /// Creates a new `ApInt` from a given `i128` value with a bit-width of 128.
    #[inline]
    pub fn from_i128(val: i128) -> ApInt {
        ApInt::from_u128(val as u128)
    }

    /// Creates a new `ApInt` from a given `u128` value with a bit-width of 128.
    pub fn from_u128(val: u128) -> ApInt {
        let hi = (val >> Digit::BITS) as u64;
        let lo = (val & ((1u128 << 64) - 1)) as u64;
        ApInt::from([hi, lo])
    }

    /// Creates a new `ApInt` from the given iterator over `Digit`s.
    /// 
    /// This results in `ApInt` instances with bitwidths that are a multiple
    /// of a `Digit`s bitwidth (e.g. 64 bit).
    /// 
    /// Users of this API may truncate, extend or simply resize the resulting
    /// `ApInt` afterwards to obtain the desired bitwidth. This may be very cheap
    /// depending on the difference between the actual and target bitwidths.
    /// For example, `move_truncate`ing a `128` bitwidth `ApInt` to `100` is
    /// relatively cheap and won't allocate memory since both `ApInt` instances can use
    /// the same amount of `Digit`s.
    /// 
    /// # Errors
    /// 
    /// - If the iterator yields no elements.
    pub(crate) fn from_iter<I>(digits: I) -> Result<ApInt>
        where I: IntoIterator<Item=Digit>,
    {
        let mut buffer = digits.into_iter().collect::<SmallVec<[Digit; 1]>>();
        match buffer.len() {
            0 => {
                Err(Error::expected_non_empty_digits())
            }
            1 => {
                let first_and_only = *buffer
                    .first()
                    .expect("We have already asserted that `digits.len()` must be at exactly `1`.");
                Ok(ApInt::new_inl(BitWidth::w64(), first_and_only))
            }
            n => {
                use std::mem;
                let bitwidth = BitWidth::new(n * Digit::BITS)
                    .expect("We have already asserted that the number of items the given Iterator \
                             iterates over is greater than `1` and thus non-zero and thus a valid `BitWidth`.");
                let req_digits = bitwidth.required_digits();
                buffer.shrink_to_fit();
                assert_eq!(buffer.capacity(), req_digits);
                assert_eq!(buffer.len()     , req_digits);
                let ptr_buffer = buffer.as_ptr() as *mut Digit;
                mem::forget(buffer);
                Ok(unsafe{ ApInt::new_ext(bitwidth, ptr_buffer) })
            }
        }
    }

    // TODO: convert this to take from a slice or IntoIterator<u64>
    #[cfg(test)]
    pub(crate) fn from_vec_u64(val: Vec<u64>) -> Option<ApInt> {
        if val.is_empty() {
            None
        } else {
            let buffer = val.into_iter()
                            .rev()
                            .map(Digit)
                            .collect::<Vec<Digit>>();
            Some(ApInt::from_iter(buffer).unwrap())
        }
    }

    /// Creates a new `ApInt` that represents the repetition of the given digit
    /// up to the given target bitwidth.
    /// 
    /// Note: The last digit in the generated sequence is truncated to make the `ApInt`'s
    ///       value representation fit the given bit-width.
    pub(crate) fn repeat_digit<D>(target_width: BitWidth, digit: D) -> ApInt
        where D: Into<Digit>
    {
        use std::iter;
        let digit = digit.into();
        let req_digits = target_width.required_digits();
        ApInt::from_iter(iter::repeat(digit).take(req_digits))
            .expect("Since `required_digits` always returns `1` or more \
                     required digits we can safely assume that this operation \
                     never fails.")
            .into_truncate(target_width)
            .expect("Since `BitWidth::required_digits` always returns the upper bound \
                     for the number of digits required to represent the given `BitWidth` \
                     and `ApInt::from_iter` will use exactly this upper bound \
                     we can safely assume that `target_width` is always equal or \
                     less than what `ApInt::from_iter` returns and thus truncation will \
                     never fail.")
    }

    /// Creates a new `ApInt` with the given bit width that represents zero.
    pub fn zero(width: BitWidth) -> ApInt {
        ApInt::repeat_digit(width, Digit::ZERO)
    }

    /// Creates a new `ApInt` with the given bit width that represents one.
    pub fn one(width: BitWidth) -> ApInt {
        ApInt::from_u64(1).into_zero_resize(width)
    }

    /// Creates a new `ApInt` with the given bit width that has all bits unset.
    /// 
    /// **Note:** This is equal to calling `ApInt::zero` with the given `width`.
    pub fn all_unset(width: BitWidth) -> ApInt {
        ApInt::zero(width)
    }

    /// Creates a new `ApInt` with the given bit width that has all bits set.
    pub fn all_set(width: BitWidth) -> ApInt {
        ApInt::repeat_digit(width, Digit::ONES)
    }

    /// Returns the smallest unsigned `ApInt` that can be represented by the given `BitWidth`.
    pub fn unsigned_min_value(width: BitWidth) -> ApInt {
        ApInt::zero(width)
    }

    /// Returns the largest unsigned `ApInt` that can be represented by the given `BitWidth`.
    pub fn unsigned_max_value(width: BitWidth) -> ApInt {
        ApInt::all_set(width)
    }

    /// Returns the smallest signed `ApInt` that can be represented by the given `BitWidth`.
    pub fn signed_min_value(width: BitWidth) -> ApInt {
        let mut result = ApInt::zero(width);
        result.set_sign_bit();
        result
    }

    /// Returns the largest signed `ApInt` that can be represented by the given `BitWidth`.
    pub fn signed_max_value(width: BitWidth) -> ApInt {
        let mut result = ApInt::all_set(width);
        result.unset_sign_bit();
        result
    }
}

impl From<bool> for ApInt {
    #[inline]
    fn from(bit: bool) -> ApInt {
        ApInt::from_bool(bit)
    }
}

impl From<u8> for ApInt {
    #[inline]
    fn from(val: u8) -> ApInt {
        ApInt::from_u8(val)
    }
}

impl From<i8> for ApInt {
    #[inline]
    fn from(val: i8) -> ApInt {
        ApInt::from_i8(val)
    }
}

impl From<u16> for ApInt {
    #[inline]
    fn from(val: u16) -> ApInt {
        ApInt::from_u16(val)
    }
}

impl From<i16> for ApInt {
    #[inline]
    fn from(val: i16) -> ApInt {
        ApInt::from_i16(val)
    }
}

impl From<u32> for ApInt {
    #[inline]
    fn from(val: u32) -> ApInt {
        ApInt::from_u32(val)
    }
}

impl From<i32> for ApInt {
    #[inline]
    fn from(val: i32) -> ApInt {
        ApInt::from_i32(val)
    }
}

impl From<u64> for ApInt {
    #[inline]
    fn from(val: u64) -> ApInt {
        ApInt::from_u64(val)
    }
}

impl From<i64> for ApInt {
    #[inline]
    fn from(val: i64) -> ApInt {
        ApInt::from_i64(val)
    }
}

impl From<u128> for ApInt {
    #[inline]
    fn from(val: u128) -> ApInt {
        ApInt::from_u128(val)
    }
}

impl From<i128> for ApInt {
    #[inline]
    fn from(val: i128) -> ApInt {
        ApInt::from_i128(val)
    }
}

macro_rules! impl_from_array_for_apint {
    ($n:expr) => {
        impl From<[i64; $n]> for ApInt {
            fn from(val: [i64; $n]) -> ApInt {
                <Self as From<[u64; $n]>>::from(
                    unsafe{ ::std::mem::transmute::<[i64; $n], [u64; $n]>(val) })
            }
        }

        impl From<[u64; $n]> for ApInt {
            fn from(val: [u64; $n]) -> ApInt {
                let buffer = val.into_iter()
                                .rev()
                                .cloned()
                                .map(Digit)
                                .collect::<Vec<Digit>>();
                assert_eq!(buffer.len(), $n);
                ApInt::from_iter(buffer)
                    .expect("We asserted that `buffer.len()` is exactly `$n` \
                                so we can expect `ApInt::from_iter` to be successful.")
            }
        }
    }
}

impl_from_array_for_apint!(2);  // 128 bits
impl_from_array_for_apint!(3);  // 192 bits
impl_from_array_for_apint!(4);  // 256 bits
impl_from_array_for_apint!(5);  // 320 bits
impl_from_array_for_apint!(6);  // 384 bits
impl_from_array_for_apint!(7);  // 448 bits
impl_from_array_for_apint!(8);  // 512 bits
impl_from_array_for_apint!(16); // 1024 bits
impl_from_array_for_apint!(32); // 2048 bits

// Note: There are some tests for this file that are located in `apint.rs`

#[cfg(test)]
mod tests {
    use super::*;

    use std::ops::Range;

    fn powers() -> impl Iterator<Item=u128> {
        (0..128).map(|p| 1 << p)
    }

    fn powers_from_to(range: Range<usize>) -> impl Iterator<Item=u128> {
        powers().skip(range.start).take(range.end - range.start)
    }

    #[test]
    fn test_powers() {
        let mut pows = powers();
        assert_eq!(pows.next(), Some(1 << 0));
        assert_eq!(pows.next(), Some(1 << 1));
        assert_eq!(pows.next(), Some(1 << 2));
        assert_eq!(pows.next(), Some(1 << 3));
        assert_eq!(pows.next(), Some(1 << 4));
        assert_eq!(pows.next(), Some(1 << 5));
        assert_eq!(pows.last(), Some(1 << 127));
    }

    #[test]
    fn test_powers_from_to() {
        {
            let mut powsft = powers_from_to(0..4);
            assert_eq!(powsft.next(), Some(1 << 0));
            assert_eq!(powsft.next(), Some(1 << 1));
            assert_eq!(powsft.next(), Some(1 << 2));
            assert_eq!(powsft.next(), Some(1 << 3));
            assert_eq!(powsft.next(), None);
        }
        {
            let mut powsft = powers_from_to(4..7);
            assert_eq!(powsft.next(), Some(1 << 4));
            assert_eq!(powsft.next(), Some(1 << 5));
            assert_eq!(powsft.next(), Some(1 << 6));
            assert_eq!(powsft.next(), None);
        }
    }

    fn test_values_u8() -> impl Iterator<Item=u8> {
        powers_from_to(0..8)
            .map(|v| v as u8)
            .chain([
                u8::max_value(),
                10,
                42,
                99,
                123
            ].into_iter()
             .map(|v| *v))
    }

    #[test]
    fn from_bool() {
        {
            let explicit = ApInt::from_bool(true);
            let implicit = ApInt::from(true);
            let expected = ApInt::new_inl(BitWidth::w1(), Digit::one());
            assert_eq!(explicit, implicit);
            assert_eq!(explicit, expected);
        }
        {
            let explicit = ApInt::from_bool(false);
            let implicit = ApInt::from(false);
            let expected = ApInt::new_inl(BitWidth::w1(), Digit::zero());
            assert_eq!(explicit, implicit);
            assert_eq!(explicit, expected);
        }
    }

    fn test_values_u16() -> impl Iterator<Item=u16> {
        test_values_u8()
            .map(u16::from)
            .chain(powers_from_to(8..16)
                .map(|v| v as u16))
            .chain([
                u16::max_value(),
                500,
                1000,
                1337,
                7777,
                42_000
            ].into_iter().map(|v| *v))
    }

    fn test_values_u32() -> impl Iterator<Item=u32> {
        test_values_u16()
            .map(u32::from)
            .chain(powers_from_to(16..32)
                .map(|v| v as u32))
            .chain([
                u32::max_value(),
                1_000_000,
                999_999_999,
                1_234_567_890
            ].into_iter().map(|v| *v))
    }

    fn test_values_u64() -> impl Iterator<Item=u64> {
        test_values_u32()
            .map(u64::from)
            .chain(powers_from_to(32..64)
                .map(|v| v as u64))
            .chain([
                u64::max_value(),
                1_000_000_000_000,
                999_999_999_999_999_999,
                0x0123_4567_89AB_CDEF
            ].into_iter().map(|v| *v))
    }

    fn test_values_u128() -> impl Iterator<Item=u128> {
        test_values_u64()
            .map(u128::from)
            .chain(powers_from_to(64..128)
                .map(|v| v as u128))
            .chain([
                u128::max_value(),
                1_000_000_000_000_000_000_000_000,
                999_999_999_999_999_999_999_999_999,
                0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210
            ].into_iter().map(|v| *v))
    }

    #[test]
    fn from_w128() {
        for val in test_values_u128() {
            let explicit_u128 = ApInt::from_u128(val);
            let explicit_i128 = ApInt::from_i128(val as i128);
            let implicit_u128 = ApInt::from(val);
            let implicit_i128 = ApInt::from(val as i128);
            let expected = ApInt::from_iter(
                vec![
                    Digit((val & u128::from(u64::max_value())) as DigitRepr),
                    Digit((val >> 64) as DigitRepr)
                ]).unwrap();
            assert_eq!(explicit_u128, explicit_i128);
            assert_eq!(explicit_u128, implicit_i128);
            assert_eq!(explicit_u128, implicit_u128);
            assert_eq!(explicit_u128, expected);
        }
    }

    #[test]
    fn zero() {
        assert_eq!(ApInt::zero(BitWidth::w1()), ApInt::from_bool(false));
        assert_eq!(ApInt::zero(BitWidth::w8()), ApInt::from_u8(0));
        assert_eq!(ApInt::zero(BitWidth::w16()), ApInt::from_u16(0));
        assert_eq!(ApInt::zero(BitWidth::w32()), ApInt::from_u32(0));
        assert_eq!(ApInt::zero(BitWidth::w64()), ApInt::from_u64(0));
        assert_eq!(ApInt::zero(BitWidth::w128()), ApInt::from_u128(0));
        assert_eq!(ApInt::zero(BitWidth::new(192).unwrap()), ApInt::from([0_u64; 3]));
        assert_eq!(ApInt::zero(BitWidth::new(256).unwrap()), ApInt::from([0_u64; 4]));
    }

    #[test]
    fn one() {
        assert_eq!(ApInt::one(BitWidth::w1()), ApInt::from_bool(true));
        assert_eq!(ApInt::one(BitWidth::w8()), ApInt::from_u8(1));
        assert_eq!(ApInt::one(BitWidth::w16()), ApInt::from_u16(1));
        assert_eq!(ApInt::one(BitWidth::w32()), ApInt::from_u32(1));
        assert_eq!(ApInt::one(BitWidth::w64()), ApInt::from_u64(1));
        assert_eq!(ApInt::one(BitWidth::w128()), ApInt::from_u128(1));
        assert_eq!(ApInt::one(BitWidth::new(192).unwrap()), ApInt::from([0_u64, 0, 1]));
        assert_eq!(ApInt::one(BitWidth::new(256).unwrap()), ApInt::from([0_u64, 0, 0, 1]));
    }

    #[test]
    fn all_unset_eq_zero() {
        let test_widths =
            [
                1_usize, 2, 4, 8, 10, 16, 32, 50, 64,
                100, 128, 150, 200, 250, 255, 256
            ]
            .into_iter()
            .map(|&w| BitWidth::new(w).unwrap());
        for width in test_widths {
            assert_eq!(ApInt::zero(width), ApInt::all_unset(width));
        }
    }

    #[test]
    fn same_signed_unsigned() {
        assert_eq!(ApInt::from_i8(-1), ApInt::from_u8(0xFF));
        assert_eq!(ApInt::from_i16(-1), ApInt::from_u16(0xFFFF));
        assert_eq!(ApInt::from_i32(-1), ApInt::from_u32(0xFFFF_FFFF));
        assert_eq!(ApInt::from_i64(-1), ApInt::from_u64(0xFFFF_FFFF_FFFF_FFFF));
        assert_eq!(ApInt::from_i128(-1), ApInt::from_u128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF));
    }

    #[test]
    fn all_set() {
        assert_eq!(ApInt::all_set(BitWidth::w1()), ApInt::from_bool(true));
        assert_eq!(ApInt::all_set(BitWidth::w8()), ApInt::from_i8(-1));
        assert_eq!(ApInt::all_set(BitWidth::w16()), ApInt::from_i16(-1));
        assert_eq!(ApInt::all_set(BitWidth::w32()), ApInt::from_i32(-1));
        assert_eq!(ApInt::all_set(BitWidth::w64()), ApInt::from_i64(-1));
        assert_eq!(ApInt::all_set(BitWidth::w128()), ApInt::from_i128(-1));
        assert_eq!(
            ApInt::all_set(BitWidth::new(192).unwrap()),
            ApInt::from([-1_i64 as u64, -1_i64 as u64, -1_i64 as u64])
        );
        assert_eq!(
            ApInt::all_set(BitWidth::new(256).unwrap()),
            ApInt::from([-1_i64 as u64, -1_i64 as u64, -1_i64 as u64, -1_i64 as u64])
        );
    }

    #[test]
    fn unsiged_min_value_eq_zero() {
        let test_widths =
            [
                1_usize, 2, 4, 8, 10, 16, 32, 50, 64,
                100, 128, 150, 200, 250, 255, 256
            ]
            .into_iter()
            .map(|&w| BitWidth::new(w).unwrap());
        for width in test_widths {
            assert_eq!(ApInt::zero(width), ApInt::unsigned_min_value(width));
        }
    }

    #[test]
    fn unsiged_max_value_eq_all_set() {
        let test_widths =
            [
                1_usize, 2, 4, 8, 10, 16, 32, 50, 64,
                100, 128, 150, 200, 250, 255, 256
            ]
            .into_iter()
            .map(|&w| BitWidth::new(w).unwrap());
        for width in test_widths {
            assert_eq!(ApInt::all_set(width), ApInt::unsigned_max_value(width));
        }
    }

    #[test]
    fn signed_min_value() {
        assert_eq!(ApInt::signed_min_value(BitWidth::w1()), ApInt::from_bool(true));
        assert_eq!(ApInt::signed_min_value(BitWidth::w8()), ApInt::from_i8(i8::min_value()));
        assert_eq!(ApInt::signed_min_value(BitWidth::w16()), ApInt::from_i16(i16::min_value()));
        assert_eq!(ApInt::signed_min_value(BitWidth::w32()), ApInt::from_i32(i32::min_value()));
        assert_eq!(ApInt::signed_min_value(BitWidth::w64()), ApInt::from_i64(i64::min_value()));
        assert_eq!(ApInt::signed_min_value(BitWidth::w128()), ApInt::from_i128(i128::min_value()));

        {
            let w10 = BitWidth::new(10).unwrap();
            assert_eq!(
                ApInt::signed_min_value(w10), ApInt::new_inl(w10, Digit(0x0000_0000_0000_0200))
            )
        }
        {
            use std::i128;
            assert_eq!(
                ApInt::signed_min_value(BitWidth::w128()), ApInt::from(i128::MIN)
            );
            assert_eq!(
                ApInt::signed_min_value(BitWidth::w128()), ApInt::from([0x8000_0000_0000_0000_u64, 0_u64])
            );
            let w256 = BitWidth::new(256).unwrap();
            assert_eq!(
                ApInt::signed_min_value(w256), ApInt::from([0x8000_0000_0000_0000_u64, 0_u64, 0_u64, 0_u64])
            )
        }
    }

    #[test]
    fn signed_max_value() {
        assert_eq!(ApInt::signed_max_value(BitWidth::w1()), ApInt::from_bool(false));
        assert_eq!(ApInt::signed_max_value(BitWidth::w8()), ApInt::from_i8(i8::max_value()));
        assert_eq!(ApInt::signed_max_value(BitWidth::w16()), ApInt::from_i16(i16::max_value()));
        assert_eq!(ApInt::signed_max_value(BitWidth::w32()), ApInt::from_i32(i32::max_value()));
        assert_eq!(ApInt::signed_max_value(BitWidth::w64()), ApInt::from_i64(i64::max_value()));
        assert_eq!(ApInt::signed_max_value(BitWidth::w128()), ApInt::from_i128(i128::max_value()));

        {
            let w10 = BitWidth::new(10).unwrap();
            assert_eq!(
                ApInt::signed_max_value(w10), ApInt::new_inl(w10, Digit(0x0000_0000_0000_01FF))
            )
        }
    }
}