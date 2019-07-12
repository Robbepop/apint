use crate::data::{Storage, Digit};
use crate::info::{BitWidth, Width, Result, Error};

use std::ptr::NonNull;

    /// Creates a new small `ApInt` from the given `BitWidth` and `Digit`.
    /// 
    /// Small `ApInt` instances are stored entirely on the stack.
    /// 
    /// # Panics
    /// 
    /// - If the given `width` represents a `BitWidth` larger than `64` bits.
    #[inline]
    pub(crate) fn new_inl(width: BitWidth, digit: Digit) -> ApInt {
        assert_eq!(width.storage(), Storage::Inl);
        ApInt {
            len: width,
            data: ApIntData { inl: digit }
        }
    }

    /// Creates a new large `ApInt` from the given `BitWidth` and `Digit`.
    /// 
    /// Large `ApInt` instances allocate their digits on the heap.
    /// 
    /// **Note:** This operation is unsafe since the buffer length behind the
    ///           given `ext_ptr` must be trusted.
    /// 
    /// # Panics
    /// 
    /// - If the given `width` represents a `BitWidth` smaller than
    ///   or equal to `64` bits.
    pub(crate) unsafe fn new_ext(width: BitWidth, ext_ptr: *mut Digit) -> ApInt {
        assert_eq!(width.storage(), Storage::Ext);
        ApInt{
            len: width,
            data: ApIntData{ ext: NonNull::new_unchecked(ext_ptr) }
        }
    }

// These are tests that would normally be in `constructors.rs`.
// This is put here to be able to constrict the visibility modifiers for
// `ApIntData`.
#[cfg(test)]
mod raw_construction {
    use super::*;

    use std::ops::Range;

    fn powers() -> impl Iterator<Item=u128> {
        (0..128).map(|p| 1 << p)
    }

    fn powers_from_to(range: Range<usize>) -> impl Iterator<Item=u128> {
        powers().skip(range.start).take(range.end - range.start)
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

    #[test]
    fn from_w8() {
        for val in test_values_u8() {
            let explicit_u8 = ApInt::from_u8(val);
            let explicit_i8 = ApInt::from_i8(val as i8);
            let implicit_u8 = ApInt::from(val);
            let implicit_i8 = ApInt::from(val as i8);
            let expected = ApInt{
                len : BitWidth::w8(),
                data: ApIntData{inl: Digit(u64::from(val))}
            };
            assert_eq!(explicit_u8, explicit_i8);
            assert_eq!(explicit_u8, implicit_i8);
            assert_eq!(explicit_u8, implicit_u8);
            assert_eq!(explicit_u8, expected);
        }
    }

    #[test]
    fn from_w16() {
        for val in test_values_u16() {
            let explicit_u16 = ApInt::from_u16(val);
            let explicit_i16 = ApInt::from_i16(val as i16);
            let implicit_u16 = ApInt::from(val);
            let implicit_i16 = ApInt::from(val as i16);
            let expected = ApInt{
                len : BitWidth::w16(),
                data: ApIntData{inl: Digit(u64::from(val))}
            };
            assert_eq!(explicit_u16, explicit_i16);
            assert_eq!(explicit_u16, implicit_i16);
            assert_eq!(explicit_u16, implicit_u16);
            assert_eq!(explicit_u16, expected);
        }
    }

    #[test]
    fn from_w32() {
        for val in test_values_u32() {
            let explicit_u32 = ApInt::from_u32(val);
            let explicit_i32 = ApInt::from_i32(val as i32);
            let implicit_u32 = ApInt::from(val);
            let implicit_i32 = ApInt::from(val as i32);
            let expected = ApInt{
                len : BitWidth::w32(),
                data: ApIntData{inl: Digit(u64::from(val))}
            };
            assert_eq!(explicit_u32, explicit_i32);
            assert_eq!(explicit_u32, implicit_i32);
            assert_eq!(explicit_u32, implicit_u32);
            assert_eq!(explicit_u32, expected);
        }
    }

    #[test]
    fn from_w64() {
        for val in test_values_u64() {
            let explicit_u64 = ApInt::from_u64(val);
            let explicit_i64 = ApInt::from_i64(val as i64);
            let implicit_u64 = ApInt::from(val);
            let implicit_i64 = ApInt::from(val as i64);
            let expected = ApInt{
                len : BitWidth::w64(),
                data: ApIntData{inl: Digit(u64::from(val))}
            };
            assert_eq!(explicit_u64, explicit_i64);
            assert_eq!(explicit_u64, implicit_i64);
            assert_eq!(explicit_u64, implicit_u64);
            assert_eq!(explicit_u64, expected);
        }
    }
}