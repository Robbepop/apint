use crate::data::{Storage, Digit};
use crate::info::{BitWidth, Width, Result, Error};

use std::ptr::NonNull;

/// An arbitrary precision integer with modulo arithmetics similar to machine integers.
/// 
/// Note: The width of the `ApInt` can be found at runtime through importing the [`Width`](trait.Width.html) trait.
pub struct ApInt {
    /// The width in bits of this `ApInt`.
    pub(crate) len : BitWidth,
    /// The actual data (bits) of this `ApInt`.
    pub(in crate::data) data: ApIntData
}

pub(in crate::data) union ApIntData {
    /// Inline storage (up to 64 bits) for small-space optimization.
    pub(in crate::data) inl: Digit,
    /// Extern storage (>64 bits) for larger `ApInt`s.
    pub(in crate::data) ext: NonNull<Digit>
}

/// `ApInt` is safe to send between threads since it does not own
/// aliasing memory and has no reference counting mechanism like `Rc`.
unsafe impl Send for ApInt {}

/// `ApInt` is safe to share between threads since it does not own
/// aliasing memory and has no mutable internal state like `Cell` or `RefCell`.
unsafe impl Sync for ApInt {}

impl ApInt {
    /// Deallocates memory that may be allocated by this `ApInt`.
    /// 
    /// `ApInt` instances with a bit width larger than `64` bits
    /// allocate their digits on the heap. With `drop_digits` this
    /// memory can be freed.
    /// 
    /// **Note:** This is extremely unsafe, only use this if the
    ///           `ApInt` no longer needs its digits.
    /// 
    /// **Note:** This is `unsafe` since it violates invariants
    ///           of the `ApInt`.
    pub(crate) unsafe fn drop_digits(&mut self) {
        if self.len.storage() == Storage::Ext {
            let len = self.len_digits();
            // TODO: Is there a more direct way to do this?
            drop(Vec::from_raw_parts(
                self.data.ext.as_ptr(), len, len))
        }
    }

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

    /// Returns the number of bits of the bit width of this `ApInt`.
    #[inline]
    pub(crate) fn len_bits(&self) -> usize {
        self.len.to_usize()
    }

    /// Returns the number of digits used internally for the value
    /// representation of this `ApInt`.
    #[inline]
    pub(crate) fn len_digits(&self) -> usize {
        self.len.required_digits()
    }

    /// Returns the storage specifier of this `ApInt`.
    /// 
    /// This is `Storage::Inl` for `ApInt` instances that can be stored
    /// entirely on the stack and `Storage::Ext` otherwise.
    #[inline]
    pub(crate) fn storage(&self) -> Storage {
        self.len.storage()
    }

    /// Returns a slice over the `Digit`s of this `ApInt` in little-endian order.
    #[inline]    
    pub(crate) fn as_digit_slice(&self) -> &[Digit] {
        use std::slice;
        match self.len.storage() {
            Storage::Inl => unsafe {
                slice::from_raw_parts(&self.data.inl, 1)
            },
            Storage::Ext => unsafe {
                slice::from_raw_parts(self.data.ext.as_ptr(), self.len_digits())
            }
        }
    }

    /// Returns a mutable slice over the `Digit`s of this `ApInt` in little-endian order.
    #[inline]    
    pub(crate) fn as_digit_slice_mut(&mut self) -> &mut [Digit] {
        use std::slice;
        match self.len.storage() {
            Storage::Inl => unsafe {
                slice::from_raw_parts_mut(&mut self.data.inl, 1)
            },
            Storage::Ext => unsafe {
                slice::from_raw_parts_mut(self.data.ext.as_ptr(), self.len_digits())
            }
        }
    }

    /// Assigns `rhs` to this `ApInt`.
    ///
    /// This mutates digits and may affect the bitwidth of `self`
    /// which **may cause allocations**.
    ///
    /// After this operation `rhs` and `self` are equal to each other.
    pub fn assign(&mut self, rhs: &ApInt) {
        if self.len_digits() == rhs.len_digits() {
            // If `self` and `rhs` require the same amount of digits
            // for their representation we can simply utilize `ApInt`
            // invariants and basically `memcpy` from `rhs` to `self`.
            // Afterwards a simple adjustment of the length is sufficient.
            // (At the end of this method.)
            self.as_digit_slice_mut()
                .copy_from_slice(rhs.as_digit_slice());
        }
        else {
            // In this case `rhs` and `self` require an unequal amount
            // of digits for their representation which means that the
            // digits that may be allocated by `self` must be dropped.
            //
            // Note that `ApInt::drop_digits` only deallocates if possible.
            unsafe{ self.drop_digits(); }

            match rhs.storage() {
                Storage::Inl => {
                    // If `rhs` is a small `ApInt` we can simply update
                    // the `digit` field of `self` and we are done.
                    self.data.inl = unsafe{ rhs.data.inl };
                }
                Storage::Ext => {
                    // If `rhs` is a large heap-allocated `ApInt` we first
                    // need to expensively clone its buffer and feed it to `self`.
                    let cloned = rhs.clone();
                    self.data.ext = unsafe{ cloned.data.ext };
                    use std::mem;
                    mem::forget(cloned);
                }
            }
        }
        // Since all cases may need bit width adjustment we outsourced it
        // to the end of this method.
        self.len = rhs.len;
    }

    /// Strictly assigns `rhs` to this `ApInt`.
    /// 
    /// After this operation `rhs` and `self` are equal to each other.
    /// 
    /// **Note:** Strict assigns protect against mutating the bit width
    /// of `self` and thus return an error instead of executing a probably
    /// expensive `assign` operation.
    /// 
    /// # Errors
    /// 
    /// - If `rhs` and `self` have unmatching bit widths.
    pub fn strict_assign(&mut self, rhs: &ApInt) -> Result<()> {
        if self.width() != rhs.width() {
            return Error::unmatching_bitwidths(self.width(), rhs.width())
                .with_annotation(format!(
                    "Occured while trying to `strict_assign` {:?} to {:?}.", self, rhs))
                .into()
        }
        self.as_digit_slice_mut()
            .copy_from_slice(rhs.as_digit_slice());
        Ok(())
    }
}

impl Drop for ApInt {
    fn drop(&mut self) {
        unsafe{self.drop_digits()}
    }
}

impl Clone for ApInt {
    fn clone(&self) -> Self {
        match self.storage() {
            Storage::Inl => {
                ApInt::new_inl(self.len, unsafe{ self.data.inl })
            }
            Storage::Ext => {
                use std::mem;
                let req_digits = self.len_digits();
                //TODO: this can be simplified and should be benchmarked
                let mut buffer = self.as_digit_slice()
                    .to_vec()
                    .into_boxed_slice();
                assert_eq!(buffer.len(), req_digits);
                let ptr_buffer = buffer.as_mut_ptr();
                mem::forget(buffer);
                unsafe{ ApInt::new_ext(self.len, ptr_buffer) }
            }
        }
    }
}

impl Width for ApInt {
    /// Returns the `BitWidth` of this `ApInt`.
    #[inline]
    fn width(&self) -> BitWidth {
        BitWidth::new(self.len_bits()).unwrap()
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