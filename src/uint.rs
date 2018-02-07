use apint::ApInt;
use traits::Width;
use digit::Bit;
use bitwidth::BitWidth;
use errors::Result;

use std::cmp::Ordering;

/// This one still needs documentation ...
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UInt {
    value: ApInt,
}

impl PartialOrd for UInt {
    fn partial_cmp(&self, rhs: &UInt) -> Option<Ordering> {
        if self.value.width() != rhs.value.width() {
            return None;
        }
        if self.value.checked_ult(&rhs.value).unwrap() {
            return Some(Ordering::Less);
        }
        if self.value == rhs.value {
            return Some(Ordering::Equal);
        }
        Some(Ordering::Greater)
    }

    fn lt(&self, rhs: &UInt) -> bool {
        self.value.checked_ult(&rhs.value).unwrap_or(false)
    }

    fn le(&self, rhs: &UInt) -> bool {
        self.value.checked_ule(&rhs.value).unwrap_or(false)
    }

    fn gt(&self, rhs: &UInt) -> bool {
        self.value.checked_ugt(&rhs.value).unwrap_or(false)
    }

    fn ge(&self, rhs: &UInt) -> bool {
        self.value.checked_uge(&rhs.value).unwrap_or(false)
    }
}

impl From<ApInt> for UInt {
    fn from(value: ApInt) -> UInt {
        UInt { value }
    }
}

/// # Constructors
impl UInt {
    /// Creates a new `UInt` from the given `Bit` value with a bit width of `1`.
    ///
    /// This function is generic over types that are convertible to `Bit` such as `bool`.
    pub fn from_bit<B>(bit: B) -> UInt
    where
        B: Into<Bit>,
    {
        UInt::from(ApInt::from_bit(bit))
    }

    /// Creates a new `UInt` from a given `u8` value with a bit-width of 8.
    #[inline]
    pub fn from_u8(val: u8) -> UInt {
        UInt::from(ApInt::from_u8(val))
    }

    /// Creates a new `UInt` from a given `u16` value with a bit-width of 16.
    #[inline]
    pub fn from_u16(val: u16) -> UInt {
        UInt::from(ApInt::from_u16(val))
    }

    /// Creates a new `UInt` from a given `u32` value with a bit-width of 32.
    #[inline]
    pub fn from_u32(val: u32) -> UInt {
        UInt::from(ApInt::from_u32(val))
    }

    /// Creates a new `UInt` from a given `u64` value with a bit-width of 64.
    #[inline]
    pub fn from_u64(val: u64) -> UInt {
        UInt::from(ApInt::from_u64(val))
    }

    /// Creates a new `UInt` from a given `u64` value with a bit-width of 64.
    pub fn from_u128(val: u128) -> UInt {
        UInt::from(ApInt::from_u128(val))
    }

    /// Creates a new `UInt` with the given bit width that represents zero.
    pub fn zero(width: BitWidth) -> UInt {
        UInt::from(ApInt::zero(width))
    }

    /// Creates a new `UInt` with the given bit width that represents one.
    pub fn one(width: BitWidth) -> UInt {
        UInt::from(ApInt::one(width))
    }

    /// Creates a new `UInt` with the given bit width that has all bits unset.
    ///
    /// **Note:** This is equal to calling `UInt::zero` with the given `width`.
    pub fn all_unset(width: BitWidth) -> UInt {
        UInt::zero(width)
    }

    /// Creates a new `UInt` with the given bit width that has all bits set.
    ///
    /// # Note
    ///
    /// - This is equal to minus one on any twos-complement machine.
    pub fn all_set(width: BitWidth) -> UInt {
        UInt::from(ApInt::all_set(width))
    }

    /// Returns the smallest `UInt` that can be represented by the given `BitWidth`.
    pub fn min_value(width: BitWidth) -> UInt {
        UInt::from(ApInt::unsigned_min_value(width))
    }

    /// Returns the largest unsigned `UInt` that can be represented by the given `BitWidth`.
    pub fn max_value(width: BitWidth) -> UInt {
        UInt::from(ApInt::unsigned_max_value(width))
    }
}

impl From<u8> for UInt {
    fn from(val: u8) -> UInt {
        UInt::from_u8(val)
    }
}

impl From<u16> for UInt {
    fn from(val: u16) -> UInt {
        UInt::from_u16(val)
    }
}

impl From<u32> for UInt {
    fn from(val: u32) -> UInt {
        UInt::from_u32(val)
    }
}

impl From<u64> for UInt {
    fn from(val: u64) -> UInt {
        UInt::from_u64(val)
    }
}

impl From<u128> for UInt {
    fn from(val: u128) -> UInt {
        UInt::from_u128(val)
    }
}

macro_rules! impl_from_array_for_uint {
	($n:expr) => {
		impl From<[u64; $n]> for UInt {
			fn from(val: [u64; $n]) -> UInt {
				UInt::from(ApInt::from(val))
			}
		}
	}
}

impl_from_array_for_uint!(2); // 128 bits
impl_from_array_for_uint!(3); // 192 bits
impl_from_array_for_uint!(4); // 256 bits
impl_from_array_for_uint!(5); // 320 bits
impl_from_array_for_uint!(6); // 384 bits
impl_from_array_for_uint!(7); // 448 bits
impl_from_array_for_uint!(8); // 512 bits
impl_from_array_for_uint!(16); // 1024 bits
impl_from_array_for_uint!(32); // 2048 bits

/// # Utilities
impl UInt {
    /// Returns `true` if this `UInt` represents the value zero (`0`).
    ///
    /// # Note
    ///
    /// - Zero (`0`) is also called the additive neutral element.
    /// - This operation is more efficient than comparing two instances
    ///   of `UInt` for the same reason.
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    /// Returns `true` if this `UInt` represents the value one (`1`).
    ///
    /// # Note
    ///
    /// - One (`1`) is also called the multiplicative neutral element.
    /// - This operation is more efficient than comparing two instances
    ///   of `UInt` for the same reason.
    pub fn is_one(&self) -> bool {
        self.value.is_one()
    }

    /// Returns `true` if this `UInt` represents an even number.
    pub fn is_even(&self) -> bool {
        self.value.is_even()
    }

    /// Returns `true` if this `UInt` represents an odd number.
    pub fn is_odd(&self) -> bool {
        self.value.is_odd()
    }
}

/// # To Primitive (Resize)
impl UInt {
    /// Resizes this `UInt` to a `bool` primitive type.
    ///
    /// Bits in this `UInt` that are not within the bounds
    /// of the `bool` are being ignored.
    ///
    /// # Note
    ///
    /// - Basically this returns `true` if the least significant
    ///   bit of this `UInt` is `1` and `false` otherwise.
    pub fn resize_to_bool(&self) -> bool {
        self.value.resize_to_bool()
    }

    /// Resizes this `UInt` to a `u8` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `8` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u8(&self) -> u8 {
        self.value.resize_to_u8()
    }

    /// Resizes this `UInt` to a `u16` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `16` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u16(&self) -> u16 {
        self.value.resize_to_u16()
    }

    /// Resizes this `UInt` to a `u32` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `32` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u32(&self) -> u32 {
        self.value.resize_to_u32()
    }

    /// Resizes this `UInt` to a `u64` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `64` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u64(&self) -> u64 {
        self.value.resize_to_u64()
    }

    /// Resizes this `UInt` to a `u128` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `128` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u128(&self) -> u128 {
        self.value.resize_to_u128()
    }
}

/// # To Primitive (Try-Cast)
impl UInt {
    /// Tries to represent the value of this `UInt` as a `bool`.
    ///
    /// # Note
    ///
    /// This returns `true` if the value represented by this `UInt`
    /// is `1`, returns `false` if the value represented by this
    /// `UInt` is `0` and returns an error otherwise.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `bool`.
    pub fn try_to_bool(&self) -> Result<bool> {
        self.value.try_to_bool()
    }

    /// Tries to represent the value of this `UInt` as a `u8`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `UInt` does not exceed the maximum value of `u8`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `u8`.
    pub fn try_to_u8(&self) -> Result<u8> {
        self.value.try_to_u8()
    }

    /// Tries to represent the value of this `UInt` as a `u16`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `UInt` does not exceed the maximum value of `u16`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `u16`.
    pub fn try_to_u16(&self) -> Result<u16> {
        self.value.try_to_u16()
    }

    /// Tries to represent the value of this `UInt` as a `u32`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `UInt` does not exceed the maximum value of `u32`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `u32`.
    pub fn try_to_u32(&self) -> Result<u32> {
        self.value.try_to_u32()
    }

    /// Tries to represent the value of this `UInt` as a `u64`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `UInt` does not exceed the maximum value of `u64`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `u64`.
    pub fn try_to_u64(&self) -> Result<u64> {
        self.value.try_to_u64()
    }

    /// Tries to represent the value of this `UInt` as a `u128`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `UInt` does not exceed the maximum value of `u128`.
    ///
    /// # Complexity
    ///
    /// - 𝒪(n) where n is the number of digits of this `UInt`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be
    ///   represented by a `u128`.
    pub fn try_to_u128(&self) -> Result<u128> {
        self.value.try_to_u128()
    }
}
