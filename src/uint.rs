//! All UInt methods are defined here, except for `std::ops` traits in
//! `std_ops.rs`

use crate::{
    utils::{forward_bin_mut_impl, forward_mut_impl, try_forward_bin_mut_impl},
    ApInt,
    BitPos,
    BitWidth,
    Int,
    Result,
    ShiftAmount,
    Width,
};

use core::cmp::Ordering;

/// Unsigned machine integer with arbitrary bitwidths and modulo arithmetics.
///
/// Thin convenience wrapper around `ApInt` for static unsigned interpretation
/// of the value.
///
/// This very cheaply transformes to and from `ApInt` and `Int` instances and
/// together with `Int` offers a more elegant and higher-level abstraction
/// interface to the lower-level `ApInt`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(serde_support, Serialize)]
#[cfg_attr(serde_support, Deserialize)]
pub struct UInt {
    value: ApInt,
}

impl From<ApInt> for UInt {
    fn from(value: ApInt) -> UInt {
        UInt { value }
    }
}

impl Width for UInt {
    fn width(&self) -> BitWidth {
        self.value.width()
    }
}

impl UInt {
    /// Transforms this `UInt` into an equivalent `ApInt` instance.
    pub fn into_apint(self) -> ApInt {
        self.value
    }

    /// Transforms this `UInt` into an equivalent `Int` instance.
    pub fn into_signed(self) -> Int {
        Int::from(self.value)
    }
}

/// # Constructors
impl UInt {
    /// Creates a new `UInt` from the given `bool` value with a bit-width of
    /// `1`.
    pub fn from_bool(bit: bool) -> UInt {
        UInt::from(ApInt::from_bool(bit))
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

    /// Returns the smallest `UInt` that can be represented by the given
    /// `BitWidth`.
    pub fn min_value(width: BitWidth) -> UInt {
        UInt::from(ApInt::unsigned_min_value(width))
    }

    /// Returns the largest `UInt` that can be represented by the given
    /// `BitWidth`.
    pub fn max_value(width: BitWidth) -> UInt {
        UInt::from(ApInt::unsigned_max_value(width))
    }
}

impl From<bool> for UInt {
    #[inline]
    fn from(bit: bool) -> UInt {
        UInt::from_bool(bit)
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
    };
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
    /// - This operation is more efficient than comparing two instances of
    ///   `UInt`
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    /// Returns `true` if this `Int` represents the value one (`1`).
    ///
    /// # Note
    ///
    /// - One (`1`) is also called the multiplicative neutral element.
    /// - This operation is more efficient than comparing two instances of `Int`
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

impl UInt {
    /// Less-than (`lt`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self < rhs`.
    /// - Interprets both `UInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn checked_lt(&self, rhs: &UInt) -> Result<bool> {
        self.value.checked_ult(&rhs.value)
    }

    /// Less-equals (`le`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self <= rhs`.
    /// - Interprets both `UInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_le(&self, rhs: &UInt) -> Result<bool> {
        self.value.checked_ule(&rhs.value)
    }

    /// Greater-than (`gt`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self > rhs`.
    /// - Interprets both `UInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_gt(&self, rhs: &UInt) -> Result<bool> {
        self.value.checked_ugt(&rhs.value)
    }

    /// Greater-equals (`ge`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self >= rhs`.
    /// - Interprets both `UInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_ge(&self, rhs: &UInt) -> Result<bool> {
        self.value.checked_uge(&rhs.value)
    }
}

/// If `self` and `rhs` have unmatching bit widths, `None` will be returned for
/// `partial_cmp` and `false` will be returned for the rest of the `PartialOrd`
/// methods.
impl PartialOrd for UInt {
    fn partial_cmp(&self, rhs: &UInt) -> Option<Ordering> {
        if self.width() != rhs.width() {
            return None
        }
        if self.checked_lt(rhs).unwrap() {
            return Some(Ordering::Less)
        }
        if self.value == rhs.value {
            return Some(Ordering::Equal)
        }
        Some(Ordering::Greater)
    }

    fn lt(&self, rhs: &UInt) -> bool {
        self.checked_lt(rhs).unwrap_or(false)
    }

    fn le(&self, rhs: &UInt) -> bool {
        self.checked_le(rhs).unwrap_or(false)
    }

    fn gt(&self, rhs: &UInt) -> bool {
        self.checked_gt(rhs).unwrap_or(false)
    }

    fn ge(&self, rhs: &UInt) -> bool {
        self.checked_ge(rhs).unwrap_or(false)
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
    /// - Basically this returns `true` if the least significant bit of this
    ///   `UInt` is `1` and `false` otherwise.
    pub fn resize_to_bool(&self) -> bool {
        self.value.resize_to_bool()
    }

    /// Resizes this `UInt` to a `u8` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `8` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u8(&self) -> u8 {
        self.value.resize_to_u8()
    }

    /// Resizes this `UInt` to a `u16` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `16` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u16(&self) -> u16 {
        self.value.resize_to_u16()
    }

    /// Resizes this `UInt` to a `u32` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `32` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u32(&self) -> u32 {
        self.value.resize_to_u32()
    }

    /// Resizes this `UInt` to a `u64` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `64` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u64(&self) -> u64 {
        self.value.resize_to_u64()
    }

    /// Resizes this `UInt` to a `u128` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `128` bits are being ignored by
    ///   this operation to construct the result.
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
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `bool`.
    pub fn try_to_bool(&self) -> Result<bool> {
        self.value.try_to_bool()
    }

    /// Tries to represent the value of this `UInt` as a `u8`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `UInt` does not exceed the maximum value of `u8`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `u8`.
    pub fn try_to_u8(&self) -> Result<u8> {
        self.value.try_to_u8()
    }

    /// Tries to represent the value of this `UInt` as a `u16`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `UInt` does not exceed the maximum value of `u16`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `u16`.
    pub fn try_to_u16(&self) -> Result<u16> {
        self.value.try_to_u16()
    }

    /// Tries to represent the value of this `UInt` as a `u32`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `UInt` does not exceed the maximum value of `u32`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `u32`.
    pub fn try_to_u32(&self) -> Result<u32> {
        self.value.try_to_u32()
    }

    /// Tries to represent the value of this `UInt` as a `u64`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `UInt` does not exceed the maximum value of `u64`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `u64`.
    pub fn try_to_u64(&self) -> Result<u64> {
        self.value.try_to_u64()
    }

    /// Tries to represent the value of this `UInt` as a `u128`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `UInt` does not exceed the maximum value of `u128`.
    ///
    /// # Complexity
    ///
    /// - 𝒪(n) where n is the number of digits of this `UInt`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `UInt` can not be represented by a
    ///   `u128`.
    pub fn try_to_u128(&self) -> Result<u128> {
        self.value.try_to_u128()
    }
}

/// # Shifts
impl UInt {
    /// Shift this `UInt` left by the given `shift_amount` bits.
    ///
    /// This operation is inplace and will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If the given `shift_amount` is invalid for the bit width of this
    ///   `UInt`.
    pub fn wrapping_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
    where
        S: Into<ShiftAmount>,
    {
        self.value.wrapping_shl_assign(shift_amount)
    }

    /// Shift this `UInt` left by the given `shift_amount` bits and returns the
    /// result.
    ///
    /// This operation is inplace and will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If the given `shift_amount` is invalid for the bit width of this
    ///   `UInt`.
    pub fn into_wrapping_shl<S>(self, shift_amount: S) -> Result<UInt>
    where
        S: Into<ShiftAmount>,
    {
        self.value.into_wrapping_shl(shift_amount).map(UInt::from)
    }

    /// Right-shifts this `UInt` by the given `shift_amount` bits.
    ///
    /// This operation is inplace and will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If the given `shift_amount` is invalid for the bit width of this
    ///   `UInt`.
    pub fn wrapping_shr_assign<S>(&mut self, shift_amount: S) -> Result<()>
    where
        S: Into<ShiftAmount>,
    {
        self.value.wrapping_lshr_assign(shift_amount)
    }

    /// Right-shifts this `UInt` by the given `shift_amount` bits
    /// and returns the result.
    ///
    /// This operation is inplace and will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If the given `shift_amount` is invalid for the bit width of this
    ///   `UInt`.
    pub fn into_wrapping_shr<S>(self, shift_amount: S) -> Result<UInt>
    where
        S: Into<ShiftAmount>,
    {
        self.value.into_wrapping_lshr(shift_amount).map(UInt::from)
    }
}

/// # Random Utilities using `rand` crate.
#[cfg(feature = "rand_support")]
impl UInt {
    /// Creates a new `UInt` with the given `BitWidth` and random `Digit`s.
    pub fn random_with_width(width: BitWidth) -> UInt {
        UInt::from(ApInt::random_with_width(width))
    }

    /// Creates a new `UInt` with the given `BitWidth` and random `Digit`s
    /// using the given random number generator.
    ///
    /// **Note:** This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R>(width: BitWidth, rng: &mut R) -> UInt
    where
        R: rand::Rng,
    {
        UInt::from(ApInt::random_with_width_using(width, rng))
    }

    /// Randomizes the digits of this `UInt` inplace.
    ///
    /// This won't change its `BitWidth`.
    pub fn randomize(&mut self) {
        self.value.randomize()
    }

    /// Randomizes the digits of this `UInt` inplace using the given
    /// random number generator.
    ///
    /// This won't change its `BitWidth`.
    pub fn randomize_using<R>(&mut self, rng: &mut R)
    where
        R: rand::Rng,
    {
        self.value.randomize_using(rng)
    }
}

impl UInt {
    /// Assigns `rhs` to this `UInt`.
    ///
    /// This mutates digits and may affect the bitwidth of `self`
    /// which **might result in an expensive operations**.
    ///
    /// After this operation `rhs` and `self` are equal to each other.
    pub fn assign(&mut self, rhs: &UInt) {
        self.value.assign(&rhs.value)
    }

    /// Strictly assigns `rhs` to this `UInt`.
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
    pub fn strict_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.strict_assign(&rhs.value)
    }
}

/// # Casting: Truncation & Extension
impl UInt {
    /// Tries to truncate this `UInt` inplace to the given `target_width`
    /// and returns the result.
    ///
    /// # Note
    ///
    /// - This is useful for method chaining.
    /// - For more details look into
    ///   [`truncate`](struct.UInt.html#method.truncate).
    ///
    /// # Errors
    ///
    /// - If the `target_width` is greater than the current width.
    pub fn into_truncate<W>(self, target_width: W) -> Result<UInt>
    where
        W: Into<BitWidth>,
    {
        try_forward_bin_mut_impl(self, target_width, UInt::truncate)
    }

    /// Tries to truncate this `UInt` inplace to the given `target_width`.
    ///
    /// # Note
    ///
    /// - This is a no-op if `self.width()` and `target_width` are equal.
    /// - This operation is inplace as long as `self.width()` and `target_width`
    ///   require the same amount of digits for their representation.
    ///
    /// # Errors
    ///
    /// - If the `target_width` is greater than the current width.
    pub fn truncate<W>(&mut self, target_width: W) -> Result<()>
    where
        W: Into<BitWidth>,
    {
        self.value.truncate(target_width)
    }

    // ========================================================================

    /// Tries to zero-extend this `UInt` inplace to the given `target_width`
    /// and returns the result.
    ///
    /// # Note
    ///
    /// - This is useful for method chaining.
    /// - For more details look into [`extend`](struct.UInt.html#method.extend).
    ///
    /// # Errors
    ///
    /// - If the `target_width` is less than the current width.
    pub fn into_extend<W>(self, target_width: W) -> Result<UInt>
    where
        W: Into<BitWidth>,
    {
        try_forward_bin_mut_impl(self, target_width, UInt::extend)
    }

    /// Tries to extend this `UInt` inplace to the given `target_width`.
    ///
    /// # Note
    ///
    /// - This is a no-op if `self.width()` and `target_width` are equal.
    /// - This operation is inplace as long as `self.width()` and `target_width`
    ///   require the same amount of digits for their representation.
    ///
    /// # Errors
    ///
    /// - If the `target_width` is less than the current width.
    pub fn extend<W>(&mut self, target_width: W) -> Result<()>
    where
        W: Into<BitWidth>,
    {
        self.value.zero_extend(target_width)
    }

    // ========================================================================

    /// Resizes this `UInt` to the given `target_width`
    /// and returns the result.
    ///
    /// # Note
    ///
    /// - This is useful for method chaining.
    /// - For more details look into [`resize`](struct.UInt.html#method.resize).
    pub fn into_resize<W>(self, target_width: W) -> UInt
    where
        W: Into<BitWidth>,
    {
        forward_bin_mut_impl(self, target_width, UInt::resize)
    }

    /// Resizes the given `UInt` inplace.
    ///
    /// # Note
    ///
    /// This operation will forward to
    ///
    /// - [`truncate`](struct.UInt.html#method.truncate) if `target_width` is
    ///   less than or equal to the width of the given `UInt`
    /// - [`extend`](struct.UInt.html#method.extend) otherwise
    pub fn resize<W>(&mut self, target_width: W)
    where
        W: Into<BitWidth>,
    {
        self.value.zero_resize(target_width)
    }
}

/// # Bitwise Operations
impl UInt {
    /// Flips all bits of `self` and returns the result.
    pub fn into_bitnot(self) -> Self {
        forward_mut_impl(self, UInt::bitnot)
    }

    /// Flip all bits of this `UInt` inplace.
    pub fn bitnot(&mut self) {
        self.value.bitnot()
    }

    /// Tries to bit-and assign this `UInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitand(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::bitand_assign)
    }

    /// Bit-and assigns all bits of this `UInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitand_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.bitand_assign(&rhs.value)
    }

    /// Tries to bit-and assign this `UInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitor(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::bitor_assign)
    }

    /// Bit-or assigns all bits of this `UInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitor_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.bitor_assign(&rhs.value)
    }

    /// Tries to bit-xor assign this `UInt` inplace to `rhs`
    /// and returns the result.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn into_bitxor(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::bitxor_assign)
    }

    /// Bit-xor assigns all bits of this `UInt` with the bits of `rhs`.
    ///
    /// **Note:** This operation is inplace of `self` and won't allocate memory.
    ///
    /// # Errors
    ///
    /// If `self` and `rhs` have unmatching bit widths.
    pub fn bitxor_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.bitxor_assign(&rhs.value)
    }
}

/// # Bitwise Access
impl UInt {
    /// Returns the bit at the given bit position `pos`.
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `UInt`.
    pub fn get_bit_at<P>(&self, pos: P) -> Result<bool>
    where
        P: Into<BitPos>,
    {
        self.value.get_bit_at(pos)
    }

    /// Sets the bit at the given bit position `pos` to one (`1`).
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `UInt`.
    pub fn set_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        self.value.set_bit_at(pos)
    }

    /// Sets the bit at the given bit position `pos` to zero (`0`).
    ///
    /// # Errors
    ///
    /// - If `pos` is not a valid bit position for the width of this `UInt`.
    pub fn unset_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        self.value.unset_bit_at(pos)
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
    /// - If `pos` is not a valid bit position for the width of this `UInt`.
    pub fn flip_bit_at<P>(&mut self, pos: P) -> Result<()>
    where
        P: Into<BitPos>,
    {
        self.value.flip_bit_at(pos)
    }

    /// Sets all bits of this `UInt` to one (`1`).
    pub fn set_all(&mut self) {
        self.value.set_all()
    }

    /// Returns `true` if all bits in this `UInt` are set.
    pub fn is_all_set(&self) -> bool {
        self.value.is_all_set()
    }

    /// Sets all bits of this `UInt` to zero (`0`).
    pub fn unset_all(&mut self) {
        self.value.unset_all()
    }

    /// Returns `true` if all bits in this `UInt` are unset.
    pub fn is_all_unset(&self) -> bool {
        self.value.is_all_unset()
    }

    /// Flips all bits of this `UInt`.
    pub fn flip_all(&mut self) {
        self.value.flip_all()
    }
}

/// # Bitwise utility methods.
impl UInt {
    /// Returns the number of ones in the binary representation of this `UInt`.
    pub fn count_ones(&self) -> usize {
        self.value.count_ones()
    }

    /// Returns the number of zeros in the binary representation of this `UInt`.
    pub fn count_zeros(&self) -> usize {
        self.value.count_zeros()
    }

    /// Returns the number of leading zeros in the binary representation of this
    /// `UInt`.
    pub fn leading_zeros(&self) -> usize {
        self.value.leading_zeros()
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// this `UInt`.
    pub fn trailing_zeros(&self) -> usize {
        self.value.trailing_zeros()
    }
}

/// # Arithmetic Operations
impl UInt {
    /// Negates this `Int` inplace. Note that this will overflow for all values
    /// except 0.
    ///
    /// **Note:** This will **not** allocate memory.
    pub fn wrapping_neg(&mut self) {
        self.value.wrapping_neg()
    }

    /// Negates this `Int` inplace and returns the result. Note that this will
    /// overflow for all values except 0.
    ///
    /// **Note:** This will **not** allocate memory.
    pub fn into_wrapping_neg(self) -> UInt {
        forward_mut_impl(self, UInt::wrapping_neg)
    }

    /// Adds `rhs` to `self` and returns the result.
    ///
    /// **Note:** This will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_add(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::wrapping_add_assign)
    }

    /// Add-assigns `rhs` to `self` inplace.
    ///
    /// **Note:** This will **not** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_add_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.wrapping_add_assign(&rhs.value)
    }

    /// Subtracts `rhs` from `self` and returns the result.
    ///
    /// # Note
    ///
    /// In the low-level bit-wise representation there is no difference between
    /// signed and unsigned subtraction of fixed bit-width integers. (Cite:
    /// LLVM)
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_sub(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::wrapping_sub_assign)
    }

    /// Subtract-assigns `rhs` from `self` inplace.
    ///
    /// # Note
    ///
    /// In the low-level bit-wise representation there is no difference between
    /// signed and unsigned subtraction of fixed bit-width integers. (Cite:
    /// LLVM)
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_sub_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.wrapping_sub_assign(&rhs.value)
    }

    /// Subtracts `rhs` from `self` and returns the result.
    ///
    /// # Note
    ///
    /// In the low-level bit-wise representation there is no difference between
    /// signed and unsigned multiplication of fixed bit-width integers.
    /// (Cite: LLVM)
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_mul(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::wrapping_mul_assign)
    }

    /// Multiply-assigns `rhs` to `self` inplace.
    ///
    /// # Note
    ///
    /// In the low-level bit-wise representation there is no difference between
    /// signed and unsigned multiplication of fixed bit-width integers.
    /// (Cite: LLVM)
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_mul_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.wrapping_mul_assign(&rhs.value)
    }

    /// Divides `self` by `rhs` and returns the result.
    ///
    /// # Note
    ///
    /// - This operation will **not** allocate memory and computes inplace of
    ///   `self`.
    /// - In the low-level machine abstraction signed division and unsigned
    ///   division are two different operations.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_div(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::wrapping_div_assign)
    }

    /// Assignes `self` to the division of `self` by `rhs`.
    ///
    /// # Note
    ///
    /// - This operation will **not** allocate memory and computes inplace of
    ///   `self`.
    /// - In the low-level machine abstraction signed division and unsigned
    ///   division are two different operations.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_div_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.wrapping_udiv_assign(&rhs.value)
    }

    /// Calculates the **unsigned** remainder of `self` by `rhs` and returns the
    /// result.
    ///
    /// # Note
    ///
    /// - This operation will **not** allocate memory and computes inplace of
    ///   `self`.
    /// - In the low-level machine abstraction signed division and unsigned
    ///   division are two different operations.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_rem(self, rhs: &UInt) -> Result<UInt> {
        try_forward_bin_mut_impl(self, rhs, UInt::wrapping_rem_assign)
    }

    /// Assignes `self` to the **unsigned** remainder of `self` by `rhs`.
    ///
    /// # Note
    ///
    /// - This operation will **not** allocate memory and computes inplace of
    ///   `self`.
    /// - In the low-level machine abstraction signed division and unsigned
    ///   division are two different operations.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_rem_assign(&mut self, rhs: &UInt) -> Result<()> {
        self.value.wrapping_urem_assign(&rhs.value)
    }
}

// ============================================================================
//  Binary, Oct, LowerHex and UpperHex implementations
// ============================================================================

use core::fmt;

impl fmt::Binary for UInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl fmt::Octal for UInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl fmt::LowerHex for UInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl fmt::UpperHex for UInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests {
        use super::*;

        #[test]
        fn one() {
            assert_eq!(UInt::one(BitWidth::w1()), UInt::from_bool(true));
            assert_eq!(UInt::one(BitWidth::w8()), UInt::from_u8(1));
            assert_eq!(UInt::one(BitWidth::w16()), UInt::from_u16(1));
            assert_eq!(UInt::one(BitWidth::w32()), UInt::from_u32(1));
            assert_eq!(UInt::one(BitWidth::w64()), UInt::from_u64(1));
            assert_eq!(UInt::one(BitWidth::w128()), UInt::from_u128(1));
            assert_eq!(
                UInt::one(BitWidth::new(192).unwrap()),
                UInt::from([0u64, 0, 1])
            );
        }

        #[test]
        fn count() {
            assert_eq!(UInt::one(BitWidth::w1()).count_ones(), 1);
            assert_eq!(UInt::one(BitWidth::w8()).count_ones(), 1);
            assert_eq!(UInt::one(BitWidth::w16()).count_ones(), 1);
            assert_eq!(UInt::one(BitWidth::w32()).count_ones(), 1);
            assert_eq!(UInt::one(BitWidth::w64()).count_ones(), 1);
            assert_eq!(UInt::one(BitWidth::w128()).count_ones(), 1);

            assert_eq!(UInt::one(BitWidth::w1()).count_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w8()).count_zeros(), 7);
            assert_eq!(UInt::one(BitWidth::w16()).count_zeros(), 15);
            assert_eq!(UInt::one(BitWidth::w32()).count_zeros(), 31);
            assert_eq!(UInt::one(BitWidth::w64()).count_zeros(), 63);
            assert_eq!(UInt::one(BitWidth::w128()).count_zeros(), 127);

            assert_eq!(UInt::one(BitWidth::w1()).leading_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w8()).leading_zeros(), 7);
            assert_eq!(UInt::one(BitWidth::w16()).leading_zeros(), 15);
            assert_eq!(UInt::one(BitWidth::w32()).leading_zeros(), 31);
            assert_eq!(UInt::one(BitWidth::w64()).leading_zeros(), 63);
            assert_eq!(UInt::one(BitWidth::w128()).leading_zeros(), 127);

            assert_eq!(UInt::one(BitWidth::w1()).trailing_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w8()).trailing_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w16()).trailing_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w32()).trailing_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w64()).trailing_zeros(), 0);
            assert_eq!(UInt::one(BitWidth::w128()).trailing_zeros(), 0);
        }
    }
}
