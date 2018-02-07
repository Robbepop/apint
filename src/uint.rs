use apint::ApInt;
use traits::Width;
use digit::Bit;
use bitwidth::BitWidth;
use errors::Result;
use apint::{ShiftAmount};
use bitpos::{BitPos};
use int::Int;

#[cfg(feature = "rand_support")]
use rand;

use std::cmp::Ordering;
use std::ops::{
	Not,
	BitAnd,
	BitOr,
	BitXor,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign,
	Add,
	Sub,
	Mul,
    Div,
    Rem,
	AddAssign,
	SubAssign,
	MulAssign,
    DivAssign,
    RemAssign
};

/// Unsigned machine integer with arbitrary bitwidths and modulo arithmetics.
/// 
/// Thin convenience wrapper around `ApInt` for static unsigned interpretation of the value.
/// 
/// This very cheaply transformes to and from `ApInt` and `Int` instances and together with
/// `Int` offers a more elegant and higher-level abstraction interface to the lower-level `ApInt`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UInt {
    value: ApInt,
}

impl From<ApInt> for UInt {
    fn from(value: ApInt) -> UInt {
        UInt { value }
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

    /// Returns the largest `UInt` that can be represented by the given `BitWidth`.
    pub fn max_value(width: BitWidth) -> UInt {
        UInt::from(ApInt::unsigned_max_value(width))
    }
}

impl<B> From<B> for UInt
	where B: Into<Bit>
{
	#[inline]
	fn from(bit: B) -> UInt {
        UInt::from_bit(bit)
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

impl UInt {

	/// Less-than (`lt`) comparison between `self` and `rhs`.
	/// 
	/// # Note
	/// 
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

impl PartialOrd for UInt {
    fn partial_cmp(&self, rhs: &UInt) -> Option<Ordering> {
        if self.value.width() != rhs.value.width() {
            return None;
        }
        if self.checked_lt(rhs).unwrap() {
            return Some(Ordering::Less);
        }
        if self.value == rhs.value {
            return Some(Ordering::Equal);
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

/// # Shifts
impl UInt {
   	/// Shift this `UInt` left by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `UInt`.
	pub fn checked_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		self.value.checked_shl_assign(shift_amount)
	}

	/// Shift this `UInt` left by the given `shift_amount` bits and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `UInt`.
	pub fn into_checked_shl<S>(self, shift_amount: S) -> Result<UInt>
		where S: Into<ShiftAmount>
	{
		self.value.into_checked_shl(shift_amount).map(UInt::from)
	}

	/// Right-shifts this `UInt` by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `UInt`.
	pub fn checked_shr_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		self.value.checked_lshr_assign(shift_amount)
	}

	/// Right-shifts this `UInt` by the given `shift_amount` bits
	/// and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `UInt`.
	pub fn into_checked_shr<S>(self, shift_amount: S) -> Result<UInt>
		where S: Into<ShiftAmount>
	{
		self.value.into_checked_lshr(shift_amount).map(UInt::from)
	}
}

use std::ops::{Shl, ShlAssign, Shr, ShrAssign};

impl<S> Shl<S> for UInt
    where S: Into<ShiftAmount>
{
    type Output = UInt;

    fn shl(self, shift_amount: S) -> Self::Output {
        self.into_checked_shl(shift_amount).unwrap()
    }
}

impl<S> Shr<S> for UInt
    where S: Into<ShiftAmount>
{
    type Output = UInt;

    fn shr(self, shift_amount: S) -> Self::Output {
        self.into_checked_shr(shift_amount).unwrap()
    }
}

impl<S> ShlAssign<S> for UInt
    where S: Into<ShiftAmount>
{
    fn shl_assign(&mut self, shift_amount: S) {
        self.checked_shl_assign(shift_amount).unwrap()
    }
}

impl<S> ShrAssign<S> for UInt
    where S: Into<ShiftAmount>
{
    fn shr_assign(&mut self, shift_amount: S) {
        self.checked_shr_assign(shift_amount).unwrap()
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
        where R: rand::Rng
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
        where R: rand::Rng
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
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.truncate(target_width)?;
		Ok(this)
	}

	/// Tries to strictly truncate this `UInt` inplace to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`strict_truncate`](struct.UInt.html#method.strict_truncate).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than the bitwidth of the given `UInt`.
	pub fn into_strict_truncate<W>(self, target_width: W) -> Result<UInt>
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.strict_truncate(target_width)?;
		Ok(this)
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
		where W: Into<BitWidth>
	{
		self.value.truncate(target_width)
	}

	/// Tries to strictly truncate this `UInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - Strict truncation means that the resulting `UInt` is ensured to have
	///   a smaller `BitWidth` than before this operation.
	/// - For more details look into
	///   [`truncate`](struct.UInt.html#method.truncate).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than the bitwidth of the given `UInt`.
	pub fn strict_truncate<W>(&mut self, target_width: W) -> Result<()>
		where W: Into<BitWidth>
	{
		self.value.strict_truncate(target_width)
	}

	// ========================================================================

	/// Tries to zero-extend this `UInt` inplace to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`extend`](struct.UInt.html#method.extend).
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn into_extend<W>(self, target_width: W) -> Result<UInt>
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.extend(target_width)?;
		Ok(this)
	}

	/// Tries to strictly extend this `UInt` inplace to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`strict_extend`](struct.UInt.html#method.strict_extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than the bitwidth of the given `UInt`.
	pub fn into_strict_extend<W>(self, target_width: W) -> Result<UInt>
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.strict_extend(target_width)?;
		Ok(this)
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
		where W: Into<BitWidth>
	{
		self.value.zero_extend(target_width)
	}

	/// Tries to strictly extends this `UInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - Strict extension means that the resulting `UInt` is ensured to have
	///   a larger `BitWidth` than before this operation.
	/// - For more details look into
	///   [`extend`](struct.UInt.html#method.extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than the bitwidth of the given `UInt`.
	pub fn strict_extend<W>(&mut self, target_width: W) -> Result<()>
		where W: Into<BitWidth>
	{
		self.value.strict_zero_extend(target_width)
	}

	// ========================================================================

	/// Resizes this `UInt` to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`resize`](struct.UInt.html#method.resize).
	pub fn into_resize<W>(self, target_width: W) -> UInt
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.resize(target_width);
		this
	}

	/// Tries to strictly resize this `UInt` to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`strict_resize`](struct.UInt.html#method.strict_resize).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the bitwidth of the given `UInt`.
	pub fn into_strict_resize<W>(self, target_width: W) -> Result<UInt>
		where W: Into<BitWidth>
	{
		let mut this = self;
		this.strict_resize(target_width)?;
		Ok(this)
	}

	/// Resizes the given `UInt` inplace.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`truncate`](struct.UInt.html#method.truncate)
	///   if `target_width` is less than or equal to the width of
	///   the given `UInt`
	/// - [`extend`](struct.UInt.html#method.extend)
	///   otherwise
	pub fn resize<W>(&mut self, target_width: W)
		where W: Into<BitWidth>
	{
		self.value.zero_resize(target_width)
	}

	/// Strictly resizes the given `UInt` inplace.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`strict_truncate`](struct.UInt.html#method.strict_truncate)
	///   if `target_width` is less than or equal to the width of
	///   the given `UInt`
	/// - [`strict_extend`](struct.UInt.html#method.strict_extend)
	///   otherwise
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the bitwidth of the given `UInt`.
	pub fn strict_resize<W>(&mut self, target_width: W) -> Result<()>
		where W: Into<BitWidth>
	{
		self.value.strict_zero_resize(target_width)
	}
}

/// # Bitwise Operations
impl UInt {
	/// Flip all bits of this `UInt` inplace.
	pub fn bitnot(&mut self) {
		self.value.bitnot()
	}

	/// Tries to bit-and assign this `UInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitand`](struct.UInt.html#method.checked_bitand).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitand(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_bitand_assign(rhs)?;
		Ok(this)
	}

	/// Bit-and assigns all bits of this `UInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitand_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_bitand_assign(&rhs.value)
	}

	/// Tries to bit-and assign this `UInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitor`](struct.UInt.html#method.checked_bitor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitor(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_bitor_assign(rhs)?;
		Ok(this)
	}

	/// Bit-or assigns all bits of this `UInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitor_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_bitor_assign(&rhs.value)
	}

	/// Tries to bit-xor assign this `UInt` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitxor`](struct.UInt.html#method.checked_bitxor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitxor(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_bitor_assign(rhs)?;
		Ok(this)
	}

	/// Bit-xor assigns all bits of this `UInt` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitxor_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_bitxor_assign(&rhs.value)
	}
}

/// # Bitwise Access
impl UInt {
	/// Returns the bit at the given bit position `pos`.
	/// 
	/// This returns
	/// 
	/// - `Bit::Set` if the bit at `pos` is `1`
	/// - `Bit::Unset` otherwise
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `UInt`.
	pub fn get_bit_at<P>(&self, pos: P) -> Result<Bit>
		where P: Into<BitPos>
	{
		self.value.get_bit_at(pos)
	}

	/// Sets the bit at the given bit position `pos` to one (`1`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `UInt`.
	pub fn set_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		self.value.set_bit_at(pos)
	}

	/// Sets the bit at the given bit position `pos` to zero (`0`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `UInt`.
	pub fn unset_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		self.value.unset_bit_at(pos)
	}

	/// Flips the bit at the given bit position `pos`.
	/// 
	/// # Note
	/// 
	/// - If the bit at the given position was `0` it will be `1`
	///   after this operation and vice versa.
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `UInt`.
	pub fn flip_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		self.value.flip_bit_at(pos)
	}

	/// Sets all bits of this `UInt` to one (`1`).
	pub fn set_all(&mut self) {
		self.value.set_all()
	}

	/// Sets all bits of this `UInt` to zero (`0`).
	pub fn unset_all(&mut self) {
		self.value.unset_all()
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

	/// Returns the number of leading zeros in the binary representation of this `UInt`.
	pub fn leading_zeros(&self) -> usize {
		self.value.leading_zeros()
	}

	/// Returns the number of trailing zeros in the binary representation of this `UInt`.
	pub fn trailing_zeros(&self) -> usize {
		self.value.trailing_zeros()
	}
}

//  ===========================================================================
//  `Not` (bitwise) impls
//  ===========================================================================

impl Not for UInt {
	type Output = UInt;

	fn not(self) -> Self::Output {
		let mut this = self;
		this.bitnot();
		this
	}
}

//  ===========================================================================
//  `BitAnd` impls
//  ===========================================================================

impl<'a> BitAnd<&'a UInt> for UInt {
    type Output = UInt;

    fn bitand(self, rhs: &'a UInt) -> Self::Output {
        self.into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a UInt> for &'b UInt {
    type Output = UInt;

    fn bitand(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a UInt> for &'b mut UInt {
    type Output = UInt;

    fn bitand(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitOr` impls
//  ===========================================================================

impl<'a> BitOr<&'a UInt> for UInt {
    type Output = UInt;

    fn bitor(self, rhs: &'a UInt) -> Self::Output {
        self.into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a UInt> for &'b UInt {
    type Output = UInt;

    fn bitor(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a UInt> for &'b mut UInt {
    type Output = UInt;

    fn bitor(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitXor` impls
//  ===========================================================================

impl<'a> BitXor<&'a UInt> for UInt {
    type Output = UInt;

    fn bitxor(self, rhs: &'a UInt) -> Self::Output {
        self.into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a UInt> for &'b UInt {
    type Output = UInt;

    fn bitxor(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a UInt> for &'b mut UInt {
    type Output = UInt;

    fn bitxor(self, rhs: &'a UInt) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitAndAssign`, `BitOrAssign` and `BitXorAssign` impls
//  ===========================================================================

impl<'a> BitAndAssign<&'a UInt> for UInt {
    fn bitand_assign(&mut self, rhs: &'a UInt) {
        self.checked_bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a UInt> for UInt {
    fn bitor_assign(&mut self, rhs: &'a UInt) {
        self.checked_bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a UInt> for UInt {
    fn bitxor_assign(&mut self, rhs: &'a UInt) {
        self.checked_bitxor_assign(rhs).unwrap();
    }
}

/// # Arithmetic Operations
impl UInt {
	/// Adds `rhs` to `self` and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_add(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_add_assign(rhs)?;
		Ok(this)
	}

	/// Add-assigns `rhs` to `self` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_add_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_add_assign(&rhs.value)
	}

	/// Subtracts `rhs` from `self` and returns the result.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_sub(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_add_assign(rhs)?;
		Ok(this)
	}

	/// Subtract-assigns `rhs` from `self` inplace.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned subtraction of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_sub_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_sub_assign(&rhs.value)
	}

	/// Subtracts `rhs` from `self` and returns the result.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_mul(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_mul_assign(rhs)?;
		Ok(this)
	}

	/// Multiply-assigns `rhs` to `self` inplace.
	/// 
	/// # Note
	/// 
	/// In the low-level bit-wise representation there is no difference between signed
	/// and unsigned multiplication of fixed bit-width integers. (Cite: LLVM)
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_mul_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_mul_assign(&rhs.value)
	}

	/// Divides `self` by `rhs` and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_div(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_div_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the division of `self` by `rhs`.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_div_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_udiv_assign(&rhs.value)
	}

	/// Calculates the **unsigned** remainder of `self` by `rhs` and returns the result.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_rem(self, rhs: &UInt) -> Result<UInt> {
		let mut this = self;
		this.checked_rem_assign(rhs)?;
		Ok(this)
	}

	/// Assignes `self` to the **unsigned** remainder of `self` by `rhs`.
	/// 
	/// # Note
	/// 
	/// - This operation will **not** allocate memory and computes inplace of `self`.
	/// - In the low-level machine abstraction signed division and unsigned division
	///   are two different operations.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_rem_assign(&mut self, rhs: &UInt) -> Result<()> {
		self.value.checked_urem_assign(&rhs.value)
	}
}

// ============================================================================
//  Add and Add-Assign: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl<'a> Add<&'a UInt> for UInt {
	type Output = UInt;

	fn add(self, rhs: &'a UInt) -> Self::Output {
		self.into_checked_add(rhs).unwrap()
	}
}

impl<'a, 'b> Add<&'a UInt> for &'b UInt {
	type Output = UInt;

	fn add(self, rhs: &'a UInt) -> Self::Output {
		self.clone().into_checked_add(rhs).unwrap()
	}
}

impl<'a> AddAssign<&'a UInt> for UInt {
	fn add_assign(&mut self, rhs: &'a UInt) {
		self.checked_add_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Sub and Sub-Assign: `std::ops::Sub` and `std::ops::SubAssign`
// ============================================================================

impl<'a> Sub<&'a UInt> for UInt {
	type Output = UInt;

	fn sub(self, rhs: &'a UInt) -> Self::Output {
		self.into_checked_sub(rhs).unwrap()
	}
}

impl<'a, 'b> Sub<&'a UInt> for &'b UInt {
	type Output = UInt;

	fn sub(self, rhs: &'a UInt) -> Self::Output {
		self.clone().into_checked_sub(rhs).unwrap()
	}
}

impl<'a> SubAssign<&'a UInt> for UInt {
	fn sub_assign(&mut self, rhs: &'a UInt) {
		self.checked_sub_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Mul and Mul-Assign: `std::ops::Mul` and `std::ops::MulAssign`
// ============================================================================

impl<'a> Mul<&'a UInt> for UInt {
	type Output = UInt;

	fn mul(self, rhs: &'a UInt) -> Self::Output {
		self.into_checked_mul(rhs).unwrap()
	}
}

impl<'a, 'b> Mul<&'a UInt> for &'b UInt {
	type Output = UInt;

	fn mul(self, rhs: &'a UInt) -> Self::Output {
		self.clone().into_checked_mul(rhs).unwrap()
	}
}

impl<'a> MulAssign<&'a UInt> for UInt {
	fn mul_assign(&mut self, rhs: &'a UInt) {
		self.checked_mul_assign(rhs).unwrap();
	}
}

// ============================================================================
//  Div and Div-Assign: `std::ops::Div` and `std::ops::DivAssign`
// ============================================================================

impl<'a> Div<&'a UInt> for UInt {
	type Output = UInt;

	fn div(self, rhs: &'a UInt) -> Self::Output {
		self.into_checked_div(rhs).unwrap()
	}
}

impl<'a, 'b> Div<&'a UInt> for &'b UInt {
	type Output = UInt;

	fn div(self, rhs: &'a UInt) -> Self::Output {
		self.clone().into_checked_div(rhs).unwrap()
	}
}

impl<'a> DivAssign<&'a UInt> for UInt {
	fn div_assign(&mut self, rhs: &'a UInt) {
		self.checked_div_assign(rhs).unwrap();
	}
}

// ============================================================================
//  Rem and Rem-Assign: `std::ops::Rem` and `std::ops::RemAssign`
// ============================================================================

impl<'a> Rem<&'a UInt> for UInt {
	type Output = UInt;

	fn rem(self, rhs: &'a UInt) -> Self::Output {
		self.into_checked_rem(rhs).unwrap()
	}
}

impl<'a, 'b> Rem<&'a UInt> for &'b UInt {
	type Output = UInt;

	fn rem(self, rhs: &'a UInt) -> Self::Output {
		self.clone().into_checked_rem(rhs).unwrap()
	}
}

impl<'a> RemAssign<&'a UInt> for UInt {
	fn rem_assign(&mut self, rhs: &'a UInt) {
		self.checked_rem_assign(rhs).unwrap();
	}
}