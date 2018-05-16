use apint::ApInt;
use traits::Width;
use digit::Bit;
use bitwidth::BitWidth;
use errors::Result;
use apint::{ShiftAmount};
use bitpos::{BitPos};
use uint::UInt;
use utils::{try_forward_bin_mut_impl, forward_mut_impl, forward_bin_mut_impl};

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
	Neg,
	Add,
	Sub,
	Mul,
    Div,
    Rem,
	AddAssign,
	SubAssign,
	MulAssign,
    DivAssign,
    RemAssign,
	Shl,
	ShlAssign,
	Shr,
	ShrAssign
};

/// Signed machine integer with arbitrary bitwidths and modulo arithmetics.
/// 
/// Thin convenience wrapper around `ApInt` for static signed interpretation of the value.
/// 
/// This very cheaply transformes to and from `ApInt` and `UInt` instances and together with
/// `UInt` offers a more elegant and higher-level abstraction interface to the lower-level `ApInt`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Int {
    value: ApInt,
}

impl From<ApInt> for Int {
    fn from(value: ApInt) -> Int {
        Int { value }
    }
}

impl Int {
    /// Transforms this `Int` into an equivalent `ApInt` instance.
    pub fn into_apint(self) -> ApInt {
        self.value
    }

    /// Transforms this `Int` into an equivalent `UInt` instance.
    pub fn into_unsigned(self) -> UInt {
        UInt::from(self.value)
    }
}

/// # Constructors
impl Int {
    /// Creates a new `Int` from the given `Bit` value with a bit width of `1`.
    ///
    /// This function is generic over types that are convertible to `Bit` such as `bool`.
    pub fn from_bit<B>(bit: B) -> Int
    where
        B: Into<Bit>,
    {
        Int::from(ApInt::from_bit(bit))
    }

    /// Creates a new `Int` from a given `i8` value with a bit-width of 8.
    #[inline]
    pub fn from_i8(val: i8) -> Int {
        Int::from(ApInt::from_i8(val))
    }

    /// Creates a new `Int` from a given `i16` value with a bit-width of 16.
    #[inline]
    pub fn from_i16(val: i16) -> Int {
        Int::from(ApInt::from_i16(val))
    }

    /// Creates a new `Int` from a given `i32` value with a bit-width of 32.
    #[inline]
    pub fn from_i32(val: i32) -> Int {
        Int::from(ApInt::from_i32(val))
    }

    /// Creates a new `Int` from a given `i64` value with a bit-width of 64.
    #[inline]
    pub fn from_i64(val: i64) -> Int {
        Int::from(ApInt::from_i64(val))
    }

    /// Creates a new `Int` from a given `i64` value with a bit-width of 64.
    pub fn from_i128(val: i128) -> Int {
        Int::from(ApInt::from_i128(val))
    }

    /// Creates a new `Int` with the given bit width that represents zero.
    pub fn zero(width: BitWidth) -> Int {
        Int::from(ApInt::zero(width))
    }

    /// Creates a new `Int` with the given bit width that represents one.
    pub fn one(width: BitWidth) -> Int {
        Int::from(ApInt::one(width))
    }

    /// Creates a new `Int` with the given bit width that has all bits unset.
    ///
    /// **Note:** This is equal to calling `Int::zero` with the given `width`.
    pub fn all_unset(width: BitWidth) -> Int {
        Int::zero(width)
    }

    /// Creates a new `Int` with the given bit width that has all bits set.
    ///
    /// # Note
    ///
    /// - This is equal to minus one on any twos-complement machine.
    pub fn all_set(width: BitWidth) -> Int {
        Int::from(ApInt::all_set(width))
    }

    /// Returns the smallest `Int` that can be represented by the given `BitWidth`.
    pub fn min_value(width: BitWidth) -> Int {
        Int::from(ApInt::signed_min_value(width))
    }

    /// Returns the largest `Int` that can be represented by the given `BitWidth`.
    pub fn max_value(width: BitWidth) -> Int {
        Int::from(ApInt::signed_max_value(width))
    }
}

impl<B> From<B> for Int
	where B: Into<Bit>
{
	#[inline]
	fn from(bit: B) -> Int {
        Int::from_bit(bit)
	}
}

impl From<i8> for Int {
    fn from(val: i8) -> Int {
        Int::from_i8(val)
    }
}

impl From<i16> for Int {
    fn from(val: i16) -> Int {
        Int::from_i16(val)
    }
}

impl From<i32> for Int {
    fn from(val: i32) -> Int {
        Int::from_i32(val)
    }
}

impl From<i64> for Int {
    fn from(val: i64) -> Int {
        Int::from_i64(val)
    }
}

impl From<i128> for Int {
    fn from(val: i128) -> Int {
        Int::from_i128(val)
    }
}

macro_rules! impl_from_array_for_Int {
	($n:expr) => {
		impl From<[i64; $n]> for Int {
			fn from(val: [i64; $n]) -> Int {
				Int::from(ApInt::from(val))
			}
		}
	}
}

impl_from_array_for_Int!(2); // 128 bits
impl_from_array_for_Int!(3); // 192 bits
impl_from_array_for_Int!(4); // 256 bits
impl_from_array_for_Int!(5); // 320 bits
impl_from_array_for_Int!(6); // 384 bits
impl_from_array_for_Int!(7); // 448 bits
impl_from_array_for_Int!(8); // 512 bits
impl_from_array_for_Int!(16); // 1024 bits
impl_from_array_for_Int!(32); // 2048 bits

/// # Utilities
impl Int {
    /// Returns `true` if this `Int` represents the value zero (`0`).
    ///
    /// # Note
    ///
    /// - Zero (`0`) is also called the additive neutral element.
    /// - This operation is more efficient than comparing two instances
    ///   of `Int` for the same reason.
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    /// Returns `true` if this `Int` represents the value one (`1`).
    ///
    /// # Note
    ///
    /// - One (`1`) is also called the multiplicative neutral element.
    /// - This operation is more efficient than comparing two instances
    ///   of `Int` for the same reason.
    pub fn is_one(&self) -> bool {
        self.value.is_one()
	}

    /// Returns `true` if this `Int` represents an even number.
    pub fn is_even(&self) -> bool {
        self.value.is_even()
    }

    /// Returns `true` if this `Int` represents an odd number.
    pub fn is_odd(&self) -> bool {
        self.value.is_odd()
    }

	/// Returns `true` if the value of this `Int` is positive.
	pub fn is_positive(&self) -> bool {
		self.sign_bit() == Bit::Unset
	}

	/// Returns `true` if the value of this `Int` is negative.
	pub fn is_negative(&self) -> bool {
		!self.is_positive()
	}

	/// Returns a number representing sign of this `ApInt`.
	/// 
	/// - `0` if the number is zero
	/// - `1` if the number is positive
	/// - `-1` if the number is negative
	pub fn signum(&self) -> i8 {
		if self.is_zero() {
			return 0
		}
		if self.is_negative() {
			return -1
		}
		1
	}

	/// Returns an absolute value representation of this `Int`.
	/// 
	/// # Note
	/// 
	/// - Consumes `self`.
	/// - Does nothing for positive `Int` instances.
	pub fn into_abs(self) -> Int {
		forward_mut_impl(self, Int::abs)
	}

	/// Converts this `Int` into its absolute value representation.
	/// 
	/// - Does nothing for positive `Int` instances.
	pub fn abs(&mut self) {
		if self.is_negative() {
			self.negate()
		}
	}

}

/// # Comparisons
impl Int {

	/// Less-than (`lt`) comparison between `self` and `rhs`.
	/// 
	/// # Note
	/// 
	/// - Returns `Ok(true)` if `self < rhs`.
	/// - Interprets both `Int` instances as **unsigned** values.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_lt(&self, rhs: &Int) -> Result<bool> {
		self.value.checked_slt(&rhs.value)
	}

	/// Less-equals (`le`) comparison between `self` and `rhs`.
	/// 
	/// # Note
	/// 
	/// - Returns `Ok(true)` if `self <= rhs`.
	/// - Interprets both `Int` instances as **unsigned** values.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	#[inline]
	pub fn checked_le(&self, rhs: &Int) -> Result<bool> {
		self.value.checked_sle(&rhs.value)
	}

	/// Greater-than (`gt`) comparison between `self` and `rhs`.
	/// 
	/// # Note
	/// 
	/// - Returns `Ok(true)` if `self > rhs`.
	/// - Interprets both `Int` instances as **unsigned** values.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	#[inline]
	pub fn checked_gt(&self, rhs: &Int) -> Result<bool> {
		self.value.checked_sgt(&rhs.value)
	}

	/// Greater-equals (`ge`) comparison between `self` and `rhs`.
	/// 
	/// # Note
	/// 
	/// - Returns `Ok(true)` if `self >= rhs`.
	/// - Interprets both `Int` instances as **unsigned** values.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	#[inline]
	pub fn checked_ge(&self, rhs: &Int) -> Result<bool> {
		self.value.checked_sge(&rhs.value)
	}
}

impl PartialOrd for Int {
    fn partial_cmp(&self, rhs: &Int) -> Option<Ordering> {
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

    fn lt(&self, rhs: &Int) -> bool {
        self.checked_lt(rhs).unwrap_or(false)
    }

    fn le(&self, rhs: &Int) -> bool {
        self.checked_le(rhs).unwrap_or(false)
    }

    fn gt(&self, rhs: &Int) -> bool {
        self.checked_gt(rhs).unwrap_or(false)
    }

    fn ge(&self, rhs: &Int) -> bool {
        self.checked_ge(rhs).unwrap_or(false)
    }
}

/// # To Primitive (Resize)
impl Int {
    /// Resizes this `Int` to a `bool` primitive type.
    ///
    /// Bits in this `Int` that are not within the bounds
    /// of the `bool` are being ignored.
    ///
    /// # Note
    ///
    /// - Basically this returns `true` if the least significant
    ///   bit of this `Int` is `1` and `false` otherwise.
    pub fn resize_to_bool(&self) -> bool {
        self.value.resize_to_bool()
    }

    /// Resizes this `Int` to a `i8` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `8` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i8(&self) -> i8 {
        self.value.resize_to_i8()
    }

    /// Resizes this `Int` to a `i16` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `16` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i16(&self) -> i16 {
        self.value.resize_to_i16()
    }

    /// Resizes this `Int` to a `i32` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `32` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i32(&self) -> i32 {
        self.value.resize_to_i32()
    }

    /// Resizes this `Int` to a `i64` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `64` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i64(&self) -> i64 {
        self.value.resize_to_i64()
    }

    /// Resizes this `Int` to a `i128` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `128` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i128(&self) -> i128 {
        self.value.resize_to_i128()
    }
}

/// # To Primitive (Try-Cast)
impl Int {
    /// Tries to represent the value of this `Int` as a `bool`.
    ///
    /// # Note
    ///
    /// This returns `true` if the value represented by this `Int`
    /// is `1`, returns `false` if the value represented by this
    /// `Int` is `0` and returns an error otherwise.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `bool`.
    pub fn try_to_bool(&self) -> Result<bool> {
        self.value.try_to_bool()
    }

    /// Tries to represent the value of this `Int` as a `i8`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `Int` does not exceed the maximum value of `i8`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `u8`.
    pub fn try_to_i8(&self) -> Result<i8> {
        self.value.try_to_i8()
    }

    /// Tries to represent the value of this `Int` as a `i16`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `Int` does not exceed the maximum value of `i16`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `i16`.
    pub fn try_to_i16(&self) -> Result<i16> {
        self.value.try_to_i16()
    }

    /// Tries to represent the value of this `Int` as a `i32`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `Int` does not exceed the maximum value of `i32`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `i32`.
    pub fn try_to_i32(&self) -> Result<i32> {
        self.value.try_to_i32()
    }

    /// Tries to represent the value of this `Int` as a `i64`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `Int` does not exceed the maximum value of `i64`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `i64`.
    pub fn try_to_i64(&self) -> Result<i64> {
        self.value.try_to_i64()
    }

    /// Tries to represent the value of this `Int` as a `i128`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented
    ///   by this `Int` does not exceed the maximum value of `i128`.
    ///
    /// # Complexity
    ///
    /// - 𝒪(n) where n is the number of digits of this `Int`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `Int` can not be
    ///   represented by a `i128`.
    pub fn try_to_i128(&self) -> Result<i128> {
        self.value.try_to_i128()
    }
}

/// # Shifts
impl Int {
   	/// Shift this `Int` left by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `Int`.
	pub fn checked_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		self.value.checked_shl_assign(shift_amount)
	}

	/// Shift this `Int` left by the given `shift_amount` bits and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `Int`.
	pub fn into_checked_shl<S>(self, shift_amount: S) -> Result<Int>
		where S: Into<ShiftAmount>
	{
		self.value.into_checked_shl(shift_amount).map(Int::from)
	}

	/// Right-shifts this `Int` by the given `shift_amount` bits.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `Int`.
	pub fn checked_shr_assign<S>(&mut self, shift_amount: S) -> Result<()>
		where S: Into<ShiftAmount>
	{
		self.value.checked_ashr_assign(shift_amount)
	}

	/// Right-shifts this `Int` by the given `shift_amount` bits
	/// and returns the result.
	/// 
	/// This operation is inplace and will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If the given `shift_amount` is invalid for the bit width of this `Int`.
	pub fn into_checked_shr<S>(self, shift_amount: S) -> Result<Int>
		where S: Into<ShiftAmount>
	{
		self.value.into_checked_ashr(shift_amount).map(Int::from)
	}
}

impl<S> Shl<S> for Int
    where S: Into<ShiftAmount>
{
    type Output = Int;

    fn shl(self, shift_amount: S) -> Self::Output {
        self.into_checked_shl(shift_amount).unwrap()
    }
}

impl<S> Shr<S> for Int
    where S: Into<ShiftAmount>
{
    type Output = Int;

    fn shr(self, shift_amount: S) -> Self::Output {
        self.into_checked_shr(shift_amount).unwrap()
    }
}

impl<S> ShlAssign<S> for Int
    where S: Into<ShiftAmount>
{
    fn shl_assign(&mut self, shift_amount: S) {
        self.checked_shl_assign(shift_amount).unwrap()
    }
}

impl<S> ShrAssign<S> for Int
    where S: Into<ShiftAmount>
{
    fn shr_assign(&mut self, shift_amount: S) {
        self.checked_shr_assign(shift_amount).unwrap()
    }
}

/// # Random Utilities using `rand` crate.
#[cfg(feature = "rand_support")]
impl Int {
	/// Creates a new `Int` with the given `BitWidth` and random `Digit`s.
	pub fn random_with_width(width: BitWidth) -> Int {
		Int::from(ApInt::random_with_width(width))
	}

	/// Creates a new `Int` with the given `BitWidth` and random `Digit`s
    /// using the given random number generator.
    /// 
    /// **Note:** This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R>(width: BitWidth, rng: &mut R) -> Int
        where R: rand::Rng
    {
        Int::from(ApInt::random_with_width_using(width, rng))
    }

    /// Randomizes the digits of this `Int` inplace.
    /// 
    /// This won't change its `BitWidth`.
    pub fn randomize(&mut self) {
        self.value.randomize()
    }

    /// Randomizes the digits of this `Int` inplace using the given
    /// random number generator.
    /// 
    /// This won't change its `BitWidth`.
    pub fn randomize_using<R>(&mut self, rng: &mut R)
        where R: rand::Rng
    {
        self.value.randomize_using(rng)
    }
}

impl Int {
	/// Assigns `rhs` to this `Int`.
	///
	/// This mutates digits and may affect the bitwidth of `self`
	/// which **might result in an expensive operations**.
	///
	/// After this operation `rhs` and `self` are equal to each other.
	pub fn assign(&mut self, rhs: &Int) {
		self.value.assign(&rhs.value)
	}

	/// Strictly assigns `rhs` to this `Int`.
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
	pub fn strict_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.strict_assign(&rhs.value)
	}
}

/// # Casting: Truncation & Extension
impl Int {
	/// Tries to truncate this `Int` inplace to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`truncate`](struct.Int.html#method.truncate).
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is greater than the current width.
	pub fn into_truncate<W>(self, target_width: W) -> Result<Int>
		where W: Into<BitWidth>
	{
		try_forward_bin_mut_impl(self, target_width, Int::truncate)
	}

	/// Tries to truncate this `Int` inplace to the given `target_width`.
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

	// ========================================================================

	/// Tries to zero-extend this `Int` inplace to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`extend`](struct.Int.html#method.extend).
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn into_extend<W>(self, target_width: W) -> Result<Int>
		where W: Into<BitWidth>
	{
		try_forward_bin_mut_impl(self, target_width, Int::extend)
	}

	/// Tries to extend this `Int` inplace to the given `target_width`.
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
		self.value.sign_extend(target_width)
	}

	// ========================================================================

	/// Resizes this `Int` to the given `target_width`
	/// and returns the result.
	/// 
	/// # Note
	/// 
	/// - This is useful for method chaining.
	/// - For more details look into
	///   [`resize`](struct.Int.html#method.resize).
	pub fn into_resize<W>(self, target_width: W) -> Int
		where W: Into<BitWidth>
	{
		forward_bin_mut_impl(self, target_width, Int::resize)
	}

	/// Resizes the given `Int` inplace.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`truncate`](struct.Int.html#method.truncate)
	///   if `target_width` is less than or equal to the width of
	///   the given `Int`
	/// - [`extend`](struct.Int.html#method.extend)
	///   otherwise
	pub fn resize<W>(&mut self, target_width: W)
		where W: Into<BitWidth>
	{
		self.value.sign_resize(target_width)
	}
}

/// # Bitwise Operations
impl Int {
	/// Flips all bits of `self` and returns the result.
	pub fn into_bitnot(self) -> Self {
		forward_mut_impl(self, Int::bitnot)
	}

	/// Flip all bits of this `Int` inplace.
	pub fn bitnot(&mut self) {
		self.value.bitnot()
	}

	/// Tries to bit-and assign this `Int` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitand`](struct.Int.html#method.checked_bitand).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitand(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_bitand_assign)
	}

	/// Bit-and assigns all bits of this `Int` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitand_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.checked_bitand_assign(&rhs.value)
	}

	/// Tries to bit-and assign this `Int` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitor`](struct.Int.html#method.checked_bitor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitor(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_bitor_assign)
	}

	/// Bit-or assigns all bits of this `Int` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitor_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.checked_bitor_assign(&rhs.value)
	}

	/// Tries to bit-xor assign this `Int` inplace to `rhs`
	/// and returns the result.
	/// 
	/// **Note:** This forwards to
	/// [`checked_bitxor`](struct.Int.html#method.checked_bitxor).
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_bitxor(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_bitxor_assign)
	}

	/// Bit-xor assigns all bits of this `Int` with the bits of `rhs`.
	/// 
	/// **Note:** This operation is inplace of `self` and won't allocate memory.
	/// 
	/// # Errors
	/// 
	/// If `self` and `rhs` have unmatching bit widths.
	pub fn checked_bitxor_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.checked_bitxor_assign(&rhs.value)
	}
}

/// # Bitwise Access
impl Int {
	/// Returns the bit at the given bit position `pos`.
	/// 
	/// This returns
	/// 
	/// - `Bit::Set` if the bit at `pos` is `1`
	/// - `Bit::Unset` otherwise
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `Int`.
	pub fn get_bit_at<P>(&self, pos: P) -> Result<Bit>
		where P: Into<BitPos>
	{
		self.value.get_bit_at(pos)
	}

	/// Sets the bit at the given bit position `pos` to one (`1`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `Int`.
	pub fn set_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		self.value.set_bit_at(pos)
	}

	/// Sets the bit at the given bit position `pos` to zero (`0`).
	/// 
	/// # Errors
	/// 
	/// - If `pos` is not a valid bit position for the width of this `Int`.
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
	/// - If `pos` is not a valid bit position for the width of this `Int`.
	pub fn flip_bit_at<P>(&mut self, pos: P) -> Result<()>
		where P: Into<BitPos>
	{
		self.value.flip_bit_at(pos)
	}

	/// Sets all bits of this `Int` to one (`1`).
	pub fn set_all(&mut self) {
		self.value.set_all()
	}

	/// Returns `true` if all bits in this `Int` are set.
	pub fn is_all_set(&self) -> bool {
		self.value.is_all_set()
	}

	/// Sets all bits of this `Int` to zero (`0`).
	pub fn unset_all(&mut self) {
		self.value.unset_all()
	}

	/// Returns `true` if all bits in this `Int` are unset.
	pub fn is_all_unset(&self) -> bool {
		self.value.is_all_unset()
	}

	/// Flips all bits of this `Int`.
	pub fn flip_all(&mut self) {
		self.value.flip_all()
	}

	/// Returns the sign bit of this `Int`.
	/// 
	/// **Note:** This is equal to the most significant bit of this `Int`.
	pub fn sign_bit(&self) -> Bit {
		self.value.sign_bit()
	}

	/// Sets the sign bit of this `Int` to one (`1`).
	pub fn set_sign_bit(&mut self) {
		self.value.set_sign_bit()
	}

	/// Sets the sign bit of this `Int` to zero (`0`).
	pub fn unset_sign_bit(&mut self) {
		self.value.unset_sign_bit()
	}

	/// Flips the sign bit of this `Int`.
	/// 
	/// # Note
	/// 
	/// - If the sign bit was `0` it will be `1` after this operation and vice versa.
	/// - Depending on the interpretation of the `Int` this
	///   operation changes its signedness.
	pub fn flip_sign_bit(&mut self) {
		self.value.flip_sign_bit()
	}
}

/// # Bitwise utility methods.
impl Int {
	/// Returns the number of ones in the binary representation of this `Int`.
	pub fn count_ones(&self) -> usize {
		self.value.count_ones()
	}

	/// Returns the number of zeros in the binary representation of this `Int`.
	pub fn count_zeros(&self) -> usize {
		self.value.count_zeros()
	}

	/// Returns the number of leading zeros in the binary representation of this `Int`.
	pub fn leading_zeros(&self) -> usize {
		self.value.leading_zeros()
	}

	/// Returns the number of trailing zeros in the binary representation of this `Int`.
	pub fn trailing_zeros(&self) -> usize {
		self.value.trailing_zeros()
	}
}

//  ===========================================================================
//  `Not` (bitwise) impls
//  ===========================================================================

impl Not for Int {
	type Output = Int;

	fn not(self) -> Self::Output {
		forward_mut_impl(self, Int::bitnot)
	}
}

//  ===========================================================================
//  `BitAnd` impls
//  ===========================================================================

impl<'a> BitAnd<&'a Int> for Int {
    type Output = Int;

    fn bitand(self, rhs: &'a Int) -> Self::Output {
        self.into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a Int> for &'b Int {
    type Output = Int;

    fn bitand(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a Int> for &'b mut Int {
    type Output = Int;

    fn bitand(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitand(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitOr` impls
//  ===========================================================================

impl<'a> BitOr<&'a Int> for Int {
    type Output = Int;

    fn bitor(self, rhs: &'a Int) -> Self::Output {
        self.into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a Int> for &'b Int {
    type Output = Int;

    fn bitor(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a Int> for &'b mut Int {
    type Output = Int;

    fn bitor(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitXor` impls
//  ===========================================================================

impl<'a> BitXor<&'a Int> for Int {
    type Output = Int;

    fn bitxor(self, rhs: &'a Int) -> Self::Output {
        self.into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a Int> for &'b Int {
    type Output = Int;

    fn bitxor(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a Int> for &'b mut Int {
    type Output = Int;

    fn bitxor(self, rhs: &'a Int) -> Self::Output {
        self.clone().into_checked_bitxor(rhs).unwrap()
    }
}

//  ===========================================================================
//  `BitAndAssign`, `BitOrAssign` and `BitXorAssign` impls
//  ===========================================================================

impl<'a> BitAndAssign<&'a Int> for Int {
    fn bitand_assign(&mut self, rhs: &'a Int) {
        self.checked_bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a Int> for Int {
    fn bitor_assign(&mut self, rhs: &'a Int) {
        self.checked_bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a Int> for Int {
    fn bitxor_assign(&mut self, rhs: &'a Int) {
        self.checked_bitxor_assign(rhs).unwrap();
    }
}

/// # Arithmetic Operations
impl Int {
	/// Negates this `Int` inplace and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn into_negate(self) -> Int {
		forward_mut_impl(self, Int::negate)
	}

	/// Negates this `Int` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	pub fn negate(&mut self) {
		self.value.negate()
	}

	/// Adds `rhs` to `self` and returns the result.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn into_checked_add(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_add_assign)
	}

	/// Add-assigns `rhs` to `self` inplace.
	/// 
	/// **Note:** This will **not** allocate memory.
	/// 
	/// # Errors
	/// 
	/// - If `self` and `rhs` have unmatching bit widths.
	pub fn checked_add_assign(&mut self, rhs: &Int) -> Result<()> {
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
	pub fn into_checked_sub(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_sub_assign)
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
	pub fn checked_sub_assign(&mut self, rhs: &Int) -> Result<()> {
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
	pub fn into_checked_mul(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_mul_assign)
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
	pub fn checked_mul_assign(&mut self, rhs: &Int) -> Result<()> {
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
	pub fn into_checked_div(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_div_assign)
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
	pub fn checked_div_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.checked_sdiv_assign(&rhs.value)
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
	pub fn into_checked_rem(self, rhs: &Int) -> Result<Int> {
		try_forward_bin_mut_impl(self, rhs, Int::checked_rem_assign)
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
	pub fn checked_rem_assign(&mut self, rhs: &Int) -> Result<()> {
		self.value.checked_srem_assign(&rhs.value)
	}
}

// ============================================================================
//  Unary arithmetic negation: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl Neg for Int {
	type Output = Int;

	fn neg(self) -> Self::Output {
		self.into_negate()
	}
}

impl<'a> Neg for &'a Int {
	type Output = Int;

	fn neg(self) -> Self::Output {
		self.clone().into_negate()
	}
}

impl<'a> Neg for &'a mut Int {
	type Output = &'a mut Int;

	fn neg(self) -> Self::Output {
		self.negate();
		self
	}
}

// ============================================================================
//  Add and Add-Assign: `std::ops::Add` and `std::ops::AddAssign`
// ============================================================================

impl<'a> Add<&'a Int> for Int {
	type Output = Int;

	fn add(self, rhs: &'a Int) -> Self::Output {
		self.into_checked_add(rhs).unwrap()
	}
}

impl<'a, 'b> Add<&'a Int> for &'b Int {
	type Output = Int;

	fn add(self, rhs: &'a Int) -> Self::Output {
		self.clone().into_checked_add(rhs).unwrap()
	}
}

impl<'a> AddAssign<&'a Int> for Int {
	fn add_assign(&mut self, rhs: &'a Int) {
		self.checked_add_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Sub and Sub-Assign: `std::ops::Sub` and `std::ops::SubAssign`
// ============================================================================

impl<'a> Sub<&'a Int> for Int {
	type Output = Int;

	fn sub(self, rhs: &'a Int) -> Self::Output {
		self.into_checked_sub(rhs).unwrap()
	}
}

impl<'a, 'b> Sub<&'a Int> for &'b Int {
	type Output = Int;

	fn sub(self, rhs: &'a Int) -> Self::Output {
		self.clone().into_checked_sub(rhs).unwrap()
	}
}

impl<'a> SubAssign<&'a Int> for Int {
	fn sub_assign(&mut self, rhs: &'a Int) {
		self.checked_sub_assign(rhs).unwrap()
	}
}

// ============================================================================
//  Mul and Mul-Assign: `std::ops::Mul` and `std::ops::MulAssign`
// ============================================================================

impl<'a> Mul<&'a Int> for Int {
	type Output = Int;

	fn mul(self, rhs: &'a Int) -> Self::Output {
		self.into_checked_mul(rhs).unwrap()
	}
}

impl<'a, 'b> Mul<&'a Int> for &'b Int {
	type Output = Int;

	fn mul(self, rhs: &'a Int) -> Self::Output {
		self.clone().into_checked_mul(rhs).unwrap()
	}
}

impl<'a> MulAssign<&'a Int> for Int {
	fn mul_assign(&mut self, rhs: &'a Int) {
		self.checked_mul_assign(rhs).unwrap();
	}
}

// ============================================================================
//  Div and Div-Assign: `std::ops::Div` and `std::ops::DivAssign`
// ============================================================================

impl<'a> Div<&'a Int> for Int {
	type Output = Int;

	fn div(self, rhs: &'a Int) -> Self::Output {
		self.into_checked_div(rhs).unwrap()
	}
}

impl<'a, 'b> Div<&'a Int> for &'b Int {
	type Output = Int;

	fn div(self, rhs: &'a Int) -> Self::Output {
		self.clone().into_checked_div(rhs).unwrap()
	}
}

impl<'a> DivAssign<&'a Int> for Int {
	fn div_assign(&mut self, rhs: &'a Int) {
		self.checked_div_assign(rhs).unwrap();
	}
}

// ============================================================================
//  Rem and Rem-Assign: `std::ops::Rem` and `std::ops::RemAssign`
// ============================================================================

impl<'a> Rem<&'a Int> for Int {
	type Output = Int;

	fn rem(self, rhs: &'a Int) -> Self::Output {
		self.into_checked_rem(rhs).unwrap()
	}
}

impl<'a, 'b> Rem<&'a Int> for &'b Int {
	type Output = Int;

	fn rem(self, rhs: &'a Int) -> Self::Output {
		self.clone().into_checked_rem(rhs).unwrap()
	}
}

impl<'a> RemAssign<&'a Int> for Int {
	fn rem_assign(&mut self, rhs: &'a Int) {
		self.checked_rem_assign(rhs).unwrap();
	}
}
