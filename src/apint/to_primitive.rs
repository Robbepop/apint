use crate::{
    apint::ApInt,
    bitwidth::BitWidth,
    errors::{
        Error,
        Result,
    },
    Width,
    Digit,
};

/// Represents a primitive data type.
///
/// Used by the `to_primitive` module for an improved
/// error reporting.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    /// Represents Rust's `bool`.
    Bool,
    /// Represents Rust's `i8`.
    I8,
    /// Represents Rust's `u8`.
    U8,
    /// Represents Rust's `i16`.
    I16,
    /// Represents Rust's `u16`.
    U16,
    /// Represents Rust's `i32`.
    I32,
    /// Represents Rust's `u32`.
    U32,
    /// Represents Rust's `i64`.
    I64,
    /// Represents Rust's `u64`.
    U64,
    /// Represents Rust's `i128`.
    I128,
    /// Represents Rust's `u128`.
    U128,
}

impl PrimitiveTy {
    /// Returns `true` if the given `value` is a valid representation
    /// for this `PrimitiveTy`.
    ///
    /// # Example
    ///
    /// If this `PrimitiveTy` was `U8` then `200` is a valid representation
    /// but `256` is not since it is not representable by `8` bits. Only
    /// unsigned values are considered in this regard.
    #[inline]
    pub(crate) fn is_valid_repr(self, value: u64) -> bool {
        use self::PrimitiveTy::*;
        match self {
            Bool => (value == 0) || (value == 1),
            I8 | U8 => value < (0x1 << 8),
            I16 | U16 => value < (0x1 << 16),
            I32 | U32 => value < (0x1 << 32),
            I64 | U64 | I128 | U128 => true,
        }
    }

    /// Returns `true` if the given `value` is a valid double-digit
    /// representation for this `PrimitiveTy`.
    ///
    /// # Example
    ///
    /// If this `PrimitiveTy` was `U8` then `200` is a valid representation
    /// but `256` is not since it is not representable by `8` bits. Only
    /// unsigned values are considered in this regard.
    ///
    /// # Note
    ///
    /// This functionality is currently only used by local unit tests.
    #[inline]
    #[cfg(test)]
    pub(crate) fn is_valid_dd(self, value: u128) -> bool {
        use self::PrimitiveTy::*;
        match self {
            Bool => (value == 0) || (value == 1),
            I8 | U8 => value < (0x1 << 8),
            I16 | U16 => value < (0x1 << 16),
            I32 | U32 => value < (0x1 << 32),
            I64 | U64 => value < (0x1 << 64),
            I128 | U128 => true,
        }
    }

    /// Returns `true` if this `PrimitiveTy` can represent signedness.
    #[inline]
    pub(crate) fn is_signed(self) -> bool {
        use self::PrimitiveTy::*;
        match self {
            I8 | I16 | I32 | I64 | I128 => true,
            _ => false,
        }
    }

    /// Returns the associated `BitWidth` to this `PrimitiveTy`.
    ///
    /// # Example
    ///
    /// For `i32` the associated `BitWidth` is `32 bits` and for
    /// `u64` it is `64 bits`.
    #[inline]
    pub(crate) fn associated_width(self) -> BitWidth {
        use self::PrimitiveTy::*;
        match self {
            Bool => BitWidth::w1(),
            I8 | U8 => BitWidth::w8(),
            I16 | U16 => BitWidth::w16(),
            I32 | U32 => BitWidth::w32(),
            I64 | U64 => BitWidth::w64(),
            I128 | U128 => BitWidth::w128(),
        }
    }
}

/// # Operations to lossful cast to primitive number types.
impl ApInt {
    /// Resizes the given `ApInt` to the given `PrimitiveTy`.
    ///
    /// This will truncate the bits of the `ApInt` if it has a greater bit
    /// width than the target bit width or will sign-extend the bits of the
    /// `ApInt` if its bit width is less than the target bit width.
    ///
    /// This operation cannot fail and is the generic foundation for the
    /// greater part of the `ApInt::resize_to_*` methods.
    fn resize_to_primitive_ty(&self, prim_ty: PrimitiveTy) -> Digit {
        debug_assert_ne!(prim_ty, PrimitiveTy::U128);
        debug_assert_ne!(prim_ty, PrimitiveTy::I128);
        let mut lsd = self.least_significant_digit();
        let actual_width = self.width();
        let target_width = prim_ty.associated_width();
        if prim_ty.is_signed() && actual_width < target_width {
            lsd.sign_extend_from(actual_width).expect(
                "We already asserted that `actual_width` < `target_width` and since \
                 `target_width` is always less than or equal to `64` bits calling \
                 `Digit::sign_extend_from` is safe for it.",
            );
        }
        if target_width < BitWidth::w64() {
            lsd.truncate_to(target_width).expect(
                "Since `target_width` is always less than or equal to `64` bits calling \
                 `Digit::sign_extend_from` is safe for it.",
            );
        }
        lsd
    }

    /// Resizes this `ApInt` to a `bool` primitive type.
    ///
    /// Bits in this `ApInt` that are not within the bounds
    /// of the `bool` are being ignored.
    ///
    /// # Note
    ///
    /// - Basically this returns `true` if the least significant bit of this
    ///   `ApInt` is `1` and `false` otherwise.
    pub fn resize_to_bool(&self) -> bool {
        match self.resize_to_primitive_ty(PrimitiveTy::Bool) {
            Digit(0) => false,
            Digit(1) => true,
            _ => unreachable!(),
        }
    }

    /// Resizes this `ApInt` to a `i8` primitive type.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `8` bits the
    ///   value is sign extended to the target bit width.
    /// - All bits but the least significant `8` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_i8(&self) -> i8 {
        self.resize_to_primitive_ty(PrimitiveTy::I8).repr() as i8
    }

    /// Resizes this `ApInt` to a `u8` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `8` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u8(&self) -> u8 {
        self.resize_to_primitive_ty(PrimitiveTy::U8).repr() as u8
    }

    /// Resizes this `ApInt` to a `i16` primitive type.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `16` bits the
    ///   value is sign extended to the target bit width.
    /// - All bits but the least significant `16` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_i16(&self) -> i16 {
        self.resize_to_primitive_ty(PrimitiveTy::I16).repr() as i16
    }

    /// Resizes this `ApInt` to a `u16` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `16` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u16(&self) -> u16 {
        self.resize_to_primitive_ty(PrimitiveTy::U16).repr() as u16
    }

    /// Resizes this `ApInt` to a `i32` primitive type.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `32` bits the
    ///   value is sign extended to the target bit width.
    /// - All bits but the least significant `32` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_i32(&self) -> i32 {
        self.resize_to_primitive_ty(PrimitiveTy::I32).repr() as i32
    }

    /// Resizes this `ApInt` to a `u32` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `32` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u32(&self) -> u32 {
        self.resize_to_primitive_ty(PrimitiveTy::U32).repr() as u32
    }

    /// Resizes this `ApInt` to a `i64` primitive type.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `64` bits the
    ///   value is sign extended to the target bit width.
    /// - All bits but the least significant `64` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_i64(&self) -> i64 {
        self.resize_to_primitive_ty(PrimitiveTy::I64).repr() as i64
    }

    /// Resizes this `ApInt` to a `u64` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `64` bits are being ignored by this
    ///   operation to construct the result.
    pub fn resize_to_u64(&self) -> u64 {
        self.resize_to_primitive_ty(PrimitiveTy::U64).repr() as u64
    }

    /// Resizes this `ApInt` to a `i128` primitive type.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `128` bits the
    ///   value is sign extended to the target bit width.
    /// - All bits but the least significant `128` bits are being ignored by
    ///   this operation to construct the result.
    pub fn resize_to_i128(&self) -> i128 {
        let (lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, _) = rest.split_first().unwrap_or((&Digit(0), &[]));
        let mut result: i128 =
            (i128::from(lsd_1.repr()) << Digit::BITS) + i128::from(lsd_0.repr());
        let actual_width = self.width();
        let target_width = BitWidth::w128();

        if actual_width < target_width {
            // Sign extend the `i128`. Fill up with `1` up to `128` bits
            // starting from the sign bit position.

            // Number of bits representing the number in x.
            let b = actual_width.to_usize();
            // Mask can be pre-computed if b is fixed.
            let m: i128 = 1 << (b - 1);
            // Resulting sign-extended number.
            result = (result ^ m) - m;
        }

        result
    }

    /// Resizes this `ApInt` to a `u128` primitive type.
    ///
    /// # Note
    ///
    /// - All bits but the least significant `128` bits are being ignored by
    ///   this operation to construct the result.
    pub fn resize_to_u128(&self) -> u128 {
        let (lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, _) = rest.split_first().unwrap_or((&Digit(0), &[]));
        let result: u128 =
            (u128::from(lsd_1.repr()) << Digit::BITS) + u128::from(lsd_0.repr());
        result
    }
}

/// # Operations to lossless cast to primitive number types.
impl ApInt {
    /// Verifies if this `ApInt` can be casted into the given primitive type
    /// without loss of information and returns the least significant `Digit`
    /// of this `ApInt` upon success.
    ///
    /// # Note
    ///
    /// If the given `PrimitiveTy` represents a signed integer type the
    /// returned `Digit` is also sign extended accordingly.
    /// This sign extension behaves equal to how in Rust a negative signed
    /// `i32` is extended to an `i64` and correctly preserves the negative
    /// value.
    ///
    /// # Errors
    ///
    /// If it is not possible to cast this `ApInt` without loss of information.
    fn try_cast_to_primitive_ty(&self, prim_ty: PrimitiveTy) -> Result<Digit> {
        debug_assert_ne!(prim_ty, PrimitiveTy::U128);
        debug_assert_ne!(prim_ty, PrimitiveTy::I128);
        let (mut lsd, rest) = self.split_least_significant_digit();
        if !prim_ty.is_valid_repr(lsd.repr()) || rest.iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(self.clone(), prim_ty).into()
        }
        if prim_ty.is_signed() {
            let actual_width = self.width();
            let target_width = prim_ty.associated_width();
            if actual_width < target_width {
                lsd.sign_extend_from(actual_width).expect(
                    "We already asserted that `actual_width` < `target_width` and since \
                     `target_width` is always less than or equal to `64` bits calling \
                     `Digit::sign_extend_from` is safe for it.",
                );
                if target_width < BitWidth::w64() {
                    lsd.truncate_to(target_width).expect(
                        "Since `target_width` is always less than or equal to `64` bits \
                         calling `Digit::sign_extend_from` is safe for it.",
                    );
                }
            }
        }
        Ok(lsd)
    }

    /// Tries to represent the value of this `ApInt` as a `bool`.
    ///
    /// # Note
    ///
    /// This returns `true` if the value represented by this `ApInt`
    /// is `1`, returns `false` if the value represented by this
    /// `ApInt` is `0` and returns an error otherwise.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `bool`.
    pub fn try_to_bool(&self) -> Result<bool> {
        match self.try_cast_to_primitive_ty(PrimitiveTy::Bool)? {
            Digit(0) => Ok(false),
            Digit(1) => Ok(true),
            _ => unreachable!(),
        }
    }

    /// Tries to represent the value of this `ApInt` as a `i8`.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `8` bits the
    ///   value is sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u8`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `i8`.
    pub fn try_to_i8(&self) -> Result<i8> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I8)
            .map(|d| d.repr() as i8)
    }

    /// Tries to represent the value of this `ApInt` as a `u8`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u8`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `u8`.
    pub fn try_to_u8(&self) -> Result<u8> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U8)
            .map(|d| d.repr() as u8)
    }

    /// Tries to represent the value of this `ApInt` as a `i16`.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `16` bits the
    ///   value is sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u16`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `i16`.
    pub fn try_to_i16(&self) -> Result<i16> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I16)
            .map(|d| d.repr() as i16)
    }

    /// Tries to represent the value of this `ApInt` as a `u16`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u16`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `u16`.
    pub fn try_to_u16(&self) -> Result<u16> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U16)
            .map(|d| d.repr() as u16)
    }

    /// Tries to represent the value of this `ApInt` as a `i32`.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `32` bits the
    ///   value is sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u32`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `i32`.
    pub fn try_to_i32(&self) -> Result<i32> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I32)
            .map(|d| d.repr() as i32)
    }

    /// Tries to represent the value of this `ApInt` as a `u32`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u32`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `u32`.
    pub fn try_to_u32(&self) -> Result<u32> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U32)
            .map(|d| d.repr() as u32)
    }

    /// Tries to represent the value of this `ApInt` as a `i64`.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `64` bits the
    ///   value is sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u64`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `i64`.
    pub fn try_to_i64(&self) -> Result<i64> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I64)
            .map(|d| d.repr() as i64)
    }

    /// Tries to represent the value of this `ApInt` as a `u64`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u64`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `u64`.
    pub fn try_to_u64(&self) -> Result<u64> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U64)
            .map(|d| d.repr() as u64)
    }

    /// Tries to represent the value of this `ApInt` as a `i128`.
    ///
    /// # Note
    ///
    /// - This operation will conserve the signedness of the value. This means
    ///   that for `ApInt` instances with a `BitWidth` less than `128` bits the
    ///   value is sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u128`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `i128`.
    pub fn try_to_i128(&self) -> Result<i128> {
        let (lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, rest) = rest.split_first().unwrap_or((&Digit(0), &[]));
        if rest.iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(),
                PrimitiveTy::I128,
            )
            .into()
        }
        let mut result: i128 =
            (i128::from(lsd_1.repr()) << Digit::BITS) + i128::from(lsd_0.repr());

        let actual_width = self.width();
        let target_width = BitWidth::w128();
        if actual_width < target_width {
            // Sign extend the `i128`. Fill up with `1` up to `128` bits
            // starting from the sign bit position.

            // Number of bits representing the number in x.
            let b = actual_width.to_usize();
            // Mask can be pre-computed if b is fixed.
            let m: i128 = 1 << (b - 1);
            // Resulting sign-extended number.
            result = (result ^ m).wrapping_sub(m);
        }

        Ok(result)
    }

    /// Tries to represent the value of this `ApInt` as a `u128`.
    ///
    /// # Note
    ///
    /// - This conversion is possible as long as the value represented by this
    ///   `ApInt` does not exceed the maximum value of `u128`.
    ///
    /// # Complexity
    ///
    /// - 𝒪(n) where n is the number of digits of this `ApInt`.
    ///
    /// # Errors
    ///
    /// - If the value represented by this `ApInt` can not be represented by a
    ///   `u128`.
    pub fn try_to_u128(&self) -> Result<u128> {
        let (lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, rest) = rest.split_first().unwrap_or((&Digit(0), &[]));
        if rest.iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(),
                PrimitiveTy::U128,
            )
            .into()
        }
        let result: u128 =
            (u128::from(lsd_1.repr()) << Digit::BITS) + u128::from(lsd_0.repr());
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use itertools::Itertools;

    /// Returns a bunch of interesting test values for the
    /// `to_primitive` method tests.
    fn unsigned_test_values() -> impl Iterator<Item = i64> {
        vec![
            0_u64,
            1,
            2,
            3,
            5,
            7,
            10,
            11,
            13,
            42,
            63,
            64,
            65,
            100,
            127,
            128,
            129,
            254,
            255,
            256,
            257,
            1337,
            2047,
            2048,
            2049,
            8001,
            9999,
            0xFEDC_BA98_7654_3210,
            0xF0F0_F0F0_F0F0_F0F0,
            0x8000_0000_0000_0000,
            0x1010_1010_1010_1010,
            0xFFFF_FFFF_0000_0000,
            0x0000_FFFF_FFFF_0000,
            0xFFFF_0000_0000_FFFF,
            0xFFFF_0000_FFFF_0000,
            0x0000_FFFF_0000_FFFF,
        ]
        .into_iter()
        .map(|v| v as i64)
    }

    /// Returns negated mirror values of `unsigned_test_values` thus doubeling
    /// the test values count.
    fn signed_test_values() -> impl Iterator<Item = i64> {
        unsigned_test_values().map(|v| v.wrapping_neg())
    }

    /// Unifies signed and unsigned test values into a single iterator.
    fn test_values() -> impl Iterator<Item = i64> {
        unsigned_test_values().chain(signed_test_values())
    }

    /// Which `PrimitiveTy` instances shall be tested. Basically we test all
    /// if no problems occure.
    fn test_primitive_tys() -> impl Iterator<Item = PrimitiveTy> + Clone {
        use self::PrimitiveTy::*;
        vec![Bool, I8, U8, I16, U16, I32, U32, I64, U64, I128, U128].into_iter()
    }

    /// Uses `test_values` to iterate over already constructed `ApInt`
    /// instances.
    fn test_vals_and_apints() -> impl Iterator<Item = (u128, ApInt)> {
        test_values()
            .cartesian_product(test_primitive_tys())
            .map(|(val, prim_ty)| {
                use self::PrimitiveTy::*;
                match prim_ty {
                    Bool => {
                        let val = val != 0;
                        (val as u128, ApInt::from_bit(val))
                    }
                    I8 => {
                        let val = val as i8;
                        (val as u8 as u128, ApInt::from_i8(val))
                    }
                    U8 => {
                        let val = val as u8;
                        (val as u128, ApInt::from_u8(val))
                    }
                    I16 => {
                        let val = val as i16;
                        (val as u16 as u128, ApInt::from_i16(val))
                    }
                    U16 => {
                        let val = val as u16;
                        (val as u128, ApInt::from_u16(val))
                    }
                    I32 => {
                        let val = val as i32;
                        (val as u32 as u128, ApInt::from_i32(val))
                    }
                    U32 => {
                        let val = val as u32;
                        (val as u128, ApInt::from_u32(val))
                    }
                    I64 => {
                        let val = val as i64;
                        (val as u64 as u128, ApInt::from_i64(val))
                    }
                    U64 => {
                        let val = val as u64;
                        (val as u128, ApInt::from_u64(val))
                    }
                    I128 => {
                        let val = val as i128;
                        (val as u128, ApInt::from_i128(val))
                    }
                    U128 => {
                        let val = val as u128;
                        (val, ApInt::from_u128(val))
                    }
                }
            })
    }

    mod resize {
        use super::*;

        #[test]
        fn count_test_apints() {
            assert_eq!(test_vals_and_apints().count(), 792);
        }

        #[test]
        fn to_bool_true() {
            assert_eq!(ApInt::from(true).resize_to_bool(), true);
            assert_eq!(ApInt::from(1_u8).resize_to_bool(), true);
            assert_eq!(ApInt::from(1_u16).resize_to_bool(), true);
            assert_eq!(ApInt::from(1_u32).resize_to_bool(), true);
            assert_eq!(ApInt::from(1_u64).resize_to_bool(), true);
            assert_eq!(ApInt::from(1_u128).resize_to_bool(), true);
        }

        #[test]
        fn to_bool_odd() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(val % 2 == 0, apint.is_even());
                assert_eq!(val % 2 != 0, apint.is_odd());
                assert_eq!(apint.resize_to_bool(), apint.is_odd())
            }
        }

        #[test]
        fn to_i8() {
            for (val, apint) in test_vals_and_apints() {
                let actual_width = apint.width();
                let target_width = PrimitiveTy::I8.associated_width();
                if actual_width < target_width {
                    let mut digit = Digit(val as u64);
                    digit.sign_extend_from(actual_width).unwrap();
                    digit.truncate_to(target_width).unwrap();
                    assert_eq!(apint.resize_to_i8(), digit.repr() as i8);
                } else {
                    assert_eq!(apint.resize_to_i8(), val as i8)
                }
            }
        }

        #[test]
        fn to_u8() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(apint.resize_to_u8(), val as u8)
            }
        }

        #[test]
        fn to_i16() {
            for (val, apint) in test_vals_and_apints() {
                let actual_width = apint.width();
                let target_width = PrimitiveTy::I16.associated_width();
                if actual_width < target_width {
                    let mut digit = Digit(val as u64);
                    digit.sign_extend_from(actual_width).unwrap();
                    digit.truncate_to(target_width).unwrap();
                    assert_eq!(apint.resize_to_i16(), digit.repr() as i16);
                } else {
                    assert_eq!(apint.resize_to_i16(), val as i16)
                }
            }
        }

        #[test]
        fn to_u16() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(apint.resize_to_u16(), val as u16)
            }
        }

        #[test]
        fn to_i32() {
            for (val, apint) in test_vals_and_apints() {
                let actual_width = apint.width();
                let target_width = PrimitiveTy::I32.associated_width();
                if actual_width < target_width {
                    let mut digit = Digit(val as u64);
                    digit.sign_extend_from(actual_width).unwrap();
                    digit.truncate_to(target_width).unwrap();
                    assert_eq!(apint.resize_to_i32(), digit.repr() as i32);
                } else {
                    assert_eq!(apint.resize_to_i32(), val as i32)
                }
            }
        }

        #[test]
        fn to_u32() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(apint.resize_to_u32(), val as u32)
            }
        }

        #[test]
        fn to_i64() {
            for (val, apint) in test_vals_and_apints() {
                let actual_width = apint.width();
                let target_width = PrimitiveTy::I64.associated_width();
                if actual_width < target_width {
                    let mut digit = Digit(val as u64);
                    digit.sign_extend_from(actual_width).unwrap();
                    assert_eq!(apint.resize_to_i64(), digit.repr() as i64);
                } else {
                    assert_eq!(apint.resize_to_i64(), val as i64)
                }
            }
        }

        #[test]
        fn to_u64() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(apint.resize_to_u64(), val as u64)
            }
        }

        #[test]
        fn to_i128() {
            for (val, apint) in test_vals_and_apints() {
                let actual_width = apint.width();
                let target_width = PrimitiveTy::I128.associated_width();
                if actual_width < target_width {
                    let mut digit = Digit(val as u64);
                    digit.sign_extend_from(actual_width).unwrap();
                    assert_eq!(apint.resize_to_i128(), digit.repr() as i64 as i128);
                } else {
                    assert_eq!(apint.resize_to_i128(), val as i128)
                }
            }
        }

        #[test]
        fn to_u128() {
            for (val, apint) in test_vals_and_apints() {
                assert_eq!(apint.resize_to_u128(), val)
            }
        }

        #[test]
        fn one_to_i8() {
            assert_eq!(ApInt::from(true).resize_to_i8(), -1);

            assert_eq!(ApInt::from(1_u8).resize_to_i8(), 1);
            assert_eq!(ApInt::from(1_u16).resize_to_i8(), 1);
            assert_eq!(ApInt::from(1_u32).resize_to_i8(), 1);
            assert_eq!(ApInt::from(1_u64).resize_to_i8(), 1);
            assert_eq!(ApInt::from(1_u128).resize_to_i8(), 1);

            assert_eq!(ApInt::from(-1_i8).resize_to_i8(), -1);
            assert_eq!(ApInt::from(-1_i16).resize_to_i8(), -1);
            assert_eq!(ApInt::from(-1_i32).resize_to_i8(), -1);
            assert_eq!(ApInt::from(-1_i64).resize_to_i8(), -1);
            assert_eq!(ApInt::from(-1_i128).resize_to_i8(), -1);
        }
    }

    mod r#try {
        use super::*;

        #[test]
        fn to_bool_true() {
            assert_eq!(ApInt::from(true).try_to_bool(), Ok(true));
            assert_eq!(ApInt::from(1_u8).try_to_bool(), Ok(true));
            assert_eq!(ApInt::from(1_u16).try_to_bool(), Ok(true));
            assert_eq!(ApInt::from(1_u32).try_to_bool(), Ok(true));
            assert_eq!(ApInt::from(1_u64).try_to_bool(), Ok(true));
            assert_eq!(ApInt::from(1_u128).try_to_bool(), Ok(true));
        }

        #[test]
        fn to_bool_false() {
            assert_eq!(ApInt::from(false).try_to_bool(), Ok(false));
            assert_eq!(ApInt::from(0_u8).try_to_bool(), Ok(false));
            assert_eq!(ApInt::from(0_u16).try_to_bool(), Ok(false));
            assert_eq!(ApInt::from(0_u32).try_to_bool(), Ok(false));
            assert_eq!(ApInt::from(0_u64).try_to_bool(), Ok(false));
            assert_eq!(ApInt::from(0_u128).try_to_bool(), Ok(false));
        }

        #[test]
        fn to_bool_fail() {
            assert!(ApInt::from(2_u8).try_to_bool().is_err());
            assert!(ApInt::from(-1_i16).try_to_bool().is_err());
            assert!(ApInt::from(42_u32).try_to_bool().is_err());
            assert!(ApInt::from(1337_u64).try_to_bool().is_err());
            assert!(
                ApInt::from(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_u128)
                    .try_to_bool()
                    .is_err()
            );
        }

        #[test]
        fn to_i8() {
            for (val, apint) in test_vals_and_apints() {
                if PrimitiveTy::I8.is_valid_dd(val) {
                    let actual_width = apint.width();
                    let target_width = PrimitiveTy::I8.associated_width();
                    if actual_width < target_width {
                        let mut digit = Digit(val as u64);
                        digit.sign_extend_from(actual_width).unwrap();
                        digit.truncate_to(target_width).unwrap();
                        assert_eq!(apint.try_to_i8(), Ok(digit.repr() as i8));
                    } else {
                        assert_eq!(apint.try_to_i8(), Ok(val as i8))
                    }
                } else {
                    assert!(apint.try_to_i8().is_err())
                }
            }
        }

        #[test]
        fn to_i16() {
            for (val, apint) in test_vals_and_apints() {
                if PrimitiveTy::I16.is_valid_dd(val) {
                    let actual_width = apint.width();
                    let target_width = PrimitiveTy::I16.associated_width();
                    if actual_width < target_width {
                        let mut digit = Digit(val as u64);
                        digit.sign_extend_from(actual_width).unwrap();
                        digit.truncate_to(target_width).unwrap();
                        assert_eq!(apint.try_to_i16(), Ok(digit.repr() as i16));
                    } else {
                        assert_eq!(apint.try_to_i16(), Ok(val as i16))
                    }
                } else {
                    assert!(apint.try_to_i16().is_err())
                }
            }
        }

        #[test]
        fn to_i32() {
            for (val, apint) in test_vals_and_apints() {
                if PrimitiveTy::I32.is_valid_dd(val) {
                    let actual_width = apint.width();
                    let target_width = PrimitiveTy::I32.associated_width();
                    if actual_width < target_width {
                        let mut digit = Digit(val as u64);
                        digit.sign_extend_from(actual_width).unwrap();
                        digit.truncate_to(target_width).unwrap();
                        assert_eq!(apint.try_to_i32(), Ok(digit.repr() as i32));
                    } else {
                        assert_eq!(apint.try_to_i32(), Ok(val as i32))
                    }
                } else {
                    assert!(apint.try_to_i32().is_err())
                }
            }
        }

        #[test]
        fn to_i64() {
            for (val, apint) in test_vals_and_apints() {
                if PrimitiveTy::I64.is_valid_dd(val) {
                    let actual_width = apint.width();
                    let target_width = PrimitiveTy::I64.associated_width();
                    if actual_width < target_width {
                        let mut digit = Digit(val as u64);
                        digit.sign_extend_from(actual_width).unwrap();
                        assert_eq!(apint.try_to_i64(), Ok(digit.repr() as i64));
                    } else {
                        assert_eq!(apint.try_to_i64(), Ok(val as i64))
                    }
                } else {
                    assert!(apint.try_to_i64().is_err())
                }
            }
        }

        #[test]
        fn to_i128() {
            for (val, apint) in test_vals_and_apints() {
                if PrimitiveTy::I128.is_valid_dd(val) {
                    let actual_width = apint.width();
                    let target_width = BitWidth::w128();
                    let mut result: i128 = val as i128;
                    if actual_width < target_width {
                        // Sign extend the `i128`. Fill up with `1` up to `128` bits
                        // starting from the sign bit position.

                        // Number of bits representing the number in x.
                        let b = actual_width.to_usize();
                        // Mask can be pre-computed if b is fixed.
                        let m: i128 = 1 << (b - 1);
                        // Resulting sign-extended number.
                        result = (result ^ m).wrapping_sub(m);
                    }
                    assert_eq!(apint.try_to_i128(), Ok(result))
                } else {
                    assert!(apint.try_to_i128().is_err())
                }
            }
        }

        #[test]
        fn to_u8() {
            for (val, apint) in test_vals_and_apints() {
                let result = apint.try_to_u8();
                if PrimitiveTy::U8.is_valid_dd(val) {
                    assert_eq!(result, Ok(val as u8))
                } else {
                    assert!(result.is_err())
                }
            }
        }

        #[test]
        fn to_u16() {
            for (val, apint) in test_vals_and_apints() {
                let result = apint.try_to_u16();
                if PrimitiveTy::U16.is_valid_dd(val) {
                    assert_eq!(result, Ok(val as u16))
                } else {
                    assert!(result.is_err())
                }
            }
        }

        #[test]
        fn to_u32() {
            for (val, apint) in test_vals_and_apints() {
                let result = apint.try_to_u32();
                if PrimitiveTy::U32.is_valid_dd(val) {
                    assert_eq!(result, Ok(val as u32))
                } else {
                    assert!(result.is_err())
                }
            }
        }

        #[test]
        fn to_u64() {
            for (val, apint) in test_vals_and_apints() {
                let result = apint.try_to_u64();
                if PrimitiveTy::U64.is_valid_dd(val) {
                    assert_eq!(result, Ok(val as u64))
                } else {
                    assert!(result.is_err())
                }
            }
        }

        #[test]
        fn to_u128() {
            for (val, apint) in test_vals_and_apints() {
                let result = apint.try_to_u128();
                if PrimitiveTy::U128.is_valid_dd(val) {
                    assert_eq!(result, Ok(val as u128))
                } else {
                    assert!(result.is_err())
                }
            }
        }
    }
}
