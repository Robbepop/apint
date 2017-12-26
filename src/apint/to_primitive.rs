use apint::{ApInt};
use digit;
use digit::{Digit};
use bitwidth::{BitWidth};
use errors::{Result, Error};
use traits::{Width};

/// Represents a primitive data type.
/// 
/// Used by the `to_primitive` module for an improved
/// error reporting.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
	U128
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
			Bool      => (value == 0) || (value == 1),
			I8  | U8  => value < (0x1 << 8),
			I16 | U16 => value < (0x1 << 16),
			I32 | U32 => value < (0x1 << 32),
			I64 | U64 | I128 | U128 => {
				true
			}
		}
	}

    /// Returns `true` if this `PrimitiveTy` can represent signedness.
    #[inline]
    pub(crate) fn is_signed(self) -> bool {
		use self::PrimitiveTy::*;
        match self {
            I8   |
            I16  |
            I32  |
            I64  |
            I128 => true,
            _    => false
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

//  =======================================================================
///  Operations to lossful cast to primitive number types.
/// =======================================================================
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
        let (mut lsd, _) = self.split_least_significant_digit();
        let target_width = prim_ty.associated_width();
        if prim_ty.is_signed() {
            let actual_width = self.width();
            if actual_width < target_width {
                lsd.sign_extend_from(actual_width)
                   .expect("We already asserted that `actual_width` < `target_width` \
                            and since `target_width` is always less than or equal to \
                            `64` bits calling `Digit::sign_extend_from` is safe for it.");
            }
        }
        lsd.truncate_to(target_width)
            .expect("Since `target_width` is always less than or equal to \
                    `64` bits calling `Digit::sign_extend_from` is safe for it.");
        lsd
    }

    /// Truncates this `ApInt` to a `bool` primitive type.
    /// 
    /// Bits in this `ApInt` that are not within the bounds
    /// of the `bool` are being ignored.
    /// 
    /// # Note
    /// 
    /// - Basically this returns `true` if the least significant
    ///   bit of this `ApInt` is `1` and `false` otherwise.
    pub fn resize_to_bool(&self) -> bool {
        match self.resize_to_primitive_ty(PrimitiveTy::Bool) {
            Digit(0) => false,
            Digit(1) => true,
            _ => unreachable!()
        }
    }

    /// Truncates this `ApInt` to a `i8` primitive type.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `8` bits the value is
    ///   sign extended to the target bit width.
    /// - All bits but the least significant `8` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i8(&self) -> i8 {
        self.resize_to_primitive_ty(PrimitiveTy::I8).repr() as i8
    }

    /// Truncates this `ApInt` to a `u8` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `8` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u8(&self) -> u8 {
        self.resize_to_primitive_ty(PrimitiveTy::U8).repr() as u8
    }

    /// Truncates this `ApInt` to a `i16` primitive type.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `16` bits the value is
    ///   sign extended to the target bit width.
    /// - All bits but the least significant `16` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i16(&self) -> i16 {
        self.resize_to_primitive_ty(PrimitiveTy::I16).repr() as i16
    }

    /// Truncates this `ApInt` to a `u16` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `16` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u16(&self) -> u16 {
        self.resize_to_primitive_ty(PrimitiveTy::U16).repr() as u16
    }

    /// Truncates this `ApInt` to a `i32` primitive type.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `32` bits the value is
    ///   sign extended to the target bit width.
    /// - All bits but the least significant `32` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i32(&self) -> i32 {
        self.resize_to_primitive_ty(PrimitiveTy::I32).repr() as i32
    }

    /// Truncates this `ApInt` to a `u32` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `32` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u32(&self) -> u32 {
        self.resize_to_primitive_ty(PrimitiveTy::U32).repr() as u32
    }

    /// Truncates this `ApInt` to a `i64` primitive type.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `64` bits the value is
    ///   sign extended to the target bit width.
    /// - All bits but the least significant `64` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i64(&self) -> i64 {
        self.resize_to_primitive_ty(PrimitiveTy::I64).repr() as i64
    }

    /// Truncates this `ApInt` to a `u64` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `64` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u64(&self) -> u64 {
        self.resize_to_primitive_ty(PrimitiveTy::U64).repr() as u64
    }

    /// Truncates this `ApInt` to a `i128` primitive type.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `128` bits the value is
    ///   sign extended to the target bit width.
    /// - All bits but the least significant `128` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_i128(&self) -> i128 {
        self.resize_to_u128() as i128
    }

    /// Truncates this `ApInt` to a `u128` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `128` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u128(&self) -> u128 {
        unimplemented!()
    }
}

//  =======================================================================
///  Operations to lossless cast to primitive number types.
/// =======================================================================
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
    /// `i32` is extended to an `i64` and correctly preserves the negative value.
    /// 
    /// # Errors
    /// 
    /// If it is not possible to cast this `ApInt` without loss of information.
    fn try_cast_to_primitive_ty(&self, prim_ty: PrimitiveTy) -> Result<Digit> {
        debug_assert_ne!(prim_ty, PrimitiveTy::U128);
        debug_assert_ne!(prim_ty, PrimitiveTy::I128);
        let (mut lsd, rest) = self.split_least_significant_digit();
        if !prim_ty.is_valid_repr(lsd.repr())
           || rest.into_iter().any(|d| d.repr() != 0)
        {
            return Error::encountered_unrepresentable_value(
                self.clone(), prim_ty).into()
        }
        if prim_ty.is_signed() {
            let actual_width = self.width();
            let target_width = prim_ty.associated_width();
            if actual_width < target_width {
                lsd.sign_extend_from(actual_width)
                   .expect("We already asserted that `actual_width` < `target_width` \
                            and since `target_width` is always less than or equal to \
                            `64` bits calling `Digit::sign_extend_from` is safe for it.");
                lsd.truncate_to(target_width)
                   .expect("Since `target_width` is always less than or equal to \
                            `64` bits calling `Digit::sign_extend_from` is safe for it.");
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
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `bool`.
    pub fn try_to_bool(&self) -> Result<bool> {
        match self.try_cast_to_primitive_ty(PrimitiveTy::Bool)? {
            Digit(0) => Ok(false),
            Digit(1) => Ok(true),
           _ => unreachable!()
        }
    }

    /// Tries to represent the value of this `ApInt` as a `i8`.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `8` bits the value is
    ///   sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u8`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i8`.
    pub fn try_to_i8(&self) -> Result<i8> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I8).map(|d| d.repr() as i8)
    }

    /// Tries to represent the value of this `ApInt` as a `u8`.
    /// 
    /// # Note
    /// 
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u8`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u8`.
    pub fn try_to_u8(&self) -> Result<u8> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U8).map(|d| d.repr() as u8)
    }

    /// Tries to represent the value of this `ApInt` as a `i16`.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `16` bits the value is
    ///   sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u16`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i16`.
    pub fn try_to_i16(&self) -> Result<i16> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I16).map(|d| d.repr() as i16)
    }

    /// Tries to represent the value of this `ApInt` as a `u16`.
    /// 
    /// # Note
    /// 
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u16`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u16`.
    pub fn try_to_u16(&self) -> Result<u16> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U16).map(|d| d.repr() as u16)
    }

    /// Tries to represent the value of this `ApInt` as a `i32`.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `32` bits the value is
    ///   sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u32`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i32`.
    pub fn try_to_i32(&self) -> Result<i32> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I32).map(|d| d.repr() as i32)
    }

    /// Tries to represent the value of this `ApInt` as a `u32`.
    /// 
    /// # Note
    /// 
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u32`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u32`.
    pub fn try_to_u32(&self) -> Result<u32> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U32).map(|d| d.repr() as u32)
    }

    /// Tries to represent the value of this `ApInt` as a `i64`.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `64` bits the value is
    ///   sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u64`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i64`.
    pub fn try_to_i64(&self) -> Result<i64> {
        self.try_cast_to_primitive_ty(PrimitiveTy::I64).map(|d| d.repr() as i64)
    }

    /// Tries to represent the value of this `ApInt` as a `u64`.
    /// 
    /// # Note
    /// 
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u64`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u64`.
    pub fn try_to_u64(&self) -> Result<u64> {
        self.try_cast_to_primitive_ty(PrimitiveTy::U64).map(|d| d.repr() as u64)
    }

    /// Tries to represent the value of this `ApInt` as a `i128`.
    /// 
    /// # Note
    /// 
    /// - This operation will conserve the signedness of the
    ///   value. This means that for `ApInt` instances with
    ///   a `BitWidth` less than `128` bits the value is
    ///   sign extended to the target bit width.
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u128`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i128`.
    pub fn try_to_i128(&self) -> Result<i128> {
        let ( lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, rest) = rest.split_first().unwrap_or((&Digit(0), &[]));
        if rest.into_iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I128).into()
        }
        let mut result: i128 =
            (i128::from(lsd_1.repr()) << digit::BITS) + i128::from(lsd_0.repr());

        let actual_width = self.width();
        let target_width = BitWidth::w128();
        if actual_width < target_width {
            // Sign extend the `i128`. Fill up with `1` up to `128` bits 
            // starting from the sign bit position.
            let b = actual_width.to_usize(); // Number of bits representing the number in x.
            let m: i128 = 1 << (b - 1);      // Mask can be pre-computed if b is fixed.
            result = (result ^ m) - m;       // Resulting sign-extended number.
        }

        Ok(result)
    }

    /// Tries to represent the value of this `ApInt` as a `u128`.
    /// 
    /// # Note
    /// 
    /// - This conversion is possible as long as the value represented
    ///   by this `ApInt` does not exceed the maximum value of `u128`.
    /// 
    /// # Complexity
    /// 
    /// - 𝒪(n) where n is the number of digits of this `ApInt`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u128`.
    pub fn try_to_u128(&self) -> Result<u128> {
        let ( lsd_0, rest) = self.split_least_significant_digit();
        let (&lsd_1, rest) = rest.split_first().unwrap_or((&Digit(0), &[]));
        if rest.into_iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::U128).into()
        }
        let result: u128 =
            (u128::from(lsd_1.repr()) << digit::BITS) + u128::from(lsd_0.repr());
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod try {
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
            assert!(ApInt::from(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_u128)
                .try_to_bool()
                .is_err()
            );
        }
    }
}
