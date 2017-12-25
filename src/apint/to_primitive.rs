use apint::{ApInt};
use digit;
use digit::{Digit, DigitRepr};
use bitwidth::{BitWidth};
use errors::{Result, Error};

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
        unimplemented!()
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
        self.resize_to_u8() as i8
    }

    /// Truncates this `ApInt` to a `u8` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `8` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u8(&self) -> u8 {
        unimplemented!()
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
        self.resize_to_u16() as i16
    }

    /// Truncates this `ApInt` to a `u16` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `16` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u16(&self) -> u16 {
        unimplemented!()
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
        self.resize_to_u32() as i32
    }

    /// Truncates this `ApInt` to a `u32` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `32` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u32(&self) -> u32 {
        unimplemented!()
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
        self.resize_to_u64() as i64
    }

    /// Truncates this `ApInt` to a `u64` primitive type.
    /// 
    /// # Note
    /// 
    /// - All bits but the least significant `64` bits are
    ///   being ignored by this operation to construct the
    ///   result.
    pub fn resize_to_u64(&self) -> u64 {
        unimplemented!()
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
        let (lsd, rest) = self.split_least_significant_digit();
        if lsd.repr() > 1 || rest.into_iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::Bool).into()
        }
        match lsd {
            Digit(0) => Ok(false),
            Digit(1) => Ok(true),
            _ => unreachable!()
        }
    }

    /// Tries to represent the value of this `ApInt` as a `i8`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u8`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i8`.
    pub fn try_to_i8(&self) -> Result<i8> {
        self.try_to_u8()
            .map(|v| v as i8)
            .map_err(|_| Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I8))
    }

    /// Tries to represent the value of this `ApInt` as a `u8`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u8`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u8`.
    pub fn try_to_u8(&self) -> Result<u8> {
        let (lsd, rest) = self.split_least_significant_digit();
        if lsd.repr() > DigitRepr::from(u8::max_value())
           || rest.into_iter().any(|d| d.repr() != 0)
        {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::U8).into()
        }
        Ok(lsd.repr() as u8)
    }

    /// Tries to represent the value of this `ApInt` as a `i16`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u16`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i16`.
    pub fn try_to_i16(&self) -> Result<i16> {
        self.try_to_u16()
            .map(|v| v as i16)
            .map_err(|_| Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I16))
    }

    /// Tries to represent the value of this `ApInt` as a `u16`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u16`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u16`.
    pub fn try_to_u16(&self) -> Result<u16> {
        let (lsd, rest) = self.split_least_significant_digit();
        if lsd.repr() > DigitRepr::from(u16::max_value())
           || rest.into_iter().any(|d| d.repr() != 0)
        {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::U16).into()
        }
        Ok(lsd.repr() as u16)
    }

    /// Tries to represent the value of this `ApInt` as a `i32`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u32`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i32`.
    pub fn try_to_i32(&self) -> Result<i32> {
        self.try_to_u32()
            .map(|v| v as i32)
            .map_err(|_| Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I32))
    }

    /// Tries to represent the value of this `ApInt` as a `u32`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u32`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u32`.
    pub fn try_to_u32(&self) -> Result<u32> {
        let (lsd, rest) = self.split_least_significant_digit();
        if lsd.repr() > DigitRepr::from(u32::max_value())
           || rest.into_iter().any(|d| d.repr() != 0)
        {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::U32).into()
        }
        Ok(lsd.repr() as u32)
    }

    /// Tries to represent the value of this `ApInt` as a `i64`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u64`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i64`.
    pub fn try_to_i64(&self) -> Result<i64> {
        self.try_to_u64()
            .map(|v| v as i64)
            .map_err(|_| Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I64))
    }

    /// Tries to represent the value of this `ApInt` as a `u64`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u64`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u64`.
    pub fn try_to_u64(&self) -> Result<u64> {
        let (lsd, rest) = self.split_least_significant_digit();
        if rest.into_iter().any(|d| d.repr() != 0) {
            return Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::U64).into()
        }
        Ok(lsd.repr() as u64)
    }

    /// Tries to represent the value of this `ApInt` as a `i128`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u128`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `i128`.
    pub fn try_to_i128(&self) -> Result<i128> {
        self.try_to_u128()
            .map(|v| v as i128)
            .map_err(|_| Error::encountered_unrepresentable_value(
                self.clone(), PrimitiveTy::I128))
    }

    /// Tries to represent the value of this `ApInt` as a `u128`.
    /// 
    /// # Note
    /// 
    /// This conversion is possible as long as the value represented
    /// by this `ApInt` does not exceed the maximum value of `u128`.
    /// 
    /// # Errors
    /// 
    /// - If the value represented by this `ApInt` can not be
    ///   represented by a `u128`.
    pub fn try_to_u128(&self) -> Result<u128> {
        let (lsd_0, rest) = self.split_least_significant_digit();
        match rest.split_first() {
            None => {
                Ok(lsd_0.repr() as u128)
            }
            Some((lsd_1, rest)) => {
                if rest.into_iter().any(|d| d.repr() != 0) {
                    return Error::encountered_unrepresentable_value(
                        self.clone(), PrimitiveTy::U64).into()
                }
                let result: u128 =
                    (u128::from(lsd_1.repr()) << digit::BITS) + u128::from(lsd_0.repr());
                Ok(result)
            }
        }
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
