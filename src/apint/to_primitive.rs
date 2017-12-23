use apint::{ApInt};
use errors::{Result};

//  =======================================================================
///  Operations to cast to primitive number types.
/// =======================================================================
impl ApInt {
    /// Truncates this `ApInt` to a `bool` primitive type.
    /// 
    /// Bits in this `ApInt` that are not within the bounds
    /// of the `bool` are being ignored.
    /// 
    /// # Note
    /// 
    /// Basically this returns `true` if the least significant
    /// bit of this `ApInt` is `1` and `false` otherwise.
    pub fn truncate_to_bool(&self) -> bool {
        unimplemented!()
    }

    /// Truncates this `ApInt` to a `i8` primitive type.
    /// 
    /// All bits but the least significant `8` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_i8(&self) -> i8 {
        self.truncate_to_u8() as i8
    }

    /// Truncates this `ApInt` to a `u8` primitive type.
    /// 
    /// All bits but the least significant `8` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_u8(&self) -> u8 {
        unimplemented!()
    }

    /// Truncates this `ApInt` to a `i16` primitive type.
    /// 
    /// All bits but the least significant `16` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_i16(&self) -> i16 {
        self.truncate_to_u16() as i16
    }

    /// Truncates this `ApInt` to a `u16` primitive type.
    /// 
    /// All bits but the least significant `16` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_u16(&self) -> u16 {
        unimplemented!()
    }

    /// Truncates this `ApInt` to a `i32` primitive type.
    /// 
    /// All bits but the least significant `32` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_i32(&self) -> i32 {
        self.truncate_to_u32() as i32
    }

    /// Truncates this `ApInt` to a `u32` primitive type.
    /// 
    /// All bits but the least significant `32` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_u32(&self) -> u32 {
        unimplemented!()
    }

    /// Truncates this `ApInt` to a `i64` primitive type.
    /// 
    /// All bits but the least significant `64` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_i64(&self) -> i64 {
        self.truncate_to_u64() as i64
    }

    /// Truncates this `ApInt` to a `u64` primitive type.
    /// 
    /// All bits but the least significant `64` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_u64(&self) -> u64 {
        unimplemented!()
    }

    /// Truncates this `ApInt` to a `i128` primitive type.
    /// 
    /// All bits but the least significant `128` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_i128(&self) -> i128 {
        self.truncate_to_u64() as i128
    }

    /// Truncates this `ApInt` to a `u128` primitive type.
    /// 
    /// All bits but the least significant `128` bits are
    /// being ignored by this operation to construct the
    /// result.
    pub fn truncate_to_u128(&self) -> u128 {
        unimplemented!()
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
        unimplemented!()
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
        self.try_to_u8().map(|v| v as i8)
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
        unimplemented!()
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
        self.try_to_u16().map(|v| v as i16)
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
        unimplemented!()
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
        self.try_to_u32().map(|v| v as i32)
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
        unimplemented!()
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
        self.try_to_u64().map(|v| v as i64)
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
        unimplemented!()
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
        self.try_to_u128().map(|v| v as i128)
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
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
}
