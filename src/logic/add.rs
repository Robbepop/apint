use crate::data::{ApInt, DataAccessMut, ZipDataAccessMutSelf::{Inl, Ext}, Digit};
use crate::info::{Result, Width};
use crate::logic::{try_forward_bin_mut_impl,forward_mut_impl};

/// # Addition and Subtraction Operations
/// 
/// **Note**: unless otherwise noted in the function specific documentation,
/// 
/// - **An Error is returned** if function arguments have unmatching bitwidths.
/// - The functions do **not** allocate memory.
/// - The function works for both signed and unsigned interpretations of an `ApInt`. In other words, in the low-level bit-wise representation there is no difference between a signed and unsigned operation by a certain function on fixed bit-width integers. (Cite: LLVM)
impl ApInt {
    /// Increments this `ApInt` by one inplace.
    pub fn wrapping_inc(&mut self) {
        match self.access_data_mut() {
            DataAccessMut::Inl(x) => {
                *x = x.wrapping_add(Digit::one());
            }
            DataAccessMut::Ext(x) => {
                for i in 0..x.len() {
                    match x[i].overflowing_add(Digit::one()) {
                        (v,false) => {
                            x[i] = v;
                            break;
                        }
                        (v,true) => {
                            //if the ApInt was relatively random this should rarely happen
                            x[i] = v;
                        }
                    }
                }
            }
        }
        self.clear_unused_bits();
    }

    /// Increments this `ApInt` by one and returns the result.
    pub fn into_wrapping_inc(self) -> ApInt {
        forward_mut_impl(self, ApInt::wrapping_inc)
    }

    /// Decrements this `ApInt` by one inplace.
    pub fn wrapping_dec(&mut self) {
        match self.access_data_mut() {
            DataAccessMut::Inl(x) => {
                *x = x.wrapping_sub(Digit::one());
            }
            DataAccessMut::Ext(x) => {
                for i in 0..x.len() {
                    match x[i].overflowing_sub(Digit::one()) {
                        (v,false) => {
                            x[i] = v;
                            break;
                        }
                        (v,true) => {
                            //if the ApInt was relatively random this should rarely happen
                            x[i] = v;
                        }
                    }
                }
            }
        }
        self.clear_unused_bits();
    }

    /// Decrements this `ApInt` by one and returns the result.
    pub fn into_wrapping_dec(self) -> ApInt {
        forward_mut_impl(self, ApInt::wrapping_dec)
    }

    /// Negates this `ApInt` inplace.
    pub fn wrapping_neg(&mut self) {
        self.bitnot();
        self.wrapping_inc();
        //`wrapping_inc` handles clearing the unused bits
    }

    /// Negates this `ApInt` and returns the result.
    pub fn into_wrapping_neg(self) -> ApInt {
        forward_mut_impl(self, ApInt::wrapping_neg)
    }

    /// Add-assigns `rhs` to `self` inplace.
    pub fn wrapping_add_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_add(rhs);
            }
            Ext(lhs, rhs) => {
                let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                lhs[0] = temp;
                for i in 1..lhs.len() {
                    let temp = lhs[i].dd()
                        .wrapping_add(rhs[i].dd())
                        .wrapping_add(carry.dd());
                    lhs[i] = temp.lo();
                    carry = temp.hi();
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Adds `rhs` to `self` and returns the result.
    pub fn into_wrapping_add(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_add_assign)
    }

    /// Add-assigns `rhs` to `self` inplace, and returns a boolean indicating if overflow occured,
    /// according to the **unsigned** interpretation of overflow.
    // TODO: add tests
    #[allow(dead_code)]
    pub(crate) fn overflowing_uadd_assign(&mut self, rhs: &ApInt) -> Result<bool> {
        match self.width().excess_bits() {
            Some(excess) => {
                let mask = Digit::all_set() >> excess;
                match self.zip_access_data_mut_self(rhs)? {
                    Inl(lhs, rhs) => {
                        let temp = lhs.wrapping_add(rhs);
                        *lhs = temp & mask;
                        //excess bits are cleared by the mask
                        return Ok((temp & mask) != temp)
                    }
                    Ext(lhs, rhs) => {
                        let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                        lhs[0] = temp;
                        for i in 1..(lhs.len() - 1) {
                            let temp = lhs[i].dd()
                                .wrapping_add(rhs[i].dd())
                                .wrapping_add(carry.dd());
                            lhs[i] = temp.lo();
                            carry = temp.hi();
                        }
                        let temp = lhs[lhs.len() - 1]
                            .wrapping_add(rhs[lhs.len() - 1])
                            .wrapping_add(carry);
                        lhs[lhs.len() - 1] = temp & mask;
                        //excess bits are cleared by the mask
                        return Ok((temp & mask) != temp)
                    }
                }
            }
            None => {
                match self.zip_access_data_mut_self(rhs)? {
                    Inl(lhs, rhs) => {
                        let temp = lhs.overflowing_add(rhs);
                        *lhs = temp.0;
                        //no excess bits to clear
                        return Ok(temp.1)
                    }
                    Ext(lhs, rhs) => {
                        let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                        lhs[0] = temp;
                        for i in 1..lhs.len() {
                            let temp = lhs[i].dd()
                                .wrapping_add(rhs[i].dd())
                                .wrapping_add(carry.dd());
                            lhs[i] = temp.lo();
                            carry = temp.hi();
                        }
                        //no excess bits to clear
                        return Ok(carry != Digit::zero())
                    }
                }
            }
        }
    }

    /// Add-assigns `rhs` to `self` inplace, and returns a boolean indicating if overflow occured,
    /// according to the **signed** interpretation of overflow.
    // TODO: add tests
    #[allow(dead_code)]
    pub(crate) fn overflowing_sadd_assign(&mut self, rhs: &ApInt) -> Result<bool> {
        let self_sign = self.is_negative();
        let rhs_sign = rhs.is_negative();
        self.wrapping_add_assign(rhs)?;
        Ok((self_sign == rhs_sign) && (self_sign != self.is_negative()))
    }

    /// Subtract-assigns `rhs` from `self` inplace.
    pub fn wrapping_sub_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_sub(rhs);
            }
            Ext(lhs, rhs) => {
                let (temp, mut carry) = lhs[0].dd()
                    .wrapping_add((!rhs[0]).dd())
                    .wrapping_add(Digit::one().dd()).lo_hi();
                lhs[0] = temp;
                for i in 1..lhs.len() {
                    let temp = lhs[i].dd()
                        .wrapping_add((!rhs[i]).dd())
                        .wrapping_add(carry.dd());
                    lhs[i] = temp.lo();
                    carry = temp.hi();
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Subtracts `rhs` from `self` and returns the result.
    pub fn into_wrapping_sub(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sub_assign)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::info::BitWidth;

    mod inc {
        use super::*;
        use std::u64;

        #[test]
        fn test() {
            assert_eq!(ApInt::from(14u8).into_wrapping_inc(),ApInt::from(15u8));
            assert_eq!(ApInt::from(15u8).into_wrapping_inc(),ApInt::from(16u8));
            assert_eq!(ApInt::from(16u8).into_wrapping_inc(),ApInt::from(17u8));
            assert_eq!(ApInt::from(17u8).into_wrapping_inc(),ApInt::from(18u8));
            assert_eq!(ApInt::from([0u64,0,0]).into_wrapping_inc(),ApInt::from([0u64,0,1]));			
            assert_eq!(ApInt::from([0,7,u64::MAX]).into_wrapping_inc(),ApInt::from([0u64,8,0]));
            assert_eq!(ApInt::from([u64::MAX,u64::MAX]).into_wrapping_inc(),ApInt::from([0u64,0]));
            assert_eq!(ApInt::from([0,u64::MAX,u64::MAX - 1])
                .into_wrapping_inc(),ApInt::from([0,u64::MAX,u64::MAX]));
            assert_eq!(ApInt::from([0,u64::MAX,0]).into_wrapping_inc(),ApInt::from([0,u64::MAX,1]));	
        }
    }

    mod wrapping_neg {
        use super::*;

        fn assert_symmetry(input: ApInt, expected: ApInt) {
            assert_eq!(input.clone().into_wrapping_neg(), expected.clone());
            assert_eq!(expected.into_wrapping_neg(), input);
        }

        fn test_vals() -> impl Iterator<Item = i128> {
            [0_i128, 1, 2, 4, 5, 7, 10, 42, 50, 100, 128, 150,
             1337, 123123, 999999, 987432, 77216417].into_iter().map(|v| *v)
        }

        #[test]
        fn simple() {
            assert_symmetry(ApInt::zero(BitWidth::w1()), ApInt::zero(BitWidth::w1()));
            assert_symmetry(ApInt::one(BitWidth::w1()), ApInt::all_set(BitWidth::w1()));
        }

        #[test]
        fn range() {
            for v in test_vals() {
                assert_symmetry(ApInt::from_i8(v as i8), ApInt::from_i8(-v as i8));
                assert_symmetry(ApInt::from_i16(v as i16), ApInt::from_i16(-v as i16));
                assert_symmetry(ApInt::from_i32(v as i32), ApInt::from_i32(-v as i32));
                assert_symmetry(ApInt::from_i64(v as i64), ApInt::from_i64(-v as i64));
                assert_symmetry(ApInt::from_i128(v), ApInt::from_i128(-v));
            }
        }
    }
}