use crate::data::{ApInt, Digit, DataAccess, ZipDataAccess};
use crate::info::{Result, Width};

use std::cmp::Ordering;
use std::ops::Not;

/// **Note:** If `self` and `other` have unmatching bit widths, `false` will be returned.
impl PartialEq for ApInt {
    fn eq(&self, other: &ApInt) -> bool {
        if self.len_bits() != other.len_bits() {
            return false
        }
        self.as_digit_slice() == other.as_digit_slice()
    }
}

/// **Note:** If `self` and `other` have unmatching bit widths, `false` will be returned.
impl Eq for ApInt {}

/// # Comparison Operations
/// 
/// **Note**: unless otherwise noted in the function specific documentation,
/// 
/// - **An Error is returned** if function arguments have unmatching bitwidths.
/// - The functions do **not** allocate memory.
/// - The function works for both signed and unsigned interpretations of an `ApInt`. In other words, in the low-level bit-wise representation there is no difference between a signed and unsigned operation by a certain function on fixed bit-width integers. (Cite: LLVM)
impl ApInt {
    /// Returns `true` if this `ApInt` represents the value zero (`0`).
    /// 
    /// # Note
    /// 
    /// - Zero (`0`) is also called the additive neutral element.
    /// - This operation is more efficient than comparing two instances of `ApInt`
    #[inline]    
    pub fn is_zero(&self) -> bool {
        match self.access_data() {
            DataAccess::Inl(digit) => digit.is_zero(),
            DataAccess::Ext(digits) => {
                digits.iter().all(|digit| digit.is_zero())
            }
        }
    }

    /// Returns `true` if this `ApInt` represents the value one (`1`).
    /// 
    /// # Note
    /// 
    /// - One (`1`) is also called the multiplicative neutral element.
    /// - This operation is more efficient than comparing two instances of `ApInt`
    #[inline]    
    pub fn is_one(&self) -> bool {
        match self.access_data() {
            DataAccess::Inl(digit) => digit == Digit::one(),
            DataAccess::Ext(digits) => {
                let (last, rest) = digits.split_last().unwrap_or_else(|| unreachable!());
                last.is_one() && rest.iter().all(|digit| digit.is_zero())
            }
        }
    }

    /// Returns `true` if this `ApInt` represents an even number.
    /// Equivalent to testing if the least significant bit is zero.
    #[inline]
    pub fn is_even(&self) -> bool {
        !self.least_significant_bit()
    }

    /// Returns `true` if this `ApInt` represents an odd number.
    /// Equivalent to testing if the least significant bit is one.
    #[inline]
    pub fn is_odd(&self) -> bool {
        self.least_significant_bit()
    }

    /// Returns `true` if the **signed** representation of this `ApInt` is positive.
    /// Equivalent to testing if the most significant bit is zero.
    #[inline]
    pub fn is_positive(&self) -> bool {
        !self.most_significant_bit()
    }

    /// Returns `true` if the **signed** representation of this `ApInt` is negative.
    /// Equivalent to testing if the most significant bit is one.
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.most_significant_bit()
    }

    /// Unsigned less-than (`ult`) comparison between `self` and `rhs`, meaning the returned boolean
    /// indicates if `self < rhs` for the **unsigned** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_ult(&self, rhs: &ApInt) -> Result<bool> {
        match self
            .zip_access_data(rhs)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on unsigned less-than (slt) comparison with `lhs < rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))?
        {
            ZipDataAccess::Inl(lhs, rhs) => {
                Ok(lhs.repr() < rhs.repr())
            }
            ZipDataAccess::Ext(lhs, rhs) => {
                for (l, r) in lhs.iter().rev()
                                 .zip(rhs.iter().rev())
                {
                    match l.cmp(r) {
                        Ordering::Less    => return Ok(true),
                        Ordering::Greater => return Ok(false),
                        Ordering::Equal   => ()
                    }
                }
                Ok(false)
            }
        }
    }

    /// Unsigned less-equals (`ule`) comparison between `self` and `rhs`, meaning the returned
    /// boolean indicates if `self <= rhs` for the **unsigned** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_ule(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_ult(self).map(Not::not)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on unsigned less-than or equals (ule) comparison with `lhs <= rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }

    /// Unsigned greater-than (`ugt`) comparison between `self` and `rhs`, meaning the returned
    /// boolean indicates if `self > rhs` for the **unsigned** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_ugt(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_ult(self)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on unsigned greater-than (ugt) comparison with `lhs > rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }

    /// Unsigned greater-equals (`uge`) comparison between `self` and `rhs`, meaning the returned
    /// boolean indicates if `self >= rhs` for the **unsigned** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_uge(&self, rhs: &ApInt) -> Result<bool> {
        self.checked_ult(rhs).map(Not::not)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on unsigned greater-than or equals (ule) comparison with `lhs >= rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }

    /// Signed less-than (`slt`) comparison between `self` and `rhs`, meaning the returned boolean
    /// indicates if `self < rhs` for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_slt(&self, rhs: &ApInt) -> Result<bool> {
        let lhs = self;
        lhs.zip_access_data(rhs).and_then(|zipped| {
            match zipped {
                ZipDataAccess::Inl(lhs, rhs) => {
                    let infate_abs = Digit::BITS - self.width().to_usize();
                    let lhs = (lhs.repr() << infate_abs) as i64;
                    let rhs = (rhs.repr() << infate_abs) as i64;
                    Ok(lhs < rhs)
                }
                ZipDataAccess::Ext(_, _) => {
                    match (lhs.sign_bit(), rhs.sign_bit()) {
                        (false, false) => lhs.checked_ult(rhs),
                        (false, true) => Ok(false),
                        (true, false) => Ok(true),
                        (true, true) => rhs.checked_ugt(lhs)
                    }
                }
            }
        })
        .map_err(|err| err.with_annotation(format!(
            "Error occured on signed less-than (slt) comparison with `lhs < rhs` where \
                \n\tlhs = {:?}\
                \n\trhs = {:?}",
            self, rhs)
        ))
    }

    /// Signed less-equals (`sle`) comparison between `self` and `rhs`, meaning the returned boolean
    /// indicates if `self <= rhs` for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_sle(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_slt(self).map(Not::not)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on signed less-than or equals (ule) comparison with `lhs <= rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }

    /// Signed greater-than (`sgt`) comparison between `self` and `rhs`, meaning the returned
    /// boolean indicates if `self > rhs` for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_sgt(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_slt(self)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on signed greater-than (ugt) comparison with `lhs > rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }

    /// Signed greater-equals (`sge`) comparison between `self` and `rhs`, meaning the returned
    /// boolean indicates if `self >= rhs` for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn checked_sge(&self, rhs: &ApInt) -> Result<bool> {
        self.checked_slt(rhs).map(Not::not)
            .map_err(|err| err.with_annotation(format!(
                "Error occured on signed greater-than or equals (ule) comparison with `lhs >= rhs` where \
                 \n\tlhs = {:?}\
                 \n\trhs = {:?}",
                self, rhs)
            ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod partial_eq {
        use super::*;

        #[test]
        fn simple_small() {
            let a = ApInt::from_u8(42);
            let b = ApInt::from_u8(42);
            let c = ApInt::from_u8(77);
            let d = ApInt::from_u16(42);
            assert_eq!(a, b);
            assert_ne!(a, c);
            assert_ne!(a, d);
            assert_ne!(b, c);
            assert_ne!(b, d);
            assert_ne!(c, d);
        }

        #[test]
        fn simple_large() {
            let a = ApInt::from_u128(42);
            let b = ApInt::from_u128(42);
            let c = ApInt::from_u128(1337);
            let d = ApInt::from_u64(42);
            assert_eq!(a, b);
            assert_ne!(a, c);
            assert_ne!(a, d);
            assert_ne!(b, c);
            assert_ne!(b, d);
            assert_ne!(c, d);
        }
    }
}
