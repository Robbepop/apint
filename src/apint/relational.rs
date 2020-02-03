use crate::{
    apint::{
        utils::ZipDataAccess,
        ApInt,
    },
    digit::{
        Bit,
        Digit,
    },
    errors::Result,
    mem::format,
    Width,
};
use core::{
    cmp::Ordering,
    ops::Not,
};

/// If `self` and `other` have unmatching bit widths, `false` will be returned.
impl PartialEq for ApInt {
    fn eq(&self, other: &ApInt) -> bool {
        if self.len_bits() != other.len_bits() {
            return false
        }
        self.as_digit_slice() == other.as_digit_slice()
    }
}

impl Eq for ApInt {}

/// # Comparison Operations
impl ApInt {
    /// Unsigned less-than (`ult`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self < rhs`.
    /// - Interprets both `ApInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn checked_ult(&self, rhs: &ApInt) -> Result<bool> {
        match self.zip_access_data(rhs).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on unsigned less-than (slt) comparison with `lhs < rhs` \
                 where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })? {
            ZipDataAccess::Inl(lhs, rhs) => Ok(lhs.repr() < rhs.repr()),
            ZipDataAccess::Ext(lhs, rhs) => {
                for (l, r) in lhs.iter().rev().zip(rhs.iter().rev()) {
                    match l.cmp(r) {
                        Ordering::Less => return Ok(true),
                        Ordering::Greater => return Ok(false),
                        Ordering::Equal => (),
                    }
                }
                Ok(false)
            }
        }
    }

    /// Unsigned less-equals (`ule`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self <= rhs`.
    /// - Interprets both `ApInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_ule(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_ult(self).map(Not::not).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on unsigned less-than or equals (ule) comparison with \
                 `lhs <= rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
    }

    /// Unsigned greater-than (`ugt`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self > rhs`.
    /// - Interprets both `ApInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_ugt(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_ult(self).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on unsigned greater-than (ugt) comparison with `lhs > \
                 rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
    }

    /// Unsigned greater-equals (`uge`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self >= rhs`.
    /// - Interprets both `ApInt` instances as **unsigned** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_uge(&self, rhs: &ApInt) -> Result<bool> {
        self.checked_ult(rhs).map(Not::not).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on unsigned greater-than or equals (ule) comparison with \
                 `lhs >= rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
    }

    /// Signed less-than (`slt`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self < rhs`.
    /// - Interprets both `ApInt` instances as **signed** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn checked_slt(&self, rhs: &ApInt) -> Result<bool> {
        let lhs = self;
        lhs.zip_access_data(rhs)
            .and_then(|zipped| {
                match zipped {
                    ZipDataAccess::Inl(lhs, rhs) => {
                        let infate_abs = Digit::BITS - self.width().to_usize();
                        let lhs = (lhs.repr() << infate_abs) as i64;
                        let rhs = (rhs.repr() << infate_abs) as i64;
                        Ok(lhs < rhs)
                    }
                    ZipDataAccess::Ext(..) => {
                        match (lhs.sign_bit(), rhs.sign_bit()) {
                            (Bit::Unset, Bit::Unset) => lhs.checked_ult(rhs),
                            (Bit::Unset, Bit::Set) => Ok(false),
                            (Bit::Set, Bit::Unset) => Ok(true),
                            (Bit::Set, Bit::Set) => rhs.checked_ugt(lhs),
                        }
                    }
                }
            })
            .map_err(|err| {
                err.with_annotation(format!(
                    "Error occured on signed less-than (slt) comparison with `lhs < \
                     rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                    self, rhs
                ))
            })
    }

    /// Signed less-equals (`sle`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self <= rhs`.
    /// - Interprets both `ApInt` instances as **signed** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_sle(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_slt(self).map(Not::not).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on signed less-than or equals (ule) comparison with `lhs \
                 <= rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
    }

    /// Signed greater-than (`sgt`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self > rhs`.
    /// - Interprets both `ApInt` instances as **signed** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_sgt(&self, rhs: &ApInt) -> Result<bool> {
        rhs.checked_slt(self).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on signed greater-than (ugt) comparison with `lhs > rhs` \
                 where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
    }

    /// Signed greater-equals (`sge`) comparison between `self` and `rhs`.
    ///
    /// # Note
    ///
    /// - `checked_` for this function means that it checks the bit widths
    /// - Returns `Ok(true)` if `self >= rhs`.
    /// - Interprets both `ApInt` instances as **signed** values.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    #[inline]
    pub fn checked_sge(&self, rhs: &ApInt) -> Result<bool> {
        self.checked_slt(rhs).map(Not::not).map_err(|err| {
            err.with_annotation(format!(
                "Error occured on signed greater-than or equals (ule) comparison with \
                 `lhs >= rhs` where \n\tlhs = {:?}\n\trhs = {:?}",
                self, rhs
            ))
        })
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
