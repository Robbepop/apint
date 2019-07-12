use crate::data::{Digit, ApInt};
use crate::info::{Result, Width};

/// # Utility & Helper Methods
impl ApInt {
    /// Computes the given operation on all digits of this `ApInt`.
    /// 
    /// # Note
    /// 
    /// Prefer this utility method if you want to perform the same
    /// operation for all digits within this `ApInt` as this operation
    /// uses the most efficient way to do so.
    #[inline]    
    pub(crate) fn modify_digits<F>(&mut self, f: F)
        where F: Fn(&mut Digit)
    {
        use crate::data::DataAccessMut::*;
        match self.access_data_mut() {
            Inl(digit) => f(digit),
            Ext(digits) => {
                for digit in digits {
                    f(digit)
                }
            }
        }
    }

    /// Computes the given operation on all digits of this `ApInt`
    /// zipped with the digits of `rhs`.
    /// 
    /// # Note
    /// 
    /// Prefer this utility method for these use cases since this operation
    /// uses the most efficient way to perform the specified task.
    #[inline]    
    pub(crate) fn modify_zipped_digits<F>(&mut self, rhs: &ApInt, f: F) -> Result<()>
        where F: Fn(&mut Digit, Digit)
    {
        use crate::data::ZipDataAccessMutSelf::*;
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => f(lhs, rhs),
            Ext(lhs, rhs) => {
                for (l, &r) in lhs.iter_mut().zip(rhs) {
                    f(l, r)
                }
            }
        }
        Ok(())
    }

    /// Returns the most significant `Digit` of this `ApInt`.
    #[inline]    
    pub(crate) fn most_significant_digit(&self) -> Digit {
        use crate::data::DataAccess::*;
        match self.access_data() {
            Inl(digit) => digit,
            Ext(digits) => {
                *digits.last().unwrap()
            }
        }
    }

    /// Returns a mutable reference to the most significant `Digit` of this `ApInt`.
    #[inline]    
    pub(crate) fn most_significant_digit_mut(&mut self) -> &mut Digit {
        use crate::data::DataAccessMut::*;
        match self.access_data_mut() {
            Inl(digit) => digit,
            Ext(digits) => {
                digits.last_mut().unwrap()
            }
        }
    }

    /// Returns the least significant `Digit` of this `ApInt`.
    #[inline]    
    pub(crate) fn least_significant_digit(&self) -> Digit {
        use crate::data::DataAccess::*;
        match self.access_data() {
            Inl(digit) => digit,
            Ext(digits) => digits[0]
        }
    }

    #[inline]    
    pub(crate) fn most_significant_bit(&self) -> bool {
        let sign_bit_pos = self.width().sign_bit_pos();
        self.most_significant_digit()
            .get(sign_bit_pos.to_pos_within_digit())
            .expect("`BitWidth::excess_bits` returns a number that \
                     is always a valid `BitPos` for a `Digit` so this \
                     operation cannot fail.")
    }

    #[inline]    
    pub(crate) fn least_significant_bit(&self) -> bool {
        self.least_significant_digit().least_significant_bit()
    }

    /// Clears unused bits of this `ApInt`.
    /// 
    /// # Example
    /// 
    /// An `ApInt` with a `BitWidth` of `100` bits requires 2 `Digit`s for its internal value
    /// representation, each having 64-bits which totals in `128` bits for the `ApInt` instance.
    /// So upon a call to `ApInt::clear_unused_bits` the upper
    /// `128-100 = 28` bits are cleared (set to zero (`0`)).
    #[inline]    
    pub(crate) fn clear_unused_bits(&mut self) {
        if let Some(bits) = self.width().excess_bits() {
            *self.most_significant_digit_mut() &= !(Digit::ONES << bits);
        }
    }

    /// Splits the least significant digits from the rest of the digit slice
    /// and returns it as well as the remaining part of the digit slice.
    #[inline]    
    pub(crate) fn split_least_significant_digit(&self) -> (Digit, &[Digit]) {
        use crate::data::DataAccess::*;
        match self.access_data() {
            Inl(digit) => (digit, &[]),
            Ext(digits) => {
                let (lsd, rest) = digits.split_first()
                    .expect("An `ApInt` always has at least one digit so calling \
                             `split_first` on a slice of its digits will never \
                             return `None`.");
                (*lsd, rest)
            }
        }
    }

    /// Splits the most significant digits from the rest of the digit slice
    /// and returns it as well as the remaining part of the digit slice.
    #[inline]    
    pub(crate) fn split_most_significant_digit(&self) -> (Digit, &[Digit]) {
        use crate::data::DataAccess::*;
        match self.access_data() {
            Inl(digit) => (digit, &[]),
            Ext(digits) => {
                let (lsd, rest) = digits.split_last()
                    .expect("An `ApInt` always has at least one digit so calling \
                             `split_last` on a slice of its digits will never \
                             return `None`.");
                (*lsd, rest)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn most_significant_bit() {
        assert_eq!(false,
            ApInt::from_bool(false).most_significant_bit());
        assert_eq!(true,
            ApInt::from_bool(true).most_significant_bit());
        assert_eq!(false,
            ApInt::from_u8(0b0101_0101).most_significant_bit());
        assert_eq!(true,
            ApInt::from_u8(0b1101_0101).most_significant_bit());
        assert_eq!(false,
            ApInt::from_u16(0b0111_1000_1101_0101).most_significant_bit());
        assert_eq!(true,
            ApInt::from_u16(0b1011_0001_0101_0101).most_significant_bit());
        assert_eq!(false,
            ApInt::from_u32(0x7000_0000).most_significant_bit());
        assert_eq!(true,
            ApInt::from_u32(0x8000_0000).most_significant_bit());
        assert_eq!(false,
            ApInt::from_u64(0x70FC_A875_4321_1234).most_significant_bit());
        assert_eq!(true,
            ApInt::from_u64(0x8765_4321_5555_6666).most_significant_bit());
    }
}
