use crate::data::{ApInt, DataAccessMut, Digit};
use crate::info::{Result, Width, ShiftAmount};
use crate::logic::try_forward_bin_mut_impl;

/// # Shift Operations
/// 
/// **Note**: unless otherwise noted in the function specific documentation,
/// 
/// - The functions do **not** allocate memory.
impl ApInt {

    /// Left-shifts this `ApInt` by the given `shift_amount` bits.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_shl_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        let shift_amount = shift_amount.into();
        shift_amount.verify_shift_amount(self)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                *digit.repr_mut() <<= shift_amount.to_usize();
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    let digits_len  = digits.len();
                    {
                        use std::ptr;
                        let src_ptr = digits.as_mut_ptr();
                        unsafe {
                            let dst_ptr = src_ptr.offset(digit_steps as isize);
                            ptr::copy(src_ptr, dst_ptr, digits_len - digit_steps)
                        }
                    }
                    digits.iter_mut()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::zero());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps != 0 {
                    let mut carry = 0;
                    for elem in digits[digit_steps..].iter_mut() {
                        let repr = elem.repr();
                        let new_carry = repr >> (Digit::BITS - bit_steps);
                        *elem = Digit((repr << bit_steps) | carry);
                        carry = new_carry;
                    }
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Shift this `ApInt` left by the given `shift_amount` bits and returns the result.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_shl<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_shl_assign)
    }

    /// Logically right-shifts this `ApInt` by the given `shift_amount` bits.
    /// 
    /// # Note
    /// 
    /// Logical right shifts do not copy the sign bit (the most significant bits are filled up with
    /// zeros), and thus can act as a floored division by a power of two for the **unsigned**
    /// interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_lshr_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        let shift_amount = shift_amount.into();
        shift_amount.verify_shift_amount(self)?;
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                *digit.repr_mut() >>= shift_amount.to_usize();
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    digits.rotate_left(digit_steps);
                    digits.iter_mut()
                          .rev()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::zero());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps > 0 {
                    let mut borrow = 0;
                    for elem in digits.iter_mut().rev() {
                        let repr = elem.repr();
                        let new_borrow = repr << (Digit::BITS - bit_steps);
                        *elem = Digit((repr >> bit_steps) | borrow);
                        borrow = new_borrow;
                    }
                }
            }
        }
        Ok(())
    }

    /// Logically right-shifts this `ApInt` by the given `shift_amount` bits
    /// and returns the result.
    /// 
    /// # Note
    /// 
    /// Logical right shifts do not copy the sign bit (the most significant bits are filled up with
    /// zeros), and thus can act as a floored division by a power of two for the **unsigned**
    /// interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_lshr<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_lshr_assign)
    }

    /// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits.
    /// 
    /// # Note
    /// 
    /// Arithmetic right shifts copy the sign bit to the most significant bits, and thus can act as
    /// a floored division by a power of two for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn wrapping_ashr_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        if self.sign_bit() == false {
            return self.wrapping_lshr_assign(shift_amount)
        }
        let shift_amount = shift_amount.into();
        shift_amount.verify_shift_amount(self)?;
        let width = self.width();
        match self.access_data_mut() {
            DataAccessMut::Inl(digit) => {
                let mut signed = digit.clone();
                signed.sign_extend_from(width).unwrap();
                let signed = signed.repr() as i64;
                let shifted = signed >> shift_amount.to_usize();
                *digit.repr_mut() = shifted as u64;
            }
            DataAccessMut::Ext(digits) => {
                let digit_steps = shift_amount.digit_steps();
                if digit_steps != 0 {
                    digits.rotate_left(digit_steps);
                    digits.iter_mut()
                          .rev()
                          .take(digit_steps)
                          .for_each(|d| *d = Digit::all_set());
                }
                let bit_steps = shift_amount.bit_steps();
                if bit_steps > 0 {
                    let mut borrow = 0xFFFF_FFFF_FFFF_FFFF << (Digit::BITS - bit_steps);
                    for elem in digits.iter_mut().rev().skip(digit_steps) {
                        let repr = elem.repr();
                        let new_borrow = repr << (Digit::BITS - bit_steps);
                        *elem = Digit((repr >> bit_steps) | borrow);
                        borrow = new_borrow;
                    }
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Arithmetically right-shifts this `ApInt` by the given `shift_amount` bits
    /// and returns the result.
    /// 
    /// # Note
    /// 
    /// Arithmetic right shifts copy the sign bit to the most significant bits, and thus can act as
    /// a floored division by a power of two for the **signed** interpretation of `ApInt`s.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_wrapping_ashr<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::wrapping_ashr_assign)
    }

    /// Circularly left-rotates this `ApInt` by the given `shift_amount` bits. In other words, the
    /// bits are shifted like a logical left shift would, except the bits that go outside the bit
    /// width of the `ApInt` wrap around to the least significant bits.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    /// 
    /// # Performance
    /// 
    /// This function is equivalent to the following:
    /// ```
    /// use apint::{ApInt, Width};
    /// let input = ApInt::from([1u64, 2, 3, 4]);
    /// let shift = 64usize;
    /// let output = if shift == 0 {
    ///     input.clone()
    /// } else {
    ///     input.clone().into_wrapping_shl(shift).unwrap()
    ///         | (&input.clone().into_wrapping_lshr(input.width().to_usize() - shift).unwrap())
    /// };
    /// assert_eq!(output, input.into_rotate_left(shift).unwrap());
    /// assert_eq!(output, ApInt::from([2, 3, 4, 1u64]));
    /// ```
    /// 
    /// However, this function avoids allocation and has many optimized branches for different input
    /// sizes and shifts.
    pub fn rotate_left_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        //A rotate left function that assumes `(0 < s < Digit::BITS) && (x.len() > 1)`, and treats
        //`x` as a whole `ApInt`.
        fn subdigit_rotate_left(x: &mut [Digit], s: usize) {
            let uns = Digit::BITS - s;
            //keep the end for wrapping around to the beginning
            let wrap_around = (x[x.len() - 1] >> uns) | (x[0] << s);
            for i in (0..(x.len() - 1)).rev() {
                x[i + 1] = (x[i] >> uns) | (x[i + 1] << s);
            }
            x[0] = wrap_around;
        }

        //A rotate right function that assumes `(0 < s < Digit::BITS) && (x.len() > 1)`, and treats
        //`x` as one whole `ApInt`
        fn subdigit_rotate_right(x: &mut [Digit], s: usize) {
            let uns = Digit::BITS - s;
            //keep the beginning for wrapping around to the end
            let wrap_around = (x[x.len() - 1] >> s) | (x[0] << uns);
            for i in 0..(x.len() - 1) {
                x[i] = (x[i] >> s) | (x[i + 1] << uns);
            }
            x[x.len() - 1] = wrap_around;
        }

        //A rotate left function that assumes
        //`(0 < s < Digit::BITS) && (end_bits > 0) && (x.len() > 1)`. `end_bits` is
        //`width % Digit::BITS`.
        fn subdigit_rotate_left_nonmultiple(x: &mut [Digit], end_bits: usize, s: usize) {
            let uns = Digit::BITS - s;
            let end_mask = Digit::ONES >> (Digit::BITS - end_bits);
            //handle tricky wrap around from the end to be beginning
            let mut tmp0 = if s > end_bits {
                (x[x.len() - 2] >> (Digit::BITS + end_bits - s))
                | (x[x.len() - 1] << (s - end_bits))
                | (x[0] << s)
            } else {
                (x[x.len() - 1] >> (end_bits - s)) | (x[0] << s)
            };
            let mut tmp1: Digit;
            let mut i = 0;
            loop {
                tmp1 = (x[i] >> uns) | (x[i + 1] << s);
                x[i] = tmp0;
                i += 1;
                if i == (x.len() - 1) {
                    x[i] = tmp1 & end_mask;
                    return
                }
                tmp0 = (x[i] >> uns) | (x[i + 1] << s);
                x[i] = tmp1;
                i += 1;
                if i == (x.len() - 1) {
                    x[i] = tmp0 & end_mask;
                    return
                }
            }
        }

        //A rotate left function that assumes `(s > 0) && (x.len() > 1)` and treats the width
        //as if it took up all of `x`. `s` is in digits.
        fn digit_rotate_left(x: &mut [Digit], s: usize) {
            if x.len() > 16 {
                //this becomes faster at about this point
                x.rotate_left(s);
                return
            }
            //in order to avoid allocation, we have to "leapfrog" and wrap around the indexing.
            let mut start = 0;
            let mut lowest_nonstart = s;
            loop {
                let mut tmp0 = x[start];
                let mut tmp1;
                let mut i = start + s;
                loop {
                    tmp1 = x[i];
                    x[i] = tmp0;
                    i += s;
                    if i >= x.len() {
                        i -= x.len();
                        if i == start {
                            x[i] = tmp1;
                            break
                        }
                        //we cannot just have a `lowest_nonstart = i` here without a conditional
                        //(counterexample is x.len() = 16 and s = 6)
                        if i < lowest_nonstart {
                            lowest_nonstart = i;
                        }
                    }
                    //Repeat with swapped temporaries in case the compiler cannot do it.
                    //We do not need a second indexing variable to handle the source
                    //digit, because that source variable is already stored in tmp0 or
                    //tmp1.
                    tmp0 = x[i];
                    x[i] = tmp1;
                    i += s;
                    if i >= x.len() {
                        i -= x.len();
                        if i == start {
                            x[i] = tmp0;
                            break
                        }
                        if i < lowest_nonstart {
                            lowest_nonstart = i;
                        }
                    }
                }
                //the leapfrog wraps around until it arrives back where it started, but
                //not all digits have been shifted the first time if `(x.len() % digits) == 0`.
                start += 1;
                if start == lowest_nonstart {return}
            }
        }

        //for `ApInt`s with a bit width that is not an integer multiple of `Digit`s, and a shift
        //equal to or larger than a digit, `subdigit_rotate_left` and `digit_rotate_left` should
        //be used followed by this correct the shift.
        //assumes `(digits > 0) && (end_bits > 0)`
        fn nonmultiple_rotate_correction(x: &mut [Digit], end_bits: usize, digits: usize, shift_bits: usize) {
            //digits > 0, so the bits after the end_bits will always all be wrap around bits
            let unshift = Digit::BITS - shift_bits;
            let unbits = Digit::BITS - end_bits;
            if shift_bits == 0 {
                //this is difficult to explain, the best way is to look at a diagram
                //[Digit::BITS is 8 here]
                //01234567_89abcdef //all of x
                //01234567_8 //actual width end_bits = 1
                //89abcdef_01234567 //x is shifted by 8
                //8XXXXXXX_0 1234567 //`X`s are garbage bits and the end bits are wraparound.
                //12345678_0 //the lowest bits and end bits are shifted to get a correct answer
                
                //in reverse order to avoid temporaries
                for i in (0..(digits - 1)).rev() {
                    x[i + 1] = (x[i] >> end_bits) | (x[i + 1] << unbits);
                }
                //wrap around.
                //Note that `digits > 0`, so bits after the end bits will always wrap around
                x[0] = (x[x.len() - 1] >> end_bits) | (x[0] << unbits);
                //get rid of the wraparound
                x[x.len() - 1] = x[x.len() - 1] & (Digit::ONES >> unbits);
            } else if unbits < shift_bits {
                //whenever the garbage bits are located in one digit
                //01234567_89abcdef_ghijklmn //all of x
                //01234567_89abcdef_ghijkl //actual width end_bits = 6
                //defghijk_lmn01234_56789abc //x shifted by 11
                //defghijk_lXX01234_56789a bc 
                //bcdefghi_jkl01234_56789a //the result

                //01234567_89abcdef //all of x
                //01234567_89abcde //actual width end_bits = 6
                //56789abc_def01234 //x shifted by 11
                //56789abc_deX0123 4
                //456789ab_cde0123 //the result

                //start with overwriting the bits in the middle
                x[digits] = (x[digits - 1] >> end_bits)
                    | ((x[digits] & (Digit::ONES >> (unshift + unbits))) << unbits)
                    | (x[digits] & (Digit::ONES << shift_bits));

                //shift the lower bits up in reverse order to avoid temporaries
                for i in (0..(digits - 1)).rev() {
                    x[i + 1] = (x[i] >> end_bits) | (x[i + 1] << unbits);
                }
                //wrap around
                x[0] = (x[x.len() - 1] >> end_bits) | (x[0] << unbits);
                //get rid of the wraparound
                x[x.len() - 1] = x[x.len() - 1] & (Digit::ONES >> unbits);
            } else {
                //same as above but the bits that we want to overwrite are across digit boundaries
                //01234567_89abcdef_ghijklmn //all of x
                //01234567_89abcdef_ghi //end_bits = 3
                //defghijk_lmn01234_56789abc //shifted left 11
                //defghiXX_XXX01234_567 89abc
                //89abcdef_ghi01234_567

                //01234567_89abcdef_ghijklmn //all of x
                //01234567_89abcdef_g //end_bits = 1
                //fghijklm_n0123456_789abcde //shifted left 9
                //fgXXXXXX_X0123456_7 89abcde
                //89abcdef_g0123456_7

                //this can also handle unbits == shift_bits
                //01234567_89abcdef_ghijklmn //all of x
                //01234567_89abcdef_ghijklm //end_bits = 7
                //fghijklm_n0123456_789abcde //shifted left 9
                //fghijklm_X0123456_789abcd e
                //efghijkl_m0123456_789abcd
                x[digits] = ((x[digits - 1] >> end_bits) & (Digit::ONES >> unshift))
                    | (x[digits] & (Digit::ONES << shift_bits));
                //in reverse order to avoid temporaries
                for i in (0..(digits - 1)).rev() {
                    x[i + 1] = (x[i] >> end_bits) | (x[i + 1] << unbits);
                }
                //wrap around
                x[0] = (x[x.len() - 1] >> end_bits) | (x[0] << unbits);
                //get rid of the left over wraparound
                x[x.len() - 1] = x[x.len() - 1] & (Digit::ONES >> unbits);
            }
        }

        let s = shift_amount.into();
        s.verify_shift_amount(self)?;
        let s = s.to_usize();
        //this is necessary, otherwise there can be shifts by `Digit::BITS` which causes overflows
        if s == 0 {return Ok(())}
        let width = self.width().to_usize();
        match self.access_data_mut() {
            DataAccessMut::Inl(x) => {
                *x = (((*x) << s) | ((*x) >> (width - s))) & (Digit::ONES >> (Digit::BITS - width));
            }
            DataAccessMut::Ext(x) => {
                let end_bits = width % Digit::BITS;
                let (digits, bits) = (s / Digit::BITS, s % Digit::BITS);
                match (digits == 0, bits == 0, end_bits == 0) {
                    //`bits != 0` in the following two cases
                    (true, _, true) => subdigit_rotate_left(x, bits),
                    (true, _, false) => subdigit_rotate_left_nonmultiple(x, end_bits, bits),
                    (false, true, true) => digit_rotate_left(x, digits),
                    (false, false, true) => {
                        //it is not worth it to have a single function for this, which was learned
                        //the hard way (extra masking operations cause the complicated function to
                        //have about the same number of operations per digit as two separate shift
                        //functions). Optimizing each function separately for SIMD is probably the
                        //most performant.
                        if digits == (x.len() - 1) {
                            //faster branch
                            subdigit_rotate_right(x, Digit::BITS - bits);
                        } else {
                            digit_rotate_left(x, digits);
                            subdigit_rotate_left(x, bits);
                        }
                    },
                    (false, true, false) => {
                        digit_rotate_left(x, digits);
                        nonmultiple_rotate_correction(x, end_bits, digits, bits);
                    },
                    (false, false, false) => {
                        //not using the `subdigit_rotate_left_nonmultiple` function because it cuts
                        //off needed end bits for the `nonmultiple_rotate_correction`
                        if digits == (x.len() - 1) {
                            //faster branch
                            subdigit_rotate_right(x, Digit::BITS - bits);
                        } else {
                            digit_rotate_left(x, digits);
                            subdigit_rotate_left(x, bits);
                        }
                        nonmultiple_rotate_correction(x, end_bits, digits, bits);
                    },
                }
            }
        }
        Ok(())
    }

    /// Circularly left-rotates this `ApInt` by the given `shift_amount` bits and returns the
    /// result.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_rotate_left<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::rotate_left_assign)
    }

    /// Circularly right-rotates this `ApInt` by the given `shift_amount` bits. In other words, the
    /// bits are shifted like a logical right shift would, except the bits that go outside the bit
    /// width of the `ApInt` wrap around to the most significant bits.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    /// 
    /// # Performance
    /// 
    /// This function is equivalent to the following:
    /// ```
    /// use apint::{ApInt, Width};
    /// let input = ApInt::from([1u64, 2, 3,4 ]);
    /// let shift = 64usize;
    /// let output = if shift == 0 {
    ///     input.clone()
    /// } else {
    ///     input.clone().into_wrapping_lshr(shift).unwrap()
    ///         | (&input.clone().into_wrapping_shl(input.width().to_usize() - shift).unwrap())
    /// };
    /// assert_eq!(output, input.into_rotate_right(shift).unwrap());
    /// assert_eq!(output, ApInt::from([4, 1u64, 2, 3]));
    /// ```
    /// 
    /// However, this function avoids allocation and has many optimized branches for different input
    /// sizes and shifts.
    pub fn rotate_right_assign<S>(&mut self, shift_amount: S) -> Result<()>
        where S: Into<ShiftAmount>
    {
        //compiler should be able to clean this up
        let s = shift_amount.into().to_usize();
        if s == 0 {return Ok(())}
        let width = self.width().to_usize();
        self.rotate_left_assign(ShiftAmount::from(width - s))
    }

    /// Circularly right-rotates this `ApInt` by the given `shift_amount` bits and returns the
    /// result.
    /// 
    /// # Errors
    /// 
    /// - If the given `shift_amount` is invalid for the bit width of this `ApInt`.
    pub fn into_rotate_right<S>(self, shift_amount: S) -> Result<ApInt>
        where S: Into<ShiftAmount>
    {
        try_forward_bin_mut_impl(self, shift_amount, ApInt::rotate_right_assign)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_reprs_w64() -> impl Iterator<Item = u64> {
        vec![
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0x0000_0000_0000_0000,
            0x5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA,
            0xFFFF_FFFF_FFFF_FFFF,
        ]
        .into_iter()
    }

    fn test_apints_w64() -> impl Iterator<Item = ApInt> {
        test_reprs_w64().map(ApInt::from_u64)
    }

    fn test_reprs_w128() -> impl Iterator<Item = u128> {
        vec![
            0x0123_4567_89AB_CDEF_0011_2233_4455_6677,
            0xFEDC_BA98_7654_3210_7766_5544_3322_1100,
            0x0000_0000_0000_0000_0000_0000_0000_0001,
            0x8000_0000_0000_0000_0000_0000_0000_0000,
            0x0000_0000_0000_0000_0000_0000_0000_0000,
            0x5555_5555_5555_5555_5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        ]
        .into_iter()
    }

    fn test_apints_w128() -> impl Iterator<Item = ApInt> {
        test_reprs_w128().map(ApInt::from_u128)
    }

    mod shl {
        use super::*;

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_shl_assign(shamt).unwrap();
                    let expected = ApInt::from_u64(repr << shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_shl_assign(shamt).unwrap();
                    let expected = ApInt::from_u128(repr << shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_xtra_large_ok() {
            let d0 = 0xFEDC_BA98_7654_3210;
            let d1 = 0x5555_5555_4444_4444;
            let d2 = 0xAAAA_AAAA_CCCC_CCCC;
            let d3 = 0xFFFF_7777_7777_FFFF;
            let input: [u64; 4] = [d0, d1, d2, d3];
            {
                let shamt = 100;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 1);
                assert_eq!(bit_steps, 36);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d1 << bit_steps) | (d2 >> (Digit::BITS - bit_steps)),
                    (d2 << bit_steps) | (d3 >> (Digit::BITS - bit_steps)),
                    (d3 << bit_steps),
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
            {
                let shamt = 150;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 2);
                assert_eq!(bit_steps, 22);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d2 << bit_steps) | (d3 >> (Digit::BITS - bit_steps)),
                    (d3 << bit_steps),
                    0,
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
            {
                let shamt = 200;
                let digit_steps = shamt / 64;
                let bit_steps = shamt % 64;
                assert_eq!(digit_steps, 3);
                assert_eq!(bit_steps, 8);
                let result = ApInt::from(input)
                    .into_wrapping_shl(shamt)
                    .unwrap();
                let expected: [u64; 4] = [
                    (d3 << bit_steps),
                    0,
                    0,
                    0
                ];
                let expected = ApInt::from(expected);
                assert_eq!(result, expected);
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_shl_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_shl_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_shl_assign(shamt).unwrap();
                    let y = y.into_wrapping_shl(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_shl_assign(shamt).unwrap();
                    let y = y.into_wrapping_shl(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }

    mod lshr {
        use super::*;

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_lshr_assign(shamt).unwrap();
                    let expected = ApInt::from_u64(repr >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_lshr_assign(shamt).unwrap();
                    let expected = ApInt::from_u128(repr >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_lshr_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_lshr_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_lshr_assign(shamt).unwrap();
                    let y = y.into_wrapping_lshr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_lshr_assign(shamt).unwrap();
                    let y = y.into_wrapping_lshr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }

    mod ashr {
        use super::*;

        #[test]
        fn regression_stevia_01() {
            let input = ApInt::from_i32(-8);
            let expected = ApInt::from_u32(0x_FFFF_FFFE);
            assert_eq!(input.into_wrapping_ashr(ShiftAmount::from(2)).unwrap(), expected);
        }

        #[test]
        fn assign_small_ok() {
            for repr in test_reprs_w64() {
                for shamt in 0..64 {
                    let mut result = ApInt::from_u64(repr);
                    result.wrapping_ashr_assign(shamt).unwrap();
                    let expected = ApInt::from_i64((repr as i64) >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_large_ok() {
            for repr in test_reprs_w128() {
                for shamt in 0..128 {
                    let mut result = ApInt::from_u128(repr);
                    result.wrapping_ashr_assign(shamt).unwrap();
                    let expected = ApInt::from_i128((repr as i128) >> shamt);
                    assert_eq!(result, expected);
                }
            }
        }

        #[test]
        fn assign_small_fail() {
            for mut apint in test_apints_w64() {
                assert!(apint.wrapping_ashr_assign(64).is_err())
            }
        }

        #[test]
        fn assign_large_fail() {
            for mut apint in test_apints_w128() {
                assert!(apint.wrapping_ashr_assign(128).is_err())
            }
        }

        #[test]
        fn into_equivalent_small() {
            for apint in test_apints_w64() {
                for shamt in 0..64 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_ashr_assign(shamt).unwrap();
                    let y = y.into_wrapping_ashr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }

        #[test]
        fn into_equivalent_large() {
            for apint in test_apints_w128() {
                for shamt in 0..128 {
                    let mut x = apint.clone();
                    let     y = apint.clone();
                    x.wrapping_ashr_assign(shamt).unwrap();
                    let y = y.into_wrapping_ashr(shamt).unwrap();
                    assert_eq!(x, y);
                }
            }
        }
    }

    mod rotate {
        use super::*;
        use std::u128;

        #[test]
        fn rotate_left() {
            assert_eq!(ApInt::from(1u8).into_rotate_left(0).unwrap(),ApInt::from(1u8));
            assert_eq!(ApInt::from(123u8).into_rotate_left(7).unwrap(),ApInt::from(123u8.rotate_left(7)));
            assert_eq!(ApInt::from(1u128).into_rotate_left(0).unwrap(),ApInt::from(1u128));
            assert_eq!(ApInt::from(1u128).into_rotate_left(1).unwrap(),ApInt::from(0b10u128));
            assert_eq!(ApInt::from(1u128).into_rotate_left(32).unwrap(),ApInt::from(0x1_0000_0000u128));
            assert_eq!(ApInt::from(1u128).into_rotate_left(64).unwrap(),ApInt::from(0x1_0000_0000_0000_0000u128));
            assert_eq!(ApInt::from(1u128).into_rotate_left(68).unwrap(),ApInt::from(0x10_0000_0000_0000_0000u128));
            assert_eq!(ApInt::from(1u128 << 126).into_rotate_left(33).unwrap(),ApInt::from(1u128 << 31));
            assert_eq!(ApInt::from(1u128 << 126).into_rotate_left(97).unwrap(),ApInt::from(1u128 << 95));
            assert_eq!(ApInt::from((1u128 << 2) + (1 << 126) + (1 << 66)).into_rotate_left(64).unwrap(),ApInt::from((1u128 << 66) + (1 << 62) + (1 << 2)));
            assert_eq!(ApInt::from((1u128 << 2) + (1 << 126) + (1 << 66)).into_rotate_left(33).unwrap(),ApInt::from((1u128 << 35) + (1 << 31) + (1 << 99)));
            assert_eq!(ApInt::from((1u128 << 2) + (1 << 126) + (1 << 66)).into_rotate_left(97).unwrap(),ApInt::from((1u128 << 99) + (1 << 95) + (1 << 35)));
            assert_eq!(ApInt::from(u128::MAX - 1).into_rotate_left(68).unwrap(),ApInt::from(u128::MAX - (1 << 68)));
            assert_eq!(ApInt::from([8u64,4,2]).into_rotate_left(127).unwrap(),ApInt::from([1u64,4,2]));
            assert_eq!(ApInt::from([0u64,0,2]).into_zero_resize(129).into_rotate_left(127).unwrap(),ApInt::from([1u64,0,0]).into_zero_resize(129));
            assert_eq!(ApInt::from(1u128 << 70).into_zero_resize(127).into_rotate_left(70).unwrap(),ApInt::from(1u128 << 13).into_zero_resize(127));
            assert_eq!(ApInt::from(1u128 << 126).into_zero_resize(127).into_rotate_left(70).unwrap(),ApInt::from(1u128 << 69).into_zero_resize(127));
            assert_eq!(ApInt::from(1u128 << 121).into_zero_resize(127).into_rotate_left(70).unwrap(),ApInt::from(1u128 << 64).into_zero_resize(127));
            assert_eq!(ApInt::from(1u128).into_zero_resize(127).into_rotate_left(82).unwrap(),ApInt::from(1u128 << 82).into_zero_resize(127));
            assert_eq!(ApInt::from([1u64,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]).into_rotate_left(6*64).unwrap(),ApInt::from([7u64,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6]));
        }
    }
}
