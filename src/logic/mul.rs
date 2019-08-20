use crate::data::{ApInt, Digit, DoubleDigit, ZipDataAccessMutSelf::{Inl, Ext}};
use crate::info::Result;
#[cfg(test)]
use crate::info::Width;
use crate::logic::try_forward_bin_mut_impl;

/// Multiply-assign `lhs` with `rhs` inplace. `lhs_sig_nonzero` and `rhs_sig_nonzero` indicate
/// the indexes of the most significant nonzero digits.
/// 
/// Unused bits are **not** cleared by this function.
fn digitwise_wrapping_mul(lhs: &mut [Digit], rhs: &[Digit], len: usize) {
    //wrapping (modular) multiplication
    let sig_nonzero = len - 1;
    //first digit done and carry
    let tmp = lhs[0].carrying_mul(rhs[0]);
    //the goal here with `sum` is to allocate and initialize it only once
    //here.
    //first row
    let mut sum = Vec::with_capacity(len);
    sum.push(tmp.0);
    let mut mul_carry = tmp.1;
    for rhs_i in 1..sig_nonzero {
        let tmp = lhs[0].carrying_mul_add(rhs[rhs_i], mul_carry);
        sum.push(tmp.0);
        mul_carry = tmp.1;
    }
    //final digit of first row
    sum.push(lhs[0].wrapping_mul_add(rhs[sig_nonzero], mul_carry));
    //middle rows
    for lhs_i in 1..sig_nonzero {
        //first digit of this row
        let tmp0 = lhs[lhs_i].carrying_mul(rhs[0]);
        mul_carry = tmp0.1;
        let tmp1 = sum[lhs_i].carrying_add(tmp0.0);
        //sum[lhs_i] does not need to be used again
        sum[lhs_i] = tmp1.0;
        let mut add_carry = tmp1.1;
        //as we get to the higher lhs digits, the higher rhs digits do not
        //need to be considered
        let rhs_i_upper = sig_nonzero.wrapping_sub(lhs_i);
        //middle digits of this row
        for rhs_i in 1..rhs_i_upper {
            let tmp0 = lhs[lhs_i].carrying_mul_add(rhs[rhs_i], mul_carry);
            mul_carry = tmp0.1;
            let tmp1: DoubleDigit = sum[lhs_i + rhs_i].dd()
                .wrapping_add(tmp0.0.dd())
                .wrapping_add(add_carry.dd());
            sum[lhs_i + rhs_i] = tmp1.lo();
            add_carry = tmp1.hi();
            }
        //final digit of this row
        sum[sig_nonzero] = lhs[lhs_i]
            .wrapping_mul(rhs[rhs_i_upper])
            .wrapping_add(mul_carry)
            .wrapping_add(sum[sig_nonzero])
            .wrapping_add(add_carry);
    }
    lhs[..sig_nonzero].copy_from_slice(&sum[..sig_nonzero]);
    //final digit (the only one in its row)
    lhs[sig_nonzero] = lhs[sig_nonzero]
        .wrapping_mul_add(rhs[0], sum[sig_nonzero]);
}

/// Multiply-assign `lhs` with `rhs` inplace. `lhs_sig_nonzero` and `rhs_sig_nonzero` indicate
/// the indexes of the most significant nonzero digits.
/// 
/// When calling this function, there must be no possibility of overflow of `lhs`.
///
/// Unused bits are **not** cleared by this function.
fn digitwise_nonwrapping_mul(
    lhs: &mut [Digit],
    rhs: &[Digit],
    len: usize,
    lhs_sig_nonzero: usize,
    rhs_sig_nonzero: usize
) {
    match (lhs_sig_nonzero == 0, rhs_sig_nonzero == 0) {
        (false, false) => {
            // For several routines below there was a nested loop that had its first and last
            // iterations unrolled (and the unrolled loops had their first and last iterations
            // unrolled), and then some if statements are added for digit overflow checks.
            // This is done because the compiler probably cannot properly unroll the carry
            // system, overflow system, and figure out that only `Digit` multiplications were
            // needed instead of `DoubleDigit` multiplications in some places.

            //first digit of first row
            let mult = lhs[0];
            let tmp = mult.carrying_mul(rhs[0]);
            //middle digits of first row
            //the goal here with `sum` is to allocate and initialize it only once
            //here.
            let mut sum = Vec::with_capacity(lhs_sig_nonzero + rhs_sig_nonzero + 2);
            sum.push(tmp.0);
            let mut mul_carry = tmp.1;
            for rhs_i in 1..rhs_sig_nonzero {
                let tmp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                sum.push(tmp.0);
                mul_carry = tmp.1;
            }
            let tmp = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
            sum.push(tmp.0);
            sum.push(tmp.1);
            //middle rows
            for lhs_i in 1..lhs_sig_nonzero {
                let mult = lhs[lhs_i];
                //first digit of this row
                let tmp0 = mult.carrying_mul(rhs[0]);
                let mut mul_carry = tmp0.1;
                let tmp1 = sum[lhs_i].carrying_add(tmp0.0);
                sum[lhs_i] = tmp1.0;
                let mut add_carry = tmp1.1;
                //middle digits of this row
                for rhs_i in 1..rhs_sig_nonzero {
                    let tmp0 = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                    mul_carry = tmp0.1;
                    let tmp1: DoubleDigit = sum[lhs_i + rhs_i].dd()
                        .wrapping_add(tmp0.0.dd())
                        .wrapping_add(add_carry.dd());
                    sum[lhs_i + rhs_i] = tmp1.lo();
                    add_carry = tmp1.hi();
                }
                //final digits of this row
                let tmp0 = mult.carrying_mul_add(rhs[rhs_sig_nonzero],mul_carry);
                let tmp1: DoubleDigit = sum[lhs_i + rhs_sig_nonzero].dd()
                    .wrapping_add(tmp0.0.dd())
                    .wrapping_add(add_carry.dd());
                sum[lhs_i + rhs_sig_nonzero] = tmp1.lo();
                sum.push(tmp1.hi().wrapping_add(tmp0.1));
            }
            let mult = lhs[lhs_sig_nonzero];
            //first digit of final row
            let tmp0 = mult.carrying_mul(rhs[0]);
            let mut mul_carry = tmp0.1;
            let tmp1 = sum[lhs_sig_nonzero].carrying_add(tmp0.0);
            sum[lhs_sig_nonzero] = tmp1.0;
            let mut add_carry = tmp1.1;
            //middle digits of final row
            for rhs_i in 1..rhs_sig_nonzero {
                let tmp0 = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                mul_carry = tmp0.1;
                let tmp1: DoubleDigit = sum[lhs_sig_nonzero + rhs_i].dd()
                    .wrapping_add(tmp0.0.dd())
                    .wrapping_add(add_carry.dd());
                sum[lhs_sig_nonzero + rhs_i] = tmp1.lo();
                add_carry = tmp1.hi();
            }

            // final two digits
            let tmp0 = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
            let tmp1: DoubleDigit = sum[lhs_sig_nonzero + rhs_sig_nonzero].dd()
                .wrapping_add(tmp0.0.dd())
                .wrapping_add(add_carry.dd());
            sum[lhs_sig_nonzero + rhs_sig_nonzero] = tmp1.lo();
            sum.push(tmp1.hi().wrapping_add(tmp0.1));

            if lhs.len() < sum.len() {
                lhs.copy_from_slice(&sum[..lhs.len()]);
            } else {
                lhs[..sum.len()].copy_from_slice(&sum[..]);
            }
        },
        (true, false) => {
            let mult = lhs[0];
            //first digit done and carry
            let tmp = mult.carrying_mul(rhs[0]);
            lhs[0] = tmp.0;
            let mut mul_carry = tmp.1;
            //middle of row
            for rhs_i in 1..rhs_sig_nonzero {
                let tmp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                lhs[rhs_i] = tmp.0;
                mul_carry = tmp.1;
            }
            //final digit
            if rhs_sig_nonzero == len - 1 {
                lhs[rhs_sig_nonzero] = mult
                    .wrapping_mul_add(rhs[rhs_sig_nonzero], mul_carry);
            } else {
                let tmp = mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                lhs[rhs_sig_nonzero] = tmp.0;
                lhs[rhs_sig_nonzero + 1] = tmp.1;
            }
        },
        (false, true) => {
            //first digit done and carry
            let tmp = rhs[0].carrying_mul(lhs[0]);
            lhs[0] = tmp.0;
            let mut mul_carry = tmp.1;
            //middle of row
            for lhs_i in 1..lhs_sig_nonzero {
                let tmp = rhs[0].carrying_mul_add(lhs[lhs_i], mul_carry);
                lhs[lhs_i] = tmp.0;
                mul_carry = tmp.1;
            }
            //final digit
            if lhs_sig_nonzero == len - 1 {
                lhs[lhs_sig_nonzero] = rhs[0]
                    .wrapping_mul_add(lhs[lhs_sig_nonzero], mul_carry);
            } else {
                let tmp = rhs[0].carrying_mul_add(lhs[lhs_sig_nonzero], mul_carry);
                lhs[lhs_sig_nonzero] = tmp.0;
                lhs[lhs_sig_nonzero + 1] = tmp.1;
            }
        },
        (true, true) => {
            let tmp0 = lhs[0].carrying_mul(rhs[0]);
            lhs[0] = tmp0.0;
            lhs[1] = tmp0.1;
        }
    }
}

/// # Multiplication Operations
/// 
/// **Note**: unless otherwise noted in the function specific documentation,
/// 
/// - **An Error is returned** if function arguments have unmatching bitwidths.
/// - The functions **may allocate** memory.
/// - The function works for both signed and unsigned interpretations of an `ApInt`. In other words,
///   in the low-level bit-wise representation there is no difference between a signed and unsigned
///   operation by a certain function on fixed bit-width integers. (Cite: LLVM)
/// 
/// ## Performance
/// 
/// All of the multiplication functions in this `impl` quickly check for various edge cases and use
/// an efficient algorithm for these cases. If the function detects a large number of leading zeros
/// in front of the most significant set bit, it will apply optimizations so that wasted
/// multiplications and additions of zero are avoided. This function is designed to efficiently
/// handle 5 common kinds of multiplication.
/// Small here means both small ApInt `BitWidth` and/or small **unsigned** numerical
/// significance. (Signed multiplication works, but two's complement negative numbers may have a
/// large number of leading ones, leading to potential inefficiency.)
/// 
/// - multiplication of zero by any size integer (no allocation)
/// - multiplication of small (<= 1 `Digit`) integers (no allocation)
/// - multiplication of small integers by large integers (or vice versa) (no allocation)
/// - wrapping multiplication of medium size (<= 512 bits) integers
/// - multiplication of medium size integers that will not overflow
/// 
/// Currently, Karatsuba multiplication is not implemented, so large integer multiplication 
/// may be very slow compared to other algorithms. According to Wikipedia, Karatsuba algorithms
/// outperform 𝒪(n^2) algorithms, starting around 320-640 bits
impl ApInt {
    /// Multiply-assigns `rhs` to `self` inplace.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    pub fn wrapping_mul_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_mul(rhs);
            }
            Ext(lhs, rhs) => {
                let len = rhs.len();
                //finds the most significant nonzero digit (for later optimizations) and handles
                //early return of multiplication by zero.
                let rhs_sig_nonzero: usize = match rhs.iter().rposition(|x| x != &Digit::zero()) {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(());
                    }
                };
                let lhs_sig_nonzero: usize = match lhs.iter().rposition(|x| x != &Digit::zero()) {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(());
                    }
                };
                let lhs_sig_bits = (lhs_sig_nonzero * Digit::BITS)
                    + (Digit::BITS - (lhs[lhs_sig_nonzero].leading_zeros() as usize));
                let rhs_sig_bits = (rhs_sig_nonzero * Digit::BITS)
                    + (Digit::BITS - (rhs[rhs_sig_nonzero].leading_zeros() as usize));
                let tot_sig_bits = lhs_sig_bits + rhs_sig_bits;
                if tot_sig_bits <= (len * Digit::BITS) {
                    digitwise_nonwrapping_mul(lhs, rhs, len, lhs_sig_nonzero, rhs_sig_nonzero);
                } else {
                    digitwise_wrapping_mul(lhs, rhs, len);
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Multiplies `rhs` with `self` and returns the result.
    pub fn into_wrapping_mul(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_mul_assign)
    }

    /// Multiply-assigns `rhs` to `self` inplace, and returns a boolean indicating if overflow
    /// occured, according to the **unsigned** interpretation of overflow.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bitwidths.
    #[cfg(test)]
    pub(crate) fn overflowing_umul_assign(&mut self, rhs: &ApInt) -> Result<bool> {
        let mask = Digit::ONES >> rhs.width().unused_bits();
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                let tmp = lhs.overflowing_mul(rhs);
                // clear unused bits
                *lhs = tmp.0 & mask;
                Ok(tmp.1 || ((tmp.0 & mask) != tmp.0))
            }
            Ext(lhs, rhs) => {
                let len = rhs.len();
                let rhs_sig_nonzero: usize = match rhs.iter().rposition(|x| x != &Digit::zero()) {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(false);
                    }
                };
                let lhs_sig_nonzero: usize = match lhs.iter().rposition(|x| x != &Digit::zero()) {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(false);
                    }
                };
                let lhs_sig_bits = (lhs_sig_nonzero * Digit::BITS)
                    + (Digit::BITS - (lhs[lhs_sig_nonzero].leading_zeros() as usize));
                let rhs_sig_bits = (rhs_sig_nonzero * Digit::BITS)
                    + (Digit::BITS - (rhs[rhs_sig_nonzero].leading_zeros() as usize));
                let tot_sig_bits = lhs_sig_bits + rhs_sig_bits;
                // The smallest that `lhs` and `rhs` can be is `2^(lhs_sig_bits - 1)` and
                // `2^(rhs_sig_bits - 1)`, respectively. This represents the most significant set
                // bit being the only set bit. The largest that `lhs` and `rhs` can be is
                // `2^lhs_sig_bits - 1` and `2^rhs_sig_bits - 1`, respectively, which represents
                // all bits up to the most significant set bit being set.
                // The extreme values are:
                // 2^(lhs_sig_bits - 1) * 2^(rhs_sig_bits - 1) = 2^(tot_sig_bits - 2),
                // (2^lhs_sig_bits - 1) * (2^rhs_sig_bits - 1) =
                // 2^tot_sig_bits - 2^lhs_sig_bits - 2^rhs_sig_bits + 1
                // `lhs_sig_bits` and `rhs_sig_bits` are at least 1, so the bounds can be slightly
                // expanded to `2^(tot_sig_bits - 2) <= result < 2^tot_sig_bits`.
                // If `tot_sig_bits` is `len * Digit::BITS`, then the result must fit in the
                // digitwise representation (`result < 2^bit_len`). For `2^(tot_sig_bits - 2)` to be
                // equal to `2^bit_len`, which guarantees overflow, `tot_sig_bits` must be
                // `len * Digit::BITS + 2` or more.
                if tot_sig_bits <= (len * Digit::BITS) {
                    digitwise_nonwrapping_mul(lhs, rhs, len, lhs_sig_nonzero, rhs_sig_nonzero);
                    // test for overflow into the unused bits
                    let tmp = lhs[len - 1] & mask;
                    let overflow = tmp != lhs[len - 1];
                    // clear unused bits
                    lhs[len - 1] = tmp;
                    Ok(overflow)
                } else if tot_sig_bits >= (len * Digit::BITS) + 2 {
                    digitwise_wrapping_mul(lhs, rhs, len);
                    lhs[len - 1] = lhs[len - 1] & mask;
                    Ok(true)
                } else {
                    let mut sum: Vec<Digit> = vec![Digit::ZERO; len];
                    let mut overflow = false;
                    for lhs_i in 0..len {
                        let mut add_carry = Digit::ZERO;
                        let mut mul_carry = Digit::ZERO;
                        for rhs_i in 0..(len - lhs_i - 1) {
                            let mul_tmp = lhs[lhs_i].carrying_mul_add(rhs[rhs_i], mul_carry);
                            let add_tmp = sum[lhs_i + rhs_i].dd()
                                .wrapping_add(mul_tmp.0.dd())
                                .wrapping_add(add_carry.dd()).lo_hi();
                            sum[lhs_i + rhs_i] = add_tmp.0;
                            add_carry = add_tmp.1;
                            mul_carry = mul_tmp.1;
                        }
                        // take out the last iteration to test for nonzeroed bits
                        let mul_tmp = lhs[lhs_i].carrying_mul_add(rhs[len - lhs_i - 1], mul_carry);
                        let add_tmp = sum[len - 1].dd()
                            .wrapping_add(mul_tmp.0.dd())
                            .wrapping_add(add_carry.dd()).lo_hi();
                        if lhs_i != 0 && lhs[lhs_i] != Digit::ZERO {
                            // In normal wrapping multiplication, we know that multiplying certain
                            // digits will always overflow and have no affect on `sum` (the
                            // `len - lhs_i - 1` bound excludes these), however we must check if
                            // bits are set there. Only one digit needs to be checked due to the 2
                            // bit `tot_sig_bit` range where this branch occurs.
                            if rhs[len - lhs_i] != Digit::ZERO {
                                overflow = true;
                            }
                        }
                        // clear unused bits
                        sum[len - 1] = add_tmp.0 & mask;
                        if mul_tmp.1 != Digit::ZERO
                            || add_tmp.1 != Digit::ZERO
                            || (add_tmp.0 & mask) != add_tmp.0 {
                            overflow = true;
                        }
                    }
                    lhs[..].copy_from_slice(&sum[..]);
                    Ok(overflow)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{u8,u64};
    use crate::info::BitWidth;

    #[test]
    fn wrapping_nine_test() {
        //there are many special case and size optimization paths, so this test must be very
        //rigorous.

        //multiplication of apints composed of only u8::MAX in their least significant digits
        //only works for num_u8 > 1
        fn nine_test(num_u8: usize) {
            let mut lhs;
            let mut rhs = ApInt::from(0u8).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
            let nine =
                ApInt::from(u8::MAX).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
            for rhs_nine in 0..num_u8 {
                rhs.wrapping_shl_assign(8usize).unwrap();
                rhs |= &nine;
                lhs = ApInt::from(0u8).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
                'outer: for lhs_nine in 0..num_u8 {
                    lhs.wrapping_shl_assign(8usize).unwrap();
                    lhs |= &nine;
                    //imagine multiplying a string of base 10 nines together.
                    //It will produce things like 998001, 8991, 98901, 9989001.
                    //this uses a formula for the number of nines, eights, and zeros except here
                    //nine is u8::MAX, eight is u8::MAX - 1, and zero is 0u8
                    let zeros_after_one = if lhs_nine < rhs_nine {
                        lhs_nine
                    } else {
                        rhs_nine
                    };
                    let nines_before_eight = if lhs_nine > rhs_nine {
                        lhs_nine - rhs_nine
                    } else {
                        rhs_nine - lhs_nine
                    };
                    let nines_after_eight = if lhs_nine < rhs_nine {
                        lhs_nine
                    } else {
                        rhs_nine
                    };
                    let mut result = lhs.clone().into_wrapping_mul(&rhs).unwrap();
                    assert_eq!(result.clone().resize_to_u8(), 1u8);
                    for i in 0..zeros_after_one {
                        if i >= num_u8 - 1 {
                            continue 'outer
                        }
                        result.wrapping_lshr_assign(8usize).unwrap();
                        assert_eq!(result.clone().resize_to_u8(),0);
                    }
                    for i in 0..nines_before_eight {
                        if zeros_after_one + i >= num_u8 - 1 {
                            continue 'outer
                        }
                        result.wrapping_lshr_assign(8usize).unwrap();
                        assert_eq!(result.clone().resize_to_u8(), u8::MAX);
                    }
                    if zeros_after_one + nines_before_eight >= num_u8 - 1 {
                        continue 'outer
                    }
                    result.wrapping_lshr_assign(8usize).unwrap();
                    assert_eq!(result.clone().resize_to_u8(),u8::MAX - 1);
                    for i in 0..nines_after_eight {
                        if 1 + zeros_after_one + nines_before_eight + i >= num_u8 - 1 {
                            continue 'outer
                        }
                        result.wrapping_lshr_assign(8usize).unwrap();
                        assert_eq!(result.clone().resize_to_u8(),u8::MAX);
                    }
                }
            }
        }
        //test inl apints
        assert_eq!(
            ApInt::from(u8::MAX)
                .into_wrapping_mul(&ApInt::from(u8::MAX))
                .unwrap(),
            ApInt::from(1u8)
        );
        nine_test(2);
        nine_test(3);
        nine_test(4);
        nine_test(7);
        nine_test(8);
        //test ext apints
        nine_test(9);
        nine_test(16);
        nine_test(24);
        nine_test(32);
        //5 digits wide
        nine_test(40);
        nine_test(63);
    }

    #[test]
    fn wrapping_hardcoded() {
        //non overflowing test
        let resize = [
            7usize, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 137, 200, 255,
            256, 700, 907, 1024, 2018, 2019,
        ];
        let lhs_shl = [
            0usize, 1, 0, 1, 4, 7, 4, 10, 13, 0, 31, 25, 7, 17, 32, 50, 0, 64, 249, 8, 777, 0,
            1000, 0,
        ];
        let rhs_shl = [
            0usize, 0, 1, 1, 3, 6, 4, 14, 10, 0, 0, 25, 0, 18, 32, 49, 100, 64, 0, 256, 64,
            900, 1000, 0,
        ];
        for (i, _) in resize.iter().enumerate() {
            let lhs = ApInt::from(5u8)
                .into_zero_resize(BitWidth::new(resize[i]).unwrap())
                .into_wrapping_shl(lhs_shl[i])
                .unwrap();
            let rhs = ApInt::from(11u8)
                .into_zero_resize(BitWidth::new(resize[i]).unwrap())
                .into_wrapping_shl(rhs_shl[i])
                .unwrap();
            let zero = ApInt::from(0u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
            let one = ApInt::from(1u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
            let expected = ApInt::from(55u8)
                .into_zero_resize(BitWidth::new(resize[i]).unwrap())
                .into_wrapping_shl(rhs_shl[i] + lhs_shl[i])
                .unwrap();
            assert_eq!(lhs.clone().into_wrapping_mul(&zero).unwrap(), zero);
            assert_eq!(zero.clone().into_wrapping_mul(&rhs).unwrap(), zero);
            assert_eq!(lhs.clone().into_wrapping_mul(&one).unwrap(), lhs);
            assert_eq!(one.clone().into_wrapping_mul(&rhs).unwrap(), rhs);
            assert_eq!(lhs.clone().into_wrapping_mul(&rhs).unwrap(), expected);
        }
        assert_eq!(
            ApInt::from([0,0,0,0,u64::MAX,0,u64::MAX,u64::MAX])
                .into_wrapping_mul(&ApInt::from([0,0,0,0,u64::MAX,u64::MAX,0,u64::MAX])).unwrap()
            ,ApInt::from([u64::MAX,0,1,u64::MAX - 3,1,u64::MAX,u64::MAX,1]));
    }

    #[test]
    fn overflowing() {
        // more rigorous testing is done in `fuzz.rs`
        let bw = BitWidth::new(65).unwrap();
        let mut lhs = ApInt::from(1u128 << 64).into_zero_resize(bw);
        let rhs = lhs.clone();
        assert!(lhs.overflowing_umul_assign(&rhs).unwrap());
        let mut lhs = ApInt::from(1u128 << 64).into_zero_resize(bw);
        let rhs = ApInt::unsigned_max_value(bw);
        assert!(lhs.overflowing_umul_assign(&rhs).unwrap());
        let mut lhs = ApInt::from((u64::MAX as u128) << 64);
        let rhs = ApInt::one(BitWidth::w128());
        assert!(!lhs.overflowing_umul_assign(&rhs).unwrap());
        let mut lhs = ApInt::one(BitWidth::w128());
        let rhs = ApInt::from((u64::MAX as u128) << 64);
        assert!(!lhs.overflowing_umul_assign(&rhs).unwrap());
    }
}
