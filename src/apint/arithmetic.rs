use crate::{
    apint::utils::{
        DataAccessMut,
        ZipDataAccessMutBoth,
        ZipDataAccessMutSelf::{
            Ext,
            Inl,
        },
    },
    errors::DivOp,
    mem::{
        vec,
        vec::Vec,
    },
    utils::{
        forward_mut_impl,
        try_forward_bin_mut_impl,
    },
    ApInt,
    Digit,
    DoubleDigit,
    Error,
    Result,
    Width,
};

/// # Basic Arithmetic Operations
///
/// **Note**: unless otherwise noted in the function specific documentation,
///
/// - The functions do **not** allocate memory.
/// - The function works for both signed and unsigned interpretations of an
///   `ApInt`. In other words, in the low-level bit-wise representation there is
///   no difference between a signed and unsigned operation by a certain
///   function on fixed bit-width integers. (Cite: LLVM)
impl ApInt {
    /// Increments this `ApInt` by one inplace.
    pub fn wrapping_inc(&mut self) {
        match self.access_data_mut() {
            DataAccessMut::Inl(x) => {
                *x = x.wrapping_add(Digit::ONE);
            }
            DataAccessMut::Ext(x) => {
                for i in 0..x.len() {
                    match x[i].overflowing_add(Digit::ONE) {
                        (v, false) => {
                            x[i] = v;
                            break
                        }
                        (v, true) => {
                            // if the ApInt was relatively random this should rarely
                            // happen
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
                *x = x.wrapping_sub(Digit::ONE);
            }
            DataAccessMut::Ext(x) => {
                for i in 0..x.len() {
                    match x[i].overflowing_sub(Digit::ONE) {
                        (v, false) => {
                            x[i] = v;
                            break
                        }
                        (v, true) => {
                            // if the ApInt was relatively random this should rarely
                            // happen
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
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_add_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_add(rhs);
            }
            Ext(lhs, rhs) => {
                let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                lhs[0] = temp;
                for i in 1..lhs.len() {
                    let temp = lhs[i]
                        .dd()
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
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_add(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_add_assign)
    }

    /// Add-assigns `rhs` to `self` inplace, and returns a boolean indicating if
    /// overflow occured, according to the **unsigned** interpretation of
    /// overflow.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    // TODO: add tests
    #[allow(dead_code)]
    pub(crate) fn overflowing_uadd_assign(&mut self, rhs: &ApInt) -> Result<bool> {
        match self.width().excess_bits() {
            Some(excess) => {
                let mask = Digit::ONES >> excess;
                match self.zip_access_data_mut_self(rhs)? {
                    Inl(lhs, rhs) => {
                        let temp = lhs.wrapping_add(rhs);
                        *lhs = temp & mask;
                        // excess bits are cleared by the mask
                        Ok((temp & mask) != temp)
                    }
                    Ext(lhs, rhs) => {
                        let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                        lhs[0] = temp;
                        for i in 1..(lhs.len() - 1) {
                            let temp = lhs[i]
                                .dd()
                                .wrapping_add(rhs[i].dd())
                                .wrapping_add(carry.dd());
                            lhs[i] = temp.lo();
                            carry = temp.hi();
                        }
                        let temp = lhs[lhs.len() - 1]
                            .wrapping_add(rhs[lhs.len() - 1])
                            .wrapping_add(carry);
                        lhs[lhs.len() - 1] = temp & mask;
                        // excess bits are cleared by the mask
                        Ok((temp & mask) != temp)
                    }
                }
            }
            None => {
                match self.zip_access_data_mut_self(rhs)? {
                    Inl(lhs, rhs) => {
                        let temp = lhs.overflowing_add(rhs);
                        *lhs = temp.0;
                        // no excess bits to clear
                        Ok(temp.1)
                    }
                    Ext(lhs, rhs) => {
                        let (temp, mut carry) = lhs[0].carrying_add(rhs[0]);
                        lhs[0] = temp;
                        for i in 1..lhs.len() {
                            let temp = lhs[i]
                                .dd()
                                .wrapping_add(rhs[i].dd())
                                .wrapping_add(carry.dd());
                            lhs[i] = temp.lo();
                            carry = temp.hi();
                        }
                        // no excess bits to clear
                        Ok(!carry.is_zero())
                    }
                }
            }
        }
    }

    /// Add-assigns `rhs` to `self` inplace, and returns a boolean indicating if
    /// overflow occured, according to the **signed** interpretation of
    /// overflow.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    // TODO: add tests
    #[allow(dead_code)]
    pub(crate) fn overflowing_sadd_assign(&mut self, rhs: &ApInt) -> Result<bool> {
        let self_sign = self.msb();
        let rhs_sign = rhs.msb();
        self.wrapping_add_assign(rhs)?;
        Ok((self_sign == rhs_sign) && (self_sign != self.msb()))
    }

    /// Subtract-assigns `rhs` from `self` inplace.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn wrapping_sub_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_sub(rhs);
            }
            Ext(lhs, rhs) => {
                let (temp, mut carry) = lhs[0]
                    .dd()
                    .wrapping_add((!rhs[0]).dd())
                    .wrapping_add(Digit::ONE.dd())
                    .lo_hi();
                lhs[0] = temp;
                for i in 1..lhs.len() {
                    let temp = lhs[i]
                        .dd()
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
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_sub(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sub_assign)
    }

    /// Multiply-assigns `rhs` to `self` inplace. This function **may** allocate
    /// memory.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    ///
    /// # Performance
    ///
    /// If the function detects a large number of leading zeros in front of the
    /// most significant 1 bit, it will apply optimizations so that wasted
    /// multiplications and additions of zero are avoided. This function is
    /// designed to efficiently handle 5 common kinds of multiplication.
    /// Small here means both small ApInt `BitWidth` and/or small **unsigned**
    /// numerical significance. (Signed multiplication works, but two's
    /// complement negative numbers may have a large number of leading ones,
    /// leading to potential inefficiency.)
    ///
    /// - multiplication of zero by any size integer (no allocation)
    /// - multiplication of small (<= 1 `Digit`) integers (no allocation)
    /// - wrapping multiplication of medium size (<= 512 bits) integers
    /// - multiplication of medium size integers that will not overflow
    /// - multiplication of small integers by large integers (or large integers
    ///   multiplied by small integers) (no allocation)
    ///
    /// Currently, Karatsuba multiplication is not implemented, so large integer
    /// multiplication may be very slow compared to other algorithms.
    /// According to Wikipedia, Karatsuba algorithms outperform 𝒪(n^2)
    /// algorithms, starting around 320-640 bits.
    pub fn wrapping_mul_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(lhs, rhs) => {
                *lhs = lhs.wrapping_mul(rhs);
            }
            Ext(lhs, rhs) => {
                // finds the most significant nonzero digit (for later optimizations) and
                // handles early return of multiplication by zero.
                let rhs_sig_nonzero: usize = match rhs.iter().rposition(|x| !x.is_zero())
                {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(())
                    }
                };
                let lhs_sig_nonzero: usize = match lhs.iter().rposition(|x| !x.is_zero())
                {
                    Some(x) => x,
                    None => {
                        for x in lhs.iter_mut() {
                            x.unset_all()
                        }
                        return Ok(())
                    }
                };
                // for several routines below there was a nested loop that had its first
                // and last iterations unrolled (and the unrolled loops
                // had their first and last iterations unrolled), and then
                // some if statements are added for digit overflow checks.
                // This is done because the compiler probably cannot properly unroll the
                // carry system, overflow system, and figure out that only
                // `Digit` multiplications were needed instead of
                // `DoubleDigit` multiplications in some places.
                match (lhs_sig_nonzero == 0, rhs_sig_nonzero == 0) {
                    (false, false) => {
                        let lhs_sig_bits = (lhs_sig_nonzero * Digit::BITS)
                            + (Digit::BITS
                                - (lhs[lhs_sig_nonzero].leading_zeros() as usize));
                        let rhs_sig_bits = (rhs_sig_nonzero * Digit::BITS)
                            + (Digit::BITS
                                - (rhs[rhs_sig_nonzero].leading_zeros() as usize));
                        let tot_sig_bits = lhs_sig_bits + rhs_sig_bits;
                        if tot_sig_bits <= (lhs.len() * Digit::BITS) {
                            // No possibility of `Digit` wise overflow. Note that end bits
                            // still have to be trimmed for
                            // `ApInt`s with a width that is not a multiple of
                            //`Digit`s.
                            // first digit of first row
                            let mult = lhs[0];
                            let temp = mult.carrying_mul(rhs[0]);
                            // middle digits of first row
                            // the goal here with `sum` is to allocate and initialize it
                            // only once here.
                            let mut sum =
                                Vec::with_capacity(lhs_sig_nonzero + rhs_sig_nonzero + 2);
                            sum.push(temp.0);
                            let mut mul_carry = temp.1;
                            for rhs_i in 1..rhs_sig_nonzero {
                                let temp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                                sum.push(temp.0);
                                mul_carry = temp.1;
                            }
                            let temp =
                                mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                            sum.push(temp.0);
                            sum.push(temp.1);
                            // middle rows
                            for lhs_i in 1..lhs_sig_nonzero {
                                let mult = lhs[lhs_i];
                                // first digit of this row
                                let temp0 = mult.carrying_mul(rhs[0]);
                                let mut mul_carry = temp0.1;
                                let temp1 = sum[lhs_i].carrying_add(temp0.0);
                                sum[lhs_i] = temp1.0;
                                let mut add_carry = temp1.1;
                                // middle digits of this row
                                for rhs_i in 1..rhs_sig_nonzero {
                                    let temp0 =
                                        mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                                    mul_carry = temp0.1;
                                    let temp1: DoubleDigit = sum[lhs_i + rhs_i]
                                        .dd()
                                        .wrapping_add(temp0.0.dd())
                                        .wrapping_add(add_carry.dd());
                                    sum[lhs_i + rhs_i] = temp1.lo();
                                    add_carry = temp1.hi();
                                }
                                // final digits of this row
                                let temp0 = mult
                                    .carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                                let temp1: DoubleDigit = sum[lhs_i + rhs_sig_nonzero]
                                    .dd()
                                    .wrapping_add(temp0.0.dd())
                                    .wrapping_add(add_carry.dd());
                                sum[lhs_i + rhs_sig_nonzero] = temp1.lo();
                                sum.push(temp1.hi().wrapping_add(temp0.1));
                            }
                            let mult = lhs[lhs_sig_nonzero];
                            // first digit of final row
                            let temp0 = mult.carrying_mul(rhs[0]);
                            let mut mul_carry = temp0.1;
                            let temp1 = sum[lhs_sig_nonzero].carrying_add(temp0.0);
                            sum[lhs_sig_nonzero] = temp1.0;
                            let mut add_carry = temp1.1;
                            // middle digits of final row
                            for rhs_i in 1..rhs_sig_nonzero {
                                let temp0 = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                                mul_carry = temp0.1;
                                let temp1: DoubleDigit = sum[lhs_sig_nonzero + rhs_i]
                                    .dd()
                                    .wrapping_add(temp0.0.dd())
                                    .wrapping_add(add_carry.dd());
                                sum[lhs_sig_nonzero + rhs_i] = temp1.lo();
                                add_carry = temp1.hi();
                            }
                            let temp0 =
                                mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                            let temp1: DoubleDigit = sum
                                [lhs_sig_nonzero + rhs_sig_nonzero]
                                .dd()
                                .wrapping_add(temp0.0.dd())
                                .wrapping_add(add_carry.dd());
                            sum[lhs_sig_nonzero + rhs_sig_nonzero] = temp1.lo();
                            sum.push(temp1.hi().wrapping_add(temp0.1));
                            if lhs.len() < sum.len() {
                                for i in 0..lhs.len() {
                                    lhs[i] = sum[i];
                                }
                            } else {
                                for i in 0..sum.len() {
                                    lhs[i] = sum[i];
                                }
                            }
                        } else {
                            // wrapping (modular) multiplication
                            let sig_nonzero = lhs.len() - 1;
                            // first digit done and carry
                            let temp = lhs[0].carrying_mul(rhs[0]);
                            // the goal here with `sum` is to allocate and initialize it
                            // only once here.
                            // first row
                            let mut sum = Vec::with_capacity(lhs.len());
                            sum.push(temp.0);
                            let mut mul_carry = temp.1;
                            for rhs_i in 1..sig_nonzero {
                                let temp = lhs[0].carrying_mul_add(rhs[rhs_i], mul_carry);
                                sum.push(temp.0);
                                mul_carry = temp.1;
                            }
                            // final digit of first row
                            sum.push(
                                lhs[0].wrapping_mul_add(rhs[sig_nonzero], mul_carry),
                            );
                            // middle rows
                            for lhs_i in 1..sig_nonzero {
                                // first digit of this row
                                let temp0 = lhs[lhs_i].carrying_mul(rhs[0]);
                                mul_carry = temp0.1;
                                let temp1 = sum[lhs_i].carrying_add(temp0.0);
                                // sum[lhs_i] does not need to be used again
                                sum[lhs_i] = temp1.0;
                                let mut add_carry = temp1.1;
                                // as we get to the higher lhs digits, the higher rhs
                                // digits do not
                                // need to be considered
                                let rhs_i_upper = sig_nonzero.wrapping_sub(lhs_i);
                                // middle digits of this row
                                for rhs_i in 1..rhs_i_upper {
                                    let temp0 = lhs[lhs_i]
                                        .carrying_mul_add(rhs[rhs_i], mul_carry);
                                    mul_carry = temp0.1;
                                    let temp1: DoubleDigit = sum[lhs_i + rhs_i]
                                        .dd()
                                        .wrapping_add(temp0.0.dd())
                                        .wrapping_add(add_carry.dd());
                                    sum[lhs_i + rhs_i] = temp1.lo();
                                    add_carry = temp1.hi();
                                }
                                // final digit of this row
                                sum[sig_nonzero] = lhs[lhs_i]
                                    .wrapping_mul(rhs[rhs_i_upper])
                                    .wrapping_add(mul_carry)
                                    .wrapping_add(sum[sig_nonzero])
                                    .wrapping_add(add_carry);
                            }
                            for i in 0..sig_nonzero {
                                lhs[i] = sum[i];
                            }
                            // final digit (the only one in its row)
                            lhs[sig_nonzero] = lhs[sig_nonzero]
                                .wrapping_mul_add(rhs[0], sum[sig_nonzero]);
                        }
                    }
                    (true, false) => {
                        let mult = lhs[0];
                        // first digit done and carry
                        let temp = mult.carrying_mul(rhs[0]);
                        lhs[0] = temp.0;
                        let mut mul_carry = temp.1;
                        // middle of row
                        for rhs_i in 1..rhs_sig_nonzero {
                            let temp = mult.carrying_mul_add(rhs[rhs_i], mul_carry);
                            lhs[rhs_i] = temp.0;
                            mul_carry = temp.1;
                        }
                        // final digit
                        if rhs_sig_nonzero == lhs.len() - 1 {
                            lhs[rhs_sig_nonzero] =
                                mult.wrapping_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                        } else {
                            let temp =
                                mult.carrying_mul_add(rhs[rhs_sig_nonzero], mul_carry);
                            lhs[rhs_sig_nonzero] = temp.0;
                            lhs[rhs_sig_nonzero + 1] = temp.1;
                        }
                    }
                    (false, true) => {
                        // first digit done and carry
                        let temp = rhs[0].carrying_mul(lhs[0]);
                        lhs[0] = temp.0;
                        let mut mul_carry = temp.1;
                        // middle of row
                        for lhs_i in 1..lhs_sig_nonzero {
                            let temp = rhs[0].carrying_mul_add(lhs[lhs_i], mul_carry);
                            lhs[lhs_i] = temp.0;
                            mul_carry = temp.1;
                        }
                        // final digit
                        if lhs_sig_nonzero == lhs.len() - 1 {
                            lhs[lhs_sig_nonzero] =
                                rhs[0].wrapping_mul_add(lhs[lhs_sig_nonzero], mul_carry);
                        } else {
                            let temp =
                                rhs[0].carrying_mul_add(lhs[lhs_sig_nonzero], mul_carry);
                            lhs[lhs_sig_nonzero] = temp.0;
                            lhs[lhs_sig_nonzero + 1] = temp.1;
                        }
                    }
                    (true, true) => {
                        let temp0 = lhs[0].carrying_mul(rhs[0]);
                        lhs[0] = temp0.0;
                        lhs[1] = temp0.1;
                    }
                }
            }
        }
        self.clear_unused_bits();
        Ok(())
    }

    /// Multiplies `rhs` with `self` and returns the result. This function
    /// **may** allocate memory. Note: see `wrapping_mul_assign` for more
    /// information.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    pub fn into_wrapping_mul(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_mul_assign)
    }
}

/// # Division Operations
///
/// **Note**: unless otherwise noted in the function specific documentation,
///
/// - The functions do **not** allocate memory.
/// - The function works for both signed and unsigned interpretations of an
///   `ApInt`. In other words, in the low-level bit-wise representation there is
///   no difference between a signed and unsigned operation by the function on
///   fixed bit-width integers. (Cite: LLVM)
///
/// In almost all integer division algorithms where "just" the quotient is
/// calculated, the remainder is also produced and actually exists in memory (or
/// at least is only one O(n) operation away) prior to being dropped or
/// overwritten, and vice versa for remainder only calculations. Note here
/// that functions with `div` in their names (e.g. `wrapping_div`) should really
/// be called `quo` (quotient) functions, because the division process produces
/// both the quotient and remainder. However, to stay with Rust's naming scheme
/// we have kept `div` naming. The instruction for division on many CPUs sets
/// registers to both results of the division process, and compilers will detect
/// if code uses both results and only use one division instruction. There is no
/// such detection for `ApInt`s, and thus the `divrem` and `remdiv` type
/// instructions exist to explicitly use just one division function for both
/// results.
///
/// ## Performance
///
/// All of the division functions in this `impl` quickly check for various edge
/// cases and use an efficient algorithm for these cases.
/// Small here means both small ApInt `BitWidth` and/or small **unsigned**
/// numerical significance. (Signed division works, but two's complement
/// negative numbers may have a large number of leading ones, leading to
/// potential inefficiency.)
///
/// - division of zero by any size integer (no allocation)
/// - division of small (1 `Digit`) integers (no allocation)
/// - any division that will lead to the quotient being zero or one (no
///   allocation)
/// - division of any integer by small (1 `Digit`) very small (0.5 `Digit`)
///   integers (no allocation)
/// - division where the number of leading zeros of both arguments are within
///   one `Digit` (less allocation than what long division normally requires)
/// - during long division, the algorithm may encounter a case from above and
///   will use that instead
/// - division of medium size (<= 512 bits) integers
///
/// Currently, algorithms faster than 𝒪(n^2) are not implemented, so large
/// integer division may be very slow compared to other algorithms.
impl ApInt {
    // Note: the invariant of `ApInt`s where unused bits beyond the bit width must
    // be all zero is used heavily here, so that no `clear_unused_bits` needs to
    // be used.

    /// This function is intended to be inlined into all of the unsigned
    /// quotient and remainder functions for optimal assembly.
    /// `duo` is divided by `div`, and the quotient is assigned to `duo` and
    /// remainder assigned to `div`
    /// `false` is returned if division by zero happened. Nothing is modified in
    /// the case of division by zero.
    #[inline]
    pub(crate) fn aarons_algorithm_divrem(duo: &mut [Digit], div: &mut [Digit]) -> bool {
        // Some parts were put into their own functions and macros because indentation
        // levels were getting too high, even for me.

        // The algorithm here is just like the algorithm in
        // https://github.com/AaronKutch/specialized-div-rem,
        // except that there are more branches and preconditions. There are comments in
        // this function such as  `//quotient is 0 or 1 check` which correspond
        // to comments in that function.

        // assumptions:
        //  *ini_duo_sd > 0
        //  *div_sd == 0
        // modifies `duo` to produce the quotient and returns the remainder
        #[inline(always)]
        fn large_div_by_small(duo: &mut [Digit], ini_duo_sd: usize, div: &mut [Digit]) {
            let div_small = div[0];
            let (mut quo, mut rem) = duo[ini_duo_sd].wrapping_divrem(div_small);
            duo[ini_duo_sd] = quo;
            for duo_sd_sub1 in (0..ini_duo_sd).rev() {
                let duo_double = DoubleDigit::from_lo_hi(duo[duo_sd_sub1], rem);
                let temp = duo_double.wrapping_divrem(div_small.dd());
                // the high part is guaranteed to zero out when this is subtracted,
                // so only the low parts need to be calculated
                quo = temp.0.lo();
                rem = temp.1.lo();
                duo[duo_sd_sub1] = quo;
            }
            div[0] = rem;
        }

        // assumptions:
        //  *ini_duo_sd > 0
        //  *div_sd == 0
        //  *div[0].leading_zeros >= 32
        #[inline(always)]
        fn large_div_by_u32(duo: &mut [Digit], ini_duo_sd: usize, div: &mut [Digit]) {
            let div_u32 = div[0].repr() as u32;
            #[inline(always)]
            fn dd(x: u32) -> Digit {
                Digit(u64::from(x))
            }
            #[inline(always)]
            fn lo(x: Digit) -> u32 {
                x.repr() as u32
            }
            #[inline(always)]
            fn hi(x: Digit) -> u32 {
                (x.repr() >> 32) as u32
            }
            #[inline(always)]
            fn from_lo_hi(lo: u32, hi: u32) -> Digit {
                Digit(u64::from(lo) | (u64::from(hi) << 32))
            }
            #[inline(always)]
            fn wrapping_divrem(x: u32, y: u32) -> (u32, u32) {
                (x.wrapping_div(y), x.wrapping_rem(y))
            }
            let (mut quo_hi, mut rem_hi) = wrapping_divrem(hi(duo[ini_duo_sd]), div_u32);
            let duo_double = from_lo_hi(lo(duo[ini_duo_sd]), rem_hi);
            let temp = duo_double.wrapping_divrem(dd(div_u32));
            let mut quo_lo = lo(temp.0);
            let mut rem_lo = lo(temp.1);
            duo[ini_duo_sd] = from_lo_hi(quo_lo, quo_hi);
            for duo_sd_sub1 in (0..ini_duo_sd).rev() {
                let duo_double_hi = from_lo_hi(hi(duo[duo_sd_sub1]), rem_lo);
                let temp_hi = duo_double_hi.wrapping_divrem(dd(div_u32));
                quo_hi = lo(temp_hi.0);
                rem_hi = lo(temp_hi.1);
                let duo_double_lo = from_lo_hi(lo(duo[duo_sd_sub1]), rem_hi);
                let temp_lo = duo_double_lo.wrapping_divrem(dd(div_u32));
                quo_lo = lo(temp_lo.0);
                rem_lo = lo(temp_lo.1);
                duo[duo_sd_sub1] = from_lo_hi(quo_lo, quo_hi);
            }
            div[0] = Digit(u64::from(rem_lo));
        }

        // modifies the `$array` to be the two's complement of itself, all the way up to
        // a `$len` number of digits.
        macro_rules! twos_complement {
            ($len:expr, $array:ident) => {
                for i0 in 0..$len {
                    let bitnot = !$array[i0];
                    match bitnot.overflowing_add(Digit::ONE) {
                        (v, false) => {
                            $array[i0] = v;
                            for i1 in (i0 + 1)..$len {
                                $array[i1] = !$array[i1]
                            }
                            break
                        }
                        (v, true) => {
                            $array[i0] = v;
                        }
                    }
                }
            };
        }

        // uge stands for "unsigned greater or equal to"
        // This checks for `$lhs >= $rhs` (checking only up to $lhs_len and $rhs_len
        // respectively), and runs `$ge_branch` if true and `$ln_branch`
        // otherwise
        macro_rules! uge {
            (
                $lhs_len:expr,
                $lhs:ident,
                $rhs_len:expr,
                $rhs:ident,
                $ge_branch:block,
                $ln_branch:block
            ) => {
                let mut b0 = false;
                // allows lhs.len() to be smaller than rhs.len()
                for i in ($lhs_len..$rhs_len).rev() {
                    if !$rhs[i].is_zero() {
                        b0 = true;
                        break
                    }
                }
                if b0
                    || ({
                        let mut b1 = false;
                        for i in (0..$lhs_len).rev() {
                            if $lhs[i] < $rhs[i] {
                                b1 = true;
                                break
                            } else if $lhs[i] != $rhs[i] {
                                break
                            }
                        }
                        b1
                    })
                {
                    $ln_branch
                } else {
                    $ge_branch
                }
            };
        }

        // ugt stands for "unsigned greater than"
        // This checks for `$lhs > $rhs` (checking only up to $lhs_len and $rhs_len
        // respectively), and runs `$gt_branch` if true and `$le_branch`
        // otherwise
        macro_rules! ugt {
            (
                $lhs_len:expr,
                $lhs:ident,
                $rhs_len:expr,
                $rhs:ident,
                $gt_branch:block,
                $le_branch:block
            ) => {
                let mut b0 = false;
                // allows lhs.len() to be smaller than rhs.len()
                for i in ($lhs_len..$rhs_len).rev() {
                    if !$rhs[i].is_zero() {
                        b0 = true;
                        break
                    }
                }
                if b0
                    || ({
                        let mut b1 = true;
                        for i in (0..$lhs_len).rev() {
                            if $lhs[i] > $rhs[i] {
                                b1 = false;
                                break
                            } else if $lhs[i] != $rhs[i] {
                                break
                            }
                        }
                        b1
                    })
                {
                    $le_branch
                } else {
                    $gt_branch
                }
            };
        }

        // assigns `$sum + $sub` to `$target`,
        // and zeros out `$sum` except for it sets `$sum[0]` to `$val`
        macro_rules! special0 {
            ($len:expr, $sum:ident, $sub:ident, $target:ident, $val:expr) => {{
                // subtraction (`sub` is the two's complement of some value)
                let (sum, mut carry) = $sum[0].carrying_add($sub[0]);
                $target[0] = sum;
                $sum[0] = $val;
                for i in 1..($len - 1) {
                    let temp = $sum[i]
                        .dd()
                        .wrapping_add($sub[i].dd())
                        .wrapping_add(carry.dd());
                    $target[i] = temp.lo();
                    $sum[i].unset_all();
                    carry = temp.hi();
                }
                $target[$len - 1] = $sum[$len - 1]
                    .wrapping_add($sub[$len - 1])
                    .wrapping_add(carry);
                $sum[$len - 1].unset_all();
            }};
        }

        // assigns `$sum + $sub` to `$target`,
        // and assigns `$val + $add` to `$sum`
        macro_rules! special1 {
            ($len:expr, $sum:ident, $sub:ident, $targ:ident, $val:expr, $add:ident) => {{
                // subtraction (`sub` is the two's complement of some value)
                let (temp, mut carry) = $sum[0].carrying_add($sub[0]);
                $targ[0] = temp;
                for i in 1..($len - 1) {
                    let temp = $sum[i]
                        .dd()
                        .wrapping_add($sub[i].dd())
                        .wrapping_add(carry.dd());
                    $targ[i] = temp.lo();
                    carry = temp.hi();
                }
                $targ[$len - 1] = $sum[$len - 1]
                    .wrapping_add($sub[$len - 1])
                    .wrapping_add(carry);
                let (temp, mut carry) = $add[0].carrying_add($val);
                $sum[0] = temp;
                for i0 in 1..$len {
                    if carry.is_zero() {
                        for i1 in i0..$len {
                            $sum[i1] = $add[i1];
                            break
                        }
                    }
                    let temp = $add[i0].carrying_add(carry);
                    $sum[i0] = temp.0;
                    carry = temp.1;
                }
            }};
        }

        // assigns `$sum + $add` to `$sum`
        macro_rules! add {
            ($len:expr, $sum:ident, $add:ident) => {{
                let (sum, mut carry) = $sum[0].carrying_add($add[0]);
                $sum[0] = sum;
                for i in 1..($len - 1) {
                    let temp = $sum[i]
                        .dd()
                        .wrapping_add($add[i].dd())
                        .wrapping_add(carry.dd());
                    $sum[i] = temp.lo();
                    carry = temp.hi();
                }
                $sum[$len - 1] = $sum[$len - 1]
                    .wrapping_add($add[$len - 1])
                    .wrapping_add(carry);
            }};
        }

        // assumes that:
        // ini_duo_sd > 1
        // div_sd > 1
        #[inline(always)]
        fn large_div_by_large(
            len: usize,        // equal to the length of `duo` and `div`, must be > 2
            duo: &mut [Digit], // the dividend which will become the quotient
            ini_duo_sd: usize, // the initial most significant digit of `duo`
            div: &mut [Digit], // the divisor which will become the remainder
            div_sd: usize,     // the most significant digit of `div`
        ) {
            let ini_duo_lz = duo[ini_duo_sd].leading_zeros() as usize;
            let div_lz = div[div_sd].leading_zeros() as usize;
            // number of significant bits
            let ini_duo_sb =
                (ini_duo_sd * Digit::BITS) + (Digit::BITS - (ini_duo_lz as usize));
            let div_sb = (div_sd * Digit::BITS) + (Digit::BITS - div_lz);
            // quotient is 0 precheck
            if ini_duo_sb < div_sb {
                // the quotient should be 0 and remainder should be `duo`
                for i in 0..=ini_duo_sd {
                    div[i] = duo[i];
                    duo[i].unset_all();
                }
                for i in (ini_duo_sd + 1)..=div_sd {
                    div[i].unset_all();
                }
                return
            }
            // quotient is 0 or 1 check
            if ini_duo_sb == div_sb {
                let place = ini_duo_sd + 1;
                uge!(
                    place,
                    duo,
                    place,
                    div,
                    {
                        twos_complement!(place, div);
                        special0!(place, duo, div, div, Digit::ONE);
                        return
                    },
                    {
                        for i in 0..=ini_duo_sd {
                            div[i] = duo[i];
                            duo[i].unset_all();
                        }
                        for i in place..=div_sd {
                            div[i].unset_all();
                        }
                        return
                    }
                );
            }
            let ini_bits = ini_duo_sb - div_sb;
            // difference between the places of the significant bits
            if ini_bits < Digit::BITS {
                // the `mul` or `mul - 1` algorithm
                let (duo_sig_dd, div_sig_dd) = if ini_duo_lz == 0 {
                    // avoid shr overflow
                    (
                        DoubleDigit::from_lo_hi(duo[ini_duo_sd - 1], duo[ini_duo_sd]),
                        DoubleDigit::from_lo_hi(div[ini_duo_sd - 1], div[ini_duo_sd]),
                    )
                } else {
                    (
                        (duo[ini_duo_sd].dd() << (ini_duo_lz + Digit::BITS))
                            | (duo[ini_duo_sd - 1].dd() << ini_duo_lz)
                            | (duo[ini_duo_sd - 2].dd() >> (Digit::BITS - ini_duo_lz)),
                        (div[ini_duo_sd].dd() << (ini_duo_lz + Digit::BITS))
                            | (div[ini_duo_sd - 1].dd() << ini_duo_lz)
                            | (div[ini_duo_sd - 2].dd() >> (Digit::BITS - ini_duo_lz)),
                    )
                };
                let mul = duo_sig_dd.wrapping_div(div_sig_dd).lo();
                // Allocation could be avoided but it would involve more long division to
                // recover
                //`div`.
                // this will become `-(div * mul)`
                let mut sub: Vec<Digit> = Vec::with_capacity(len);
                // first digit done and carry
                let temp = mul.carrying_mul(div[0]);
                sub.push(temp.0);
                let mut carry = temp.1;
                // middle of row
                for i in 1..div_sd {
                    let temp = mul.carrying_mul_add(div[i], carry);
                    sub.push(temp.0);
                    carry = temp.1;
                }
                // final digit, test for `div * mul > duo`, and then form the two's
                // complement
                if div_sd == len - 1 {
                    let temp = mul.carrying_mul_add(div[div_sd], carry);
                    sub.push(temp.0);
                    if !temp.1.is_zero() {
                        // overflow
                        // the quotient should be `mul - 1` and remainder should be
                        //`duo + (div - div*mul)`
                        twos_complement!(len, sub);
                        add!(len, sub, div);
                        special0!(len, duo, sub, div, mul.wrapping_sub(Digit::ONE));
                        return
                    }
                    // if `div * mul > duo`
                    ugt!(
                        len,
                        sub,
                        len,
                        duo,
                        {
                            twos_complement!(len, sub);
                            add!(len, sub, div);
                            special0!(len, duo, sub, div, mul.wrapping_sub(Digit::ONE));
                            return
                        },
                        {
                            // the quotient is `mult` and remainder is `duo - (div *
                            // mult)`
                            twos_complement!(len, sub);
                            special0!(len, duo, sub, div, mul);
                            return
                        }
                    );
                } else {
                    let temp = mul.carrying_mul_add(div[div_sd], carry);
                    sub.push(temp.0);
                    sub.push(temp.1);
                    for _ in sub.len()..len {
                        sub.push(Digit::ZERO);
                    }
                    // if `div * mul > duo`
                    ugt!(
                        len,
                        sub,
                        len,
                        duo,
                        {
                            twos_complement!(len, sub);
                            add!(len, sub, div);
                            special0!(len, duo, sub, div, mul.wrapping_sub(Digit::ONE));
                            return
                        },
                        {
                            // the quotient is `mult` and remainder is `duo - (div *
                            // mult)`
                            twos_complement!(len, sub);
                            special0!(len, duo, sub, div, mul);
                            return
                        }
                    );
                }
            }
            let mut duo_sd = ini_duo_sd;
            let mut duo_lz = ini_duo_lz;
            // the number of lesser significant digits and bits not a part of `div_sig_d`
            let div_lesser_bits =
                Digit::BITS - (div_lz as usize) + (Digit::BITS * (div_sd - 1));
            // the most significant `Digit` bits of div
            let div_sig_d = if div_lz == 0 {
                div[div_sd]
            } else {
                (div[div_sd] << div_lz) | (div[div_sd - 1] >> (Digit::BITS - div_lz))
            };
            // has to be a `DoubleDigit` in case of overflow
            let div_sig_d_add1 = div_sig_d.dd().wrapping_add(Digit::ONE.dd());
            let mut duo_lesser_bits;
            let mut duo_sig_dd;
            // TODO: fix sizes here and below
            let quo_potential = len;
            // if ini_bits % Digit::BITS == 0 {ini_bits / Digit::BITS}
            // else {(ini_bits / Digit::BITS) + 1};
            let mut quo: Vec<Digit> = vec![Digit::ZERO; quo_potential as usize];
            loop {
                duo_lesser_bits =
                    (Digit::BITS - (duo_lz as usize)) + (Digit::BITS * (duo_sd - 2));
                duo_sig_dd = if duo_lz == 0 {
                    DoubleDigit::from_lo_hi(duo[duo_sd - 1], duo[duo_sd])
                } else {
                    (duo[duo_sd].dd() << (duo_lz + Digit::BITS))
                        | (duo[duo_sd - 1].dd() << duo_lz)
                        | (duo[duo_sd - 2].dd() >> (Digit::BITS - duo_lz))
                };
                if duo_lesser_bits >= div_lesser_bits {
                    let bits = duo_lesser_bits - div_lesser_bits;
                    // bits_ll is the number of lesser bits in the digit that contains
                    // lesser and greater bits
                    let (digits, bits_ll) = (bits / Digit::BITS, bits % Digit::BITS);
                    // Unfortunately, `mul` here can be up to (2^2n - 1)/(2^(n-1)), where
                    // `n` is the number of bits in a `Digit`. This
                    // means that an `n+1` bit integer is needed to
                    // store mul. Because only one extra higher bit is involved,
                    // the algebraic simplification `(mul + 2^n)*div` to `mul*div +
                    // div*2^n` can be used when that highest bit is
                    // set. This just requires faster and simpler
                    // addition inlining hell instead of long multiplication inlining
                    // hell.
                    let mul = duo_sig_dd.wrapping_div(div_sig_d_add1);
                    // add `mul << bits` to `quo`
                    // no inlining hell here because `bits_ll < n` and it takes a shift of
                    // `n` to overflow
                    let split_mul = mul << bits_ll;
                    let (temp, mut carry) = split_mul.lo().carrying_add(quo[digits]);
                    quo[digits] = temp;
                    let temp = split_mul
                        .hi()
                        .dd()
                        .wrapping_add(quo[digits + 1].dd())
                        .wrapping_add(carry.dd());
                    quo[digits + 1] = temp.lo();
                    carry = temp.hi();
                    for i in (digits + 2)..quo.len() {
                        if carry.is_zero() {
                            break
                        }
                        let temp = quo[i].carrying_add(carry);
                        quo[i] = temp.0;
                        carry = temp.1;
                    }
                    // special long division algorithm core.
                    // Note that nearly all branches before this are not just wanted for
                    // performance reasons but are actually required
                    // in order to not break this. these blocks
                    // subtract `(mul * div) << bits` from `duo` check
                    // for highest bit set
                    if mul.hi().is_zero() {
                        let mul = mul.lo();
                        // carry for bits that wrap across digit boundaries when `<<
                        // bits_ll` applied
                        let (temp0, mut wrap_carry) = (div[0].dd() << bits_ll).lo_hi();
                        // the regular multiplication carry
                        let (temp1, mut mul_carry) =
                            mul.dd().wrapping_mul(temp0.dd()).lo_hi();
                        // this carry includes the two's complement increment carry
                        let (temp2, mut add_carry) = (!temp1)
                            .dd()
                            .wrapping_add(duo[digits].dd())
                            .wrapping_add(Digit::ONE.dd())
                            .lo_hi();
                        duo[digits] = temp2;
                        for i in (digits + 1)..=duo_sd {
                            let temp0 = ((div[i - digits].dd() << bits_ll)
                                | wrap_carry.dd())
                            .lo_hi();
                            wrap_carry = temp0.1;
                            let temp1 = mul
                                .dd()
                                .wrapping_mul(temp0.0.dd())
                                .wrapping_add(mul_carry.dd())
                                .lo_hi();
                            mul_carry = temp1.1;
                            let temp2 = (!temp1.0)
                                .dd()
                                .wrapping_add(duo[i].dd())
                                .wrapping_add(add_carry.dd())
                                .lo_hi();
                            add_carry = temp2.1;
                            duo[i] = temp2.0;
                        }
                    } else {
                        //  2222x <- mul_carry
                        //   7987 <- div
                        //      3 <- mul (13) without high bit
                        // *_____
                        //  23961 <- temp0
                        //
                        // 1111xx <- add0_carry
                        //  23961 <- temp0
                        //  7987  <- div shifted up by one digit
                        //+______
                        // 103831 <- temp1
                        //
                        // subtract duo by temp1 negated (with the carry from the two's
                        // complement being put into `wrap_carry`)
                        // and shifted (with `wrap_carry`)

                        let mul = mul.lo();
                        let (temp0, mut mul_carry) = mul.carrying_mul(div[0]);
                        let temp1 = temp0;
                        let mut add0_carry = Digit::ZERO;
                        // the increment from the two's complement can be stored in
                        // `wrap_carry`
                        let (temp2, mut wrap_carry) =
                            ((!temp1).dd().wrapping_add(Digit::ONE.dd()) << bits_ll)
                                .lo_hi();
                        let (temp3, mut add1_carry) = temp2.carrying_add(duo[digits]);
                        duo[digits] = temp3;
                        for i in (digits + 1)..=duo_sd {
                            let temp0 = mul
                                .dd()
                                .wrapping_mul(div[i - digits].dd())
                                .wrapping_add(mul_carry.dd());
                            mul_carry = temp0.hi();
                            let temp1 = temp0
                                .lo()
                                .dd()
                                .wrapping_add(div[i - digits - 1].dd())
                                .wrapping_add(add0_carry.dd());
                            add0_carry = temp1.hi();
                            let temp2 = ((!temp1.lo()).dd() << bits_ll)
                                .wrapping_add(wrap_carry.dd());
                            wrap_carry = temp2.hi();
                            let temp3 = temp2
                                .lo()
                                .dd()
                                .wrapping_add(duo[i].dd())
                                .wrapping_add(add1_carry.dd());
                            add1_carry = temp3.hi();
                            duo[i] = temp3.lo();
                        }
                    }
                } else {
                    // the `mul` or `mul - 1` algorithm with addition from `quo`
                    let div_sig_dd = if duo_lz == 0 {
                        // avoid shr overflow
                        DoubleDigit::from_lo_hi(div[duo_sd - 1], div[duo_sd])
                    } else {
                        (div[duo_sd].dd() << (duo_lz + Digit::BITS))
                            | (div[duo_sd - 1].dd() << duo_lz)
                            | (div[duo_sd - 2].dd() >> (Digit::BITS - duo_lz))
                    };
                    let mul = duo_sig_dd.wrapping_div(div_sig_dd).lo();
                    // I could avoid allocation but it would involve more long division to
                    // recover
                    //`div`, followed by a second long multiplication with `mul - 1`.
                    // this will become `-(div * mul)`
                    // note: div_sd != len - 1 because it would be caught by the first
                    // `mul` or
                    //`mul-1` algorithm
                    let mut sub: Vec<Digit> = Vec::with_capacity(len);
                    // first digit done and carry
                    let (temp, mut mul_carry) =
                        mul.dd().wrapping_mul(div[0].dd()).lo_hi();
                    sub.push(temp);
                    for i in 1..div_sd {
                        let temp = mul.carrying_mul_add(div[i], mul_carry);
                        sub.push(temp.0);
                        mul_carry = temp.1;
                    }
                    let temp = mul.carrying_mul_add(div[div_sd], mul_carry);
                    sub.push(temp.0);
                    sub.push(temp.1);
                    for _ in (div_sd + 2)..len {
                        sub.push(Digit::ZERO);
                    }
                    let sub_len = sub.len();
                    ugt!(
                        sub_len,
                        sub,
                        len,
                        duo,
                        {
                            // the quotient is `quo + (mult - 1)` and remainder is
                            //`duo + (div - div*mul)`
                            twos_complement!(sub_len, sub);
                            add!(sub_len, sub, div);
                            special1!(
                                sub_len,
                                duo,
                                sub,
                                div,
                                mul.wrapping_sub(Digit::ONE),
                                quo
                            );
                            return
                        },
                        {
                            // the quotient is `quo + mult` and remainder is `duo - (div *
                            // mult)`
                            twos_complement!(sub_len, sub);
                            special1!(sub_len, duo, sub, div, mul, quo);
                            return
                        }
                    );
                }
                // find the new `duo_sd`
                for i in (0..=duo_sd).rev() {
                    if !duo[i].is_zero() {
                        duo_sd = i;
                        break
                    }
                    if i == 0 {
                        // the quotient should be `quo` and remainder should be zero
                        for i in 0..len {
                            div[i] = Digit::ZERO;
                            duo[i] = quo[i];
                        }
                        return
                    }
                }
                duo_lz = duo[duo_sd].leading_zeros() as usize;
                let duo_sb = (duo_sd * Digit::BITS) + (Digit::BITS - duo_lz);
                //`quo` should have 0 or 1 added to it check
                if duo_sb == div_sb {
                    // if `div <= duo`
                    uge!(
                        len,
                        duo,
                        len,
                        div,
                        {
                            // the quotient should be `quo + 1` and remainder should be
                            // `duo - div`
                            twos_complement!(len, div);
                            add!(len, div, duo);
                            for i0 in 0..len {
                                match quo[i0].overflowing_add(Digit::ONE) {
                                    (v, false) => {
                                        duo[i0] = v;
                                        for i1 in (i0 + 1)..len {
                                            duo[i1] = quo[i1];
                                        }
                                        break
                                    }
                                    (v, true) => {
                                        duo[i0] = v;
                                    }
                                }
                            }
                            return
                        },
                        {
                            // the quotient should be `quo` and remainder should be `duo`
                            for i in 0..len {
                                div[i] = duo[i];
                                duo[i] = quo[i];
                            }
                            return
                        }
                    );
                }
                // more 0 cases check
                if div_sb > duo_sb {
                    // the quotient should be `quo` and remainder should be `duo`
                    for i in 0..len {
                        div[i] = duo[i];
                        duo[i] = quo[i];
                    }
                    return
                }
                // this can only happen if `div_sd < 2` (because of above branches),
                // but it is not worth it to unroll further
                if duo_sd < 2 {
                    // duo_sd < 2 because of the "if `duo >= div`" branch above
                    // simple division and addition
                    let duo_dd = DoubleDigit::from_lo_hi(duo[0], duo[1]);
                    let div_dd = DoubleDigit::from_lo_hi(div[0], div[1]);
                    let (mul, rem) = duo_dd.wrapping_divrem(div_dd);
                    // the quotient should be `quo + mul` and remainder should be `rem`
                    div[0] = rem.lo();
                    div[1] = rem.hi();
                    let (temp, mut carry) = quo[0].carrying_add(mul.lo());
                    duo[0] = temp;
                    let temp = quo[1]
                        .dd()
                        .wrapping_add(mul.hi().dd())
                        .wrapping_add(carry.dd());
                    duo[1] = temp.lo();
                    carry = temp.hi();
                    for i0 in 2..len {
                        if carry.is_zero() {
                            duo[i0..len].clone_from_slice(&quo[i0..len]);
                            break
                        }
                        let temp = quo[i0].carrying_add(carry);
                        duo[i0] = temp.0;
                        carry = temp.1;
                    }
                    return
                }
            }
        }

        // Note: Special cases are aggressively taken care of throughout this function,
        // both because the core long division algorithm does not work on many
        // edges, and because of optimization. find the most significant non
        // zeroes, check for `duo` < `div`, and check for division by zero
        match div.iter().rposition(|x| !x.is_zero()) {
            Some(div_sd) => {
                // the initial most significant nonzero duo digit
                let ini_duo_sd: usize = match duo.iter().rposition(|x| !x.is_zero()) {
                    Some(x) => x,
                    None => {
                        // quotient and remainder should be 0
                        // duo is already zero
                        for x in div.iter_mut() {
                            x.unset_all()
                        }
                        return true
                    }
                };
                if ini_duo_sd < div_sd {
                    // the divisor is larger than the dividend
                    // quotient should be 0 and remainder is `duo`
                    for (duo_d, div_d) in duo.iter_mut().zip(div.iter_mut()) {
                        *div_d = *duo_d;
                        (*duo_d).unset_all()
                    }
                    return true
                }
                match (ini_duo_sd == 0, div_sd == 0) {
                    (false, false) => {
                        // ini_duo_sd cannot be 0 or 1 for `large_div_by_large`
                        if ini_duo_sd == 1 {
                            let temp = DoubleDigit::from_lo_hi(duo[0], duo[1])
                                .wrapping_divrem(DoubleDigit::from_lo_hi(div[0], div[1]));
                            duo[0] = temp.0.lo();
                            duo[1] = temp.0.hi();
                            div[0] = temp.1.lo();
                            div[1] = temp.1.hi();
                            return true
                        }
                        large_div_by_large(duo.len(), duo, ini_duo_sd, div, div_sd);
                        true
                    }
                    (true, false) => unreachable!(),
                    (false, true) => {
                        if div[0].leading_zeros() >= 32 {
                            large_div_by_u32(duo, ini_duo_sd, div);
                            true
                        } else {
                            large_div_by_small(duo, ini_duo_sd, div);
                            true
                        }
                    }
                    (true, true) => {
                        let temp = duo[0].wrapping_divrem(div[0]);
                        duo[0] = temp.0;
                        div[0] = temp.1;
                        true
                    }
                }
            }
            None => false,
        }
    }

    /// This function is intended to be inlined into all of the unsigned
    /// quotient and remainder functions for optimal assembly.
    /// `duo` is divided by `div`, and the remainder is assigned to `duo` and
    /// quotient assigned to `div`
    /// `false` is returned if division by zero happened. Nothing is modified in
    /// the case of division by zero.
    #[inline]
    pub(crate) fn aarons_algorithm_remdiv(duo: &mut [Digit], div: &mut [Digit]) -> bool {
        if ApInt::aarons_algorithm_divrem(duo, div) {
            let mut temp;
            for i in 0..duo.len() {
                temp = duo[i];
                duo[i] = div[i];
                div[i] = temp;
            }
            true
        } else {
            false
        }
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and sets `lhs`
    /// equal to the quotient and `rhs` equal to the remainder. This
    /// function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_udivrem_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        match ApInt::zip_access_data_mut_both(lhs, rhs)? {
            ZipDataAccessMutBoth::Inl(duo, div) => {
                if !div.is_zero() {
                    let temp = duo.wrapping_divrem(*div);
                    *duo = temp.0;
                    *div = temp.1;
                    return Ok(())
                }
            }
            ZipDataAccessMutBoth::Ext(duo, div) => {
                if ApInt::aarons_algorithm_divrem(duo, div) {
                    return Ok(())
                }
            }
        }
        // Note that the typical places `Err` `Ok` are returned is switched. This is
        // because
        //`rhs.is_zero()` is found as part of finding `duo_sd` inside
        //`rhs.is_zero()` `aarons_algorithm_divrem`,
        // and `lhs.clone()` cannot be performed inside the match statement
        Err(Error::division_by_zero(DivOp::UnsignedDivRem, lhs.clone()))
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and sets `lhs`
    /// equal to the remainder and `rhs` equal to the quotient. This
    /// function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_uremdiv_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        match ApInt::zip_access_data_mut_both(lhs, rhs)? {
            ZipDataAccessMutBoth::Inl(duo, div) => {
                if !div.is_zero() {
                    let temp = duo.wrapping_divrem(*div);
                    *duo = temp.1;
                    *div = temp.0;
                    return Ok(())
                }
            }
            ZipDataAccessMutBoth::Ext(duo, div) => {
                if ApInt::aarons_algorithm_remdiv(duo, div) {
                    return Ok(())
                }
            }
        }
        Err(Error::division_by_zero(DivOp::UnsignedRemDiv, lhs.clone()))
    }

    /// Quotient-assigns `lhs` by `rhs` inplace using **unsigned**
    /// interpretation. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_udiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(duo, div) => {
                if !div.is_zero() {
                    *duo = duo.wrapping_div(div);
                    return Ok(())
                }
            }
            Ext(duo, div) => {
                if ApInt::aarons_algorithm_divrem(duo, &mut div.to_vec()[..]) {
                    return Ok(())
                }
            }
        }
        Err(Error::division_by_zero(DivOp::UnsignedDiv, self.clone()))
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and returns the
    /// quotient. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_udiv(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_udiv_assign)
    }

    /// Remainder-assigns `lhs` by `rhs` inplace using **unsigned**
    /// interpretation. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_urem_assign(&mut self, rhs: &ApInt) -> Result<()> {
        match self.zip_access_data_mut_self(rhs)? {
            Inl(duo, div) => {
                if !div.is_zero() {
                    *duo = duo.wrapping_rem(div);
                    return Ok(())
                }
            }
            Ext(duo, div) => {
                if ApInt::aarons_algorithm_remdiv(duo, &mut div.to_vec()[..]) {
                    return Ok(())
                }
            }
        }
        Err(Error::division_by_zero(DivOp::UnsignedRem, self.clone()))
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and returns the
    /// remainder. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_urem(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_urem_assign)
    }

    /// Divides `lhs` by `rhs` using **signed** interpretation and sets `lhs`
    /// equal to the quotient and `rhs` equal to the remainder. This
    /// function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_sdivrem_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedDivRem, lhs.clone()))
        }
        let (negate_lhs, negate_rhs) = match ((*lhs).msb(), (*rhs).msb()) {
            (false, false) => (false, false),
            (true, false) => {
                lhs.wrapping_neg();
                (true, true)
            }
            (false, true) => {
                rhs.wrapping_neg();
                (true, false)
            }
            (true, true) => {
                lhs.wrapping_neg();
                rhs.wrapping_neg();
                (false, true)
            }
        };
        ApInt::wrapping_udivrem_assign(lhs, rhs).unwrap();
        if negate_lhs {
            lhs.wrapping_neg()
        }
        if negate_rhs {
            rhs.wrapping_neg()
        }
        // clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Divides `lhs` by `rhs` using **signed** interpretation and sets `lhs`
    /// equal to the remainder and `rhs` equal to the quotient. This
    /// function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_sremdiv_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedRemDiv, lhs.clone()))
        }
        let (negate_lhs, negate_rhs) = match ((*lhs).msb(), (*rhs).msb()) {
            (false, false) => (false, false),
            (true, false) => {
                lhs.wrapping_neg();
                (true, true)
            }
            (false, true) => {
                rhs.wrapping_neg();
                (false, true)
            }
            (true, true) => {
                lhs.wrapping_neg();
                rhs.wrapping_neg();
                (true, false)
            }
        };
        ApInt::wrapping_uremdiv_assign(lhs, rhs).unwrap();
        if negate_lhs {
            lhs.wrapping_neg()
        }
        if negate_rhs {
            rhs.wrapping_neg()
        }
        // clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Quotient-assigns `lhs` by `rhs` inplace using **signed** interpretation.
    /// This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_sdiv_assign(&mut self, rhs: &ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedDiv, self.clone()))
        }
        let mut rhs_clone = (*rhs).clone();
        let negate_lhs = match ((*self).msb(), rhs_clone.msb()) {
            (false, false) => false,
            (true, false) => {
                self.wrapping_neg();
                true
            }
            (false, true) => {
                rhs_clone.wrapping_neg();
                true
            }
            (true, true) => {
                self.wrapping_neg();
                rhs_clone.wrapping_neg();
                false
            }
        };
        ApInt::wrapping_udivrem_assign(self, &mut rhs_clone).unwrap();
        if negate_lhs {
            self.wrapping_neg()
        }
        // clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Divides `self` by `rhs` using **signed** interpretation and returns the
    /// quotient. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_sdiv(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sdiv_assign)
    }

    /// Remainder-assigns `lhs` by `rhs` inplace using **signed**
    /// interpretation. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_srem_assign(&mut self, rhs: &ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedRem, self.clone()))
        }
        let mut rhs_clone = (*rhs).clone();
        let negate_lhs = match ((*self).msb(), rhs_clone.msb()) {
            (false, false) => false,
            (true, false) => {
                self.wrapping_neg();
                true
            }
            (false, true) => {
                rhs_clone.wrapping_neg();
                false
            }
            (true, true) => {
                self.wrapping_neg();
                rhs_clone.wrapping_neg();
                true
            }
        };
        ApInt::wrapping_uremdiv_assign(self, &mut rhs_clone).unwrap();
        if negate_lhs {
            self.wrapping_neg()
        }
        // clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Divides `self` by `rhs` using **signed** interpretation and returns the
    /// remainder. This function **may** allocate memory.
    ///
    /// # Errors
    ///
    /// - If `self` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_srem(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_srem_assign)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod inc {
        use super::*;
        use core::u64;

        #[test]
        fn test() {
            assert_eq!(ApInt::from(14u8).into_wrapping_inc(), ApInt::from(15u8));
            assert_eq!(ApInt::from(15u8).into_wrapping_inc(), ApInt::from(16u8));
            assert_eq!(ApInt::from(16u8).into_wrapping_inc(), ApInt::from(17u8));
            assert_eq!(ApInt::from(17u8).into_wrapping_inc(), ApInt::from(18u8));
            assert_eq!(
                ApInt::from([0u64, 0, 0]).into_wrapping_inc(),
                ApInt::from([0u64, 0, 1])
            );
            assert_eq!(
                ApInt::from([0, 7, u64::MAX]).into_wrapping_inc(),
                ApInt::from([0u64, 8, 0])
            );
            assert_eq!(
                ApInt::from([u64::MAX, u64::MAX]).into_wrapping_inc(),
                ApInt::from([0u64, 0])
            );
            assert_eq!(
                ApInt::from([0, u64::MAX, u64::MAX - 1]).into_wrapping_inc(),
                ApInt::from([0, u64::MAX, u64::MAX])
            );
            assert_eq!(
                ApInt::from([0, u64::MAX, 0]).into_wrapping_inc(),
                ApInt::from([0, u64::MAX, 1])
            );
        }
    }

    mod wrapping_neg {
        use super::*;
        use crate::bitwidth::BitWidth;

        fn assert_symmetry(input: ApInt, expected: ApInt) {
            assert_eq!(input.clone().into_wrapping_neg(), expected.clone());
            assert_eq!(expected.into_wrapping_neg(), input);
        }

        fn test_vals() -> impl Iterator<Item = i128> {
            [
                0_i128, 1, 2, 4, 5, 7, 10, 42, 50, 100, 128, 150, 1337, 123123, 999999,
                987432, 77216417,
            ]
            .iter()
            .map(|v| *v)
        }

        #[test]
        fn simple() {
            assert_symmetry(ApInt::zero(BitWidth::w1()), ApInt::zero(BitWidth::w1()));
            assert_symmetry(
                ApInt::unsigned_max_value(BitWidth::w1()),
                ApInt::all_set(BitWidth::w1()),
            );
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

    mod mul {
        use super::*;
        use crate::bitwidth::BitWidth;
        use core::{
            u64,
            u8,
        };

        #[test]
        fn rigorous() {
            // there are many special case and size optimization paths, so this test must
            // be very rigorous.

            // multiplication of apints composed of only u8::MAX in their least
            // significant digits only works for num_u8 > 1
            fn nine_test(num_u8: usize) {
                let mut lhs;
                let mut rhs =
                    ApInt::from(0u8).into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
                let nine = ApInt::from(u8::MAX)
                    .into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
                for rhs_nine in 0..num_u8 {
                    rhs.wrapping_shl_assign(8usize).unwrap();
                    rhs |= &nine;
                    lhs = ApInt::from(0u8)
                        .into_zero_resize(BitWidth::new(num_u8 * 8).unwrap());
                    'outer: for lhs_nine in 0..num_u8 {
                        lhs.wrapping_shl_assign(8usize).unwrap();
                        lhs |= &nine;
                        // imagine multiplying a string of base 10 nines together.
                        // It will produce things like 998001, 8991, 98901, 9989001.
                        // this uses a formula for the number of nines, eights, and zeros
                        // except here nine is u8::MAX, eight is
                        // u8::MAX - 1, and zero is 0u8
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
                            assert_eq!(result.clone().resize_to_u8(), 0);
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
                        assert_eq!(result.clone().resize_to_u8(), u8::MAX - 1);
                        for i in 0..nines_after_eight {
                            if 1 + zeros_after_one + nines_before_eight + i >= num_u8 - 1
                            {
                                continue 'outer
                            }
                            result.wrapping_lshr_assign(8usize).unwrap();
                            assert_eq!(result.clone().resize_to_u8(), u8::MAX);
                        }
                    }
                }
            }
            // test inl apints
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
            // test ext apints
            nine_test(9);
            nine_test(16);
            // 5 digits wide
            nine_test(40);
            nine_test(63);
            // non overflowing test
            let resize = [
                7usize, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 137,
                200, 255, 256, 700, 907, 1024, 2018, 2019,
            ];
            let lhs_shl = [
                0usize, 1, 0, 1, 4, 7, 4, 10, 13, 0, 31, 25, 7, 17, 32, 50, 0, 64, 249,
                8, 777, 0, 1000, 0,
            ];
            let rhs_shl = [
                0usize, 0, 1, 1, 3, 6, 4, 14, 10, 0, 0, 25, 0, 18, 32, 49, 100, 64, 0,
                256, 64, 900, 1000, 0,
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
                let zero =
                    ApInt::from(0u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
                let one =
                    ApInt::from(1u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
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
                ApInt::from([0, 0, 0, 0, u64::MAX, 0, u64::MAX, u64::MAX])
                    .into_wrapping_mul(&ApInt::from([
                        0,
                        0,
                        0,
                        0,
                        u64::MAX,
                        u64::MAX,
                        0,
                        u64::MAX
                    ]))
                    .unwrap(),
                ApInt::from([u64::MAX, 0, 1, u64::MAX - 3, 1, u64::MAX, u64::MAX, 1])
            );
        }
    }

    mod div_rem {
        use super::*;
        use crate::bitwidth::BitWidth;
        use core::u64;

        // TODO: add division by zero testing after error refactoring is finished
        // use errors::ErrorKind;
        #[test]
        fn simple() {
            /// does all of the simple division tests
            /// - `$signed`: if the functions are signed divisions or not
            /// - `$fun_assign`: a division function such as
            ///   `wrapping_udiv_assign` with that signature
            /// - `$fun_into`: a division function such as `into_wrapping_udiv`
            ///   with that signature
            /// - `$fun`: a division function such as `wrapping_udivrem_assign`
            ///   with that signature
            /// - `$r0`: the quotient or remainder or both of 80 by 7, depending
            ///   on division function type
            /// - `$r1`, `$r2`, `$r3`: 80 by -7, -80 by 7, -80 by -7. These can
            ///   be 0 if `$signed` is false.
            macro_rules! s {
                (
                    $signed:expr,
                    $fun_assign:ident,
                    $fun_into:ident,
                    $r0:expr,
                    $r1:expr,
                    $r2:expr,
                    $r3:expr
                ) => {
                    // match $fun_assign
                    // match ApInt::from(123u8).$fun_into(&ApInt::from(0u8)) {
                    // Err(Error{kind: ErrorKind::DivisionByZero{op: DivOp::$div_op, lhs:
                    // x}, message: _, annotation: _}) => { assert_eq!(x,ApInt::
                    // from(123u8)); },
                    // _ => unreachable!(),
                    // }
                    // match ApInt::from(12345678912345689123456789123456789u128).
                    {
                        let lhs = ApInt::from(80i8);
                        let rhs = ApInt::from(7i8);
                        let mut temp = lhs.clone();
                        temp.$fun_assign(&rhs).unwrap();
                        assert_eq!(temp, ApInt::from($r0));
                        assert_eq!(lhs.$fun_into(&rhs).unwrap(), ApInt::from($r0));
                    }
                    if $signed {
                        {
                            let lhs = ApInt::from(80i8);
                            let rhs = ApInt::from(-7i8);
                            let mut temp = lhs.clone();
                            temp.$fun_assign(&rhs).unwrap();
                            assert_eq!(temp, ApInt::from($r1));
                            assert_eq!(lhs.$fun_into(&rhs).unwrap(), ApInt::from($r1));
                        }
                        {
                            let lhs = ApInt::from(-80i8);
                            let rhs = ApInt::from(7i8);
                            let mut temp = lhs.clone();
                            temp.$fun_assign(&rhs).unwrap();
                            assert_eq!(temp, ApInt::from($r2));
                            assert_eq!(lhs.$fun_into(&rhs).unwrap(), ApInt::from($r2));
                        }
                        {
                            let lhs = ApInt::from(-80i8);
                            let rhs = ApInt::from(-7i8);
                            let mut temp = lhs.clone();
                            temp.$fun_assign(&rhs).unwrap();
                            assert_eq!(temp, ApInt::from($r3));
                            assert_eq!(lhs.$fun_into(&rhs).unwrap(), ApInt::from($r3));
                        }
                    }
                };
                ($signed:expr, $fun:ident, $r0:expr, $r1:expr, $r2:expr, $r3:expr) => {{
                    let mut lhs = ApInt::from(80i8);
                    let mut rhs = ApInt::from(7i8);
                    ApInt::$fun(&mut lhs, &mut rhs).unwrap();
                    assert_eq!(lhs, ApInt::from($r0.0));
                    assert_eq!(rhs, ApInt::from($r0.1));
                }
                if $signed {
                    {
                        let mut lhs = ApInt::from(80i8);
                        let mut rhs = ApInt::from(-7i8);
                        ApInt::$fun(&mut lhs, &mut rhs).unwrap();
                        assert_eq!(lhs, ApInt::from($r1.0));
                        assert_eq!(rhs, ApInt::from($r1.1));
                    }
                    {
                        let mut lhs = ApInt::from(-80i8);
                        let mut rhs = ApInt::from(7i8);
                        ApInt::$fun(&mut lhs, &mut rhs).unwrap();
                        assert_eq!(lhs, ApInt::from($r2.0));
                        assert_eq!(rhs, ApInt::from($r2.1));
                    }
                    {
                        let mut lhs = ApInt::from(-80i8);
                        let mut rhs = ApInt::from(-7i8);
                        ApInt::$fun(&mut lhs, &mut rhs).unwrap();
                        assert_eq!(lhs, ApInt::from($r3.0));
                        assert_eq!(rhs, ApInt::from($r3.1));
                    }
                }};
            }
            s!(
                false,
                wrapping_udiv_assign,
                into_wrapping_udiv,
                11i8,
                0,
                0,
                0
            );
            s!(
                false,
                wrapping_urem_assign,
                into_wrapping_urem,
                3i8,
                0,
                0,
                0
            );
            s!(
                true,
                wrapping_sdiv_assign,
                into_wrapping_sdiv,
                11i8,
                -11i8,
                -11i8,
                11i8
            );
            s!(
                true,
                wrapping_srem_assign,
                into_wrapping_srem,
                3i8,
                3i8,
                -3i8,
                -3i8
            );
            s!(
                false,
                wrapping_udivrem_assign,
                (11i8, 3i8),
                (0, 0),
                (0, 0),
                (0, 0)
            );
            s!(
                false,
                wrapping_uremdiv_assign,
                (3i8, 11i8),
                (0, 0),
                (0, 0),
                (0, 0)
            );
            s!(
                true,
                wrapping_sdivrem_assign,
                (11i8, 3i8),
                (-11i8, 3i8),
                (-11i8, -3i8),
                (11i8, -3i8)
            );
            s!(
                true,
                wrapping_sremdiv_assign,
                (3i8, 11i8),
                (3i8, -11i8),
                (-3i8, -11i8),
                (-3i8, 11i8)
            );
        }

        // NOTE: this test only works if multiplication and a few other functions work
        #[test]
        fn complex() {
            // there are many special case and size optimization paths,
            // so this test must be very rigorous.
            assert_eq!(
                ApInt::from(123u8)
                    .into_wrapping_udiv(&ApInt::from(7u8))
                    .unwrap(),
                ApInt::from(17u8)
            );
            assert_eq!(
                ApInt::from([0u64, 0, 0, 123])
                    .into_wrapping_udiv(&ApInt::from([0u64, 0, 0, 7]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 17])
            );
            assert_eq!(
                ApInt::from([0u64, 0, 0, 0])
                    .into_wrapping_udiv(&ApInt::from([0u64, 0, 0, 7]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([0u64, 0, 0, 3])
                    .into_wrapping_udiv(&ApInt::from([0u64, 0, 0, 7]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([0u64, 0, 0, 0])
                    .into_wrapping_udiv(&ApInt::from([0u64, 7, 0, 0]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([0u64, 0, 0, 7])
                    .into_wrapping_udiv(&ApInt::from([0u64, 4, 0, 0]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([0u64, 0, 3, 0])
                    .into_wrapping_udiv(&ApInt::from([0u64, 4, 0, 0]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([0u64, 1, 0, 0])
                    .into_wrapping_udiv(&ApInt::from([0u64, 0, 0, 4]))
                    .unwrap(),
                ApInt::from([0u64, 0, u64::MAX / 4 + 1, 0])
            );
            assert_eq!(
                // this one
                ApInt::from([0u64, 1, 0, 0])
                    .into_wrapping_udiv(&ApInt::from([0u64, 0, 1, 0]))
                    .unwrap(),
                ApInt::from([0u64, 0, 1, 0])
            );
            assert_eq!(
                ApInt::from([1u64, 2, 3, 4])
                    .into_wrapping_udiv(&ApInt::from([1u64, 2, 3, 4]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0, 1])
            );
            assert_eq!(
                ApInt::from([
                    0u64,
                    1,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX
                ])
                .into_wrapping_udiv(&ApInt::from([0u64, 0, 0, 0, 0, 0, 0, 2]))
                .unwrap(),
                ApInt::from([
                    0u64,
                    0,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX
                ])
            );
            assert_eq!(
                ApInt::from([
                    u64::MAX,
                    u64::MAX - 1,
                    1,
                    u64::MAX - 1,
                    u64::MAX - 1,
                    2,
                    u64::MAX - 1,
                    1
                ])
                .into_wrapping_udiv(&ApInt::from([
                    0,
                    0,
                    0,
                    0,
                    u64::MAX,
                    u64::MAX,
                    0,
                    u64::MAX
                ]))
                .unwrap(),
                ApInt::from([0, 0, 0, 0, u64::MAX, u64::MAX, 0, u64::MAX])
            );
            assert_eq!(
                ApInt::from(61924494876344321u128)
                    .into_wrapping_urem(&ApInt::from(167772160u128))
                    .unwrap(),
                ApInt::from(1u128)
            );
            assert_eq!(
                ApInt::from([
                    18446744073709551615u64,
                    18446744073709551615,
                    1048575,
                    18446462598732840960
                ])
                .into_wrapping_urem(&ApInt::from([0u64, 0, 140668768878592, 0]))
                .unwrap(),
                ApInt::from([0, 0, 136545601323007, 18446462598732840960u64])
            );
            assert_eq!(
                ApInt::from([1u64, 17293821508111564796, 2305843009213693952])
                    .into_wrapping_urem(&ApInt::from([0u64, 1, 18446742978492891132]))
                    .unwrap(),
                ApInt::from([0u64, 0, 0])
            );
            assert_eq!(
                ApInt::from([1u64, 18446744073692774368, 268435456])
                    .into_wrapping_add(&ApInt::from([0u64, 1, 18446744073709519359]))
                    .unwrap()
                    .into_wrapping_udiv(&ApInt::from([0u64, 1, 18446744073709551584]))
                    .unwrap(),
                ApInt::from([0u64, 0, 18446744073701163008])
            );
            assert_eq!(
                ApInt::from([
                    18446744073709551615u64,
                    18446744073709551615,
                    18446739675663040512,
                    2199023255552
                ])
                .into_wrapping_urem(&ApInt::from([
                    18446744073709551615u64,
                    18446744073709551615,
                    18446739675663040512,
                    2199023255552
                ]))
                .unwrap(),
                ApInt::from([0u64, 0, 0, 0])
            );
            assert_eq!(
                ApInt::from([1u64, 18446462598730776592, 1047972020113])
                    .into_wrapping_udiv(&ApInt::from([0u64, 16383, 18446744056529682433]))
                    .unwrap(),
                ApInt::from([0u64, 0, 2251782633816065])
            );
            assert_eq!(
                ApInt::from([
                    54467619767447688u64,
                    18446739675392512496,
                    5200531536562092095,
                    18446744073709551615
                ])
                .into_wrapping_udiv(&ApInt::from([0u64, 8255, 18446462598732840960, 0]))
                .unwrap(),
                ApInt::from([0u64, 0, 6597337677824, 288230376151678976])
            );
            let resize = [
                7usize, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 137,
                200, 255, 256, 700, 907, 1024, 2018, 2019,
            ];
            let lhs_shl = [
                0usize, 1, 0, 1, 4, 6, 4, 10, 13, 0, 31, 25, 7, 17, 32, 50, 0, 64, 249,
                8, 777, 0, 900, 0,
            ];
            let rhs_shl = [
                0usize, 0, 1, 1, 3, 5, 4, 14, 10, 0, 0, 25, 0, 18, 32, 49, 100, 64, 0,
                256, 64, 900, 1000, 0,
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
                let zero =
                    ApInt::from(0u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
                let one =
                    ApInt::from(1u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
                let product = lhs.clone().into_wrapping_mul(&rhs).unwrap();
                assert_eq!(zero.clone().into_wrapping_udiv(&lhs).unwrap(), zero);
                assert_eq!(zero.clone().into_wrapping_udiv(&rhs).unwrap(), zero);
                assert_eq!(lhs.clone().into_wrapping_udiv(&one).unwrap(), lhs);
                assert_eq!(rhs.clone().into_wrapping_udiv(&one).unwrap(), rhs);
                assert_eq!(lhs.clone().into_wrapping_udiv(&lhs).unwrap(), one);
                assert_eq!(rhs.clone().into_wrapping_udiv(&rhs).unwrap(), one);
                let temp = product.clone().into_wrapping_udiv(&lhs).unwrap();
                if temp != rhs {
                    panic!(
                        "lhs_shl:{:?}\nrhs_shl:{:?}\nlhs:{:?}\nrhs:{:?}\n={:?}\ntemp:{:?\
                         }",
                        lhs_shl[i], rhs_shl[i], lhs, rhs, product, temp
                    );
                }
                assert_eq!(product.clone().into_wrapping_udiv(&rhs).unwrap(), lhs);
                assert_eq!(zero.clone().into_wrapping_urem(&lhs).unwrap(), zero);
                assert_eq!(zero.clone().into_wrapping_urem(&rhs).unwrap(), zero);
                assert_eq!(lhs.clone().into_wrapping_urem(&one).unwrap(), zero);
                assert_eq!(rhs.clone().into_wrapping_urem(&one).unwrap(), zero);
                assert_eq!(lhs.clone().into_wrapping_urem(&lhs).unwrap(), zero);
                assert_eq!(rhs.clone().into_wrapping_urem(&rhs).unwrap(), zero);
                assert_eq!(product.clone().into_wrapping_urem(&lhs).unwrap(), zero);
                assert_eq!(product.clone().into_wrapping_urem(&rhs).unwrap(), zero);
                assert_eq!(
                    product
                        .clone()
                        .into_wrapping_add(&one)
                        .unwrap()
                        .into_wrapping_urem(&lhs)
                        .unwrap(),
                    one
                );
                assert_eq!(
                    product
                        .clone()
                        .into_wrapping_add(&one)
                        .unwrap()
                        .into_wrapping_urem(&rhs)
                        .unwrap(),
                    one
                );
            }
        }
    }

    mod megafuzz {
        use super::*;
        use crate::bitwidth::BitWidth;
        use core::u64;
        use rand::random;

        #[test]
        fn pull_request_35_regression() {
            let width = BitWidth::new(65).unwrap();
            // arithmetic shift right shift
            assert_eq!(
                ApInt::from([1u64, u64::MAX - (1 << 6)])
                    .into_truncate(width)
                    .unwrap(),
                ApInt::from([1u64, u64::MAX - (1 << 10)])
                    .into_truncate(width)
                    .unwrap()
                    .into_wrapping_ashr(4)
                    .unwrap()
            );
            // multiplication related
            let v1 = ApInt::from((1u128 << 64) | (7u128)).into_zero_resize(width);
            let v2 = ApInt::unsigned_max_value(width)
                .into_wrapping_shl(64)
                .unwrap();
            let v3 = v1.clone().into_wrapping_mul(&v2).unwrap();
            assert_eq!(v1, ApInt::from([1u64, 7]).into_zero_resize(width));
            assert_eq!(v2, ApInt::from([1u64, 0]).into_zero_resize(width));
            assert_eq!(v3, ApInt::from([1u64, 0]).into_zero_resize(width));
            let width = BitWidth::new(193).unwrap();
            let v3 = ApInt::from([0u64, 0, 17179852800, 1073676288])
                .into_zero_resize(width)
                .into_wrapping_mul(&ApInt::from(1u128 << 115).into_zero_resize(width))
                .unwrap();
            assert_eq!(
                v3,
                ApInt::from([0u64, 0, 17179852800, 1073676288])
                    .into_wrapping_shl(115)
                    .unwrap()
                    .into_zero_resize(width)
            );
        }

        // throws all the functions together for an identities party. If one function
        // breaks, the whole thing should break.
        fn identities(
            size: usize,
            width: BitWidth,
            zero: &ApInt,
            lhs: ApInt,
            rhs: ApInt,
            third: ApInt,
        ) {
            // basic addition and subtraction tests
            let shift = random::<usize>() % size;
            let mut temp = lhs.clone().into_wrapping_inc();
            assert_eq!(
                temp,
                lhs.clone()
                    .into_wrapping_add(
                        &ApInt::unsigned_max_value(BitWidth::w1())
                            .into_zero_resize(width)
                    )
                    .unwrap()
            );
            assert_eq!(
                temp,
                lhs.clone()
                    .into_wrapping_sub(&ApInt::all_set(width))
                    .unwrap()
            );
            temp.wrapping_dec();
            assert_eq!(temp, lhs);
            temp.wrapping_dec();
            assert_eq!(
                temp,
                lhs.clone()
                    .into_wrapping_sub(
                        &ApInt::unsigned_max_value(BitWidth::w1())
                            .into_zero_resize(width)
                    )
                    .unwrap()
            );
            assert_eq!(
                temp,
                lhs.clone()
                    .into_wrapping_add(&ApInt::all_set(width))
                    .unwrap()
            );
            temp.wrapping_inc();
            assert_eq!(temp, lhs);

            // power of two multiplication and division shifting tests
            let mut tmp1 = ApInt::unsigned_max_value(BitWidth::w1())
                .into_zero_resize(width)
                .into_wrapping_shl(shift)
                .unwrap();
            assert_eq!(
                lhs.clone().into_wrapping_shl(shift).unwrap(),
                lhs.clone().into_wrapping_mul(&tmp1).unwrap()
            );
            // negation test also
            assert_eq!(
                lhs.clone()
                    .into_wrapping_neg()
                    .into_wrapping_shl(shift)
                    .unwrap(),
                lhs.clone()
                    .into_wrapping_mul(
                        &ApInt::unsigned_max_value(width)
                            .into_wrapping_shl(shift)
                            .unwrap()
                    )
                    .unwrap()
            );
            assert_eq!(
                lhs.clone().into_wrapping_lshr(shift).unwrap(),
                lhs.clone().into_wrapping_udiv(&tmp1).unwrap()
            );
            if (shift == (size - 1)) && (lhs == tmp1) {
                // unfortunate numerical corner case where the result of the shift is -1
                // but the division ends up as +1
                assert_eq!(
                    lhs.clone().into_wrapping_sdiv(&tmp1).unwrap(),
                    ApInt::unsigned_max_value(BitWidth::w1()).into_zero_resize(width)
                );
            } else {
                let mut tmp0 = lhs.clone();
                ApInt::wrapping_sdivrem_assign(&mut tmp0, &mut tmp1).unwrap();
                // make it a floored division
                if lhs.msb() && !tmp1.is_zero() {
                    tmp0.wrapping_dec();
                }
                assert_eq!(tmp0, lhs.clone().into_wrapping_ashr(shift).unwrap());
            }
            let rand_width = BitWidth::new((random::<usize>() % size) + 1).unwrap();
            // wrapping multiplication test
            assert_eq!(
                lhs.clone()
                    .into_zero_extend(BitWidth::new(size * 2).unwrap())
                    .unwrap()
                    .into_wrapping_mul(
                        &rhs.clone()
                            .into_zero_extend(BitWidth::new(size * 2).unwrap())
                            .unwrap()
                    )
                    .unwrap()
                    .into_zero_resize(rand_width),
                lhs.clone()
                    .into_wrapping_mul(&rhs)
                    .unwrap()
                    .into_zero_resize(rand_width)
            );
            let tot_leading_zeros = lhs.leading_zeros() + rhs.leading_zeros();
            let anti_overflow_mask = if tot_leading_zeros < size {
                if rhs.leading_zeros() == 0 {
                    ApInt::zero(width)
                } else {
                    ApInt::unsigned_max_value(BitWidth::from(rhs.leading_zeros()))
                        .into_zero_extend(width)
                        .unwrap()
                }
            } else {
                ApInt::unsigned_max_value(width)
            };
            let mul = (lhs.clone() & &anti_overflow_mask)
                .into_wrapping_mul(&rhs)
                .unwrap();
            if rhs != *zero {
                let rem = third.clone().into_wrapping_urem(&rhs).unwrap();
                let mut temp0 = mul.clone();
                if !temp0.overflowing_uadd_assign(&rem).unwrap() {
                    let mut temp1 = rhs.clone();
                    let mul_plus_rem = temp0.clone();
                    ApInt::wrapping_udivrem_assign(&mut temp0, &mut temp1).unwrap();
                    if temp0 != (lhs.clone() & &anti_overflow_mask) {
                        panic!(
                            "wrong div\nlhs:{:?}\nactual:{:?}\nrhs:{:?}\nthird:{:?}\\
                             \
                             nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:\
                             {:?}",
                            lhs,
                            (lhs.clone() & &anti_overflow_mask),
                            rhs,
                            third,
                            rem,
                            mul,
                            mul_plus_rem,
                            temp0,
                            temp1
                        )
                    }
                    if temp1 != rem {
                        panic!(
                            "wrong rem\nlhs:{:?}\nactual:{:?}\nrhs:{:?}\nthird:{:?}\\
                             \
                             nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:\
                             {:?}",
                            lhs,
                            (lhs.clone() & &anti_overflow_mask),
                            rhs,
                            third,
                            rem,
                            mul,
                            mul_plus_rem,
                            temp0,
                            temp1
                        )
                    }
                }
            }
        }

        // random length AND, XOR, and OR fuzzer;
        fn fuzz_random(size: usize, iterations: usize) {
            let width = BitWidth::new(size).unwrap();
            let mut lhs = ApInt::from(0u8).into_zero_resize(width);
            let mut rhs = ApInt::from(0u8).into_zero_resize(width);
            let mut third = ApInt::from(0u8).into_zero_resize(width);
            let zero = ApInt::from(0u8).into_zero_resize(width);
            for _ in 0..iterations {
                let mut r0 = (random::<u32>() % (size as u32)) as usize;
                if r0 == 0 {
                    r0 = 1;
                }
                let ones = ApInt::unsigned_max_value(BitWidth::new(r0).unwrap())
                    .into_zero_extend(width)
                    .unwrap();
                let r1 = (random::<u32>() % (size as u32)) as usize;
                // circular shift
                let mask = if r1 == 0 {
                    ones.clone()
                } else {
                    ones.clone().into_wrapping_shl(r1).unwrap()
                        | (&ones
                            .clone()
                            .into_wrapping_lshr((size - r1) as usize)
                            .unwrap())
                };
                // assert_eq!(mask,ones.into_rotate_left(r1 as usize).unwrap());
                match (random(), random(), random(), random()) {
                    (false, false, false, false) => lhs |= &mask,
                    (false, false, false, true) => lhs &= &mask,
                    (false, false, true, false) => lhs ^= &mask,
                    (false, false, true, true) => lhs ^= &mask,
                    (false, true, false, false) => rhs |= &mask,
                    (false, true, false, true) => rhs &= &mask,
                    (false, true, true, false) => rhs ^= &mask,
                    (false, true, true, true) => rhs ^= &mask,
                    (true, false, false, false) => third |= &mask,
                    (true, false, false, true) => third &= &mask,
                    (true, false, true, false) => third ^= &mask,
                    (true, false, true, true) => third ^= &mask,
                    (true, true, false, false) => rhs |= &mask,
                    (true, true, false, true) => rhs &= &mask,
                    (true, true, true, false) => rhs ^= &mask,
                    (true, true, true, true) => rhs ^= &mask,
                }
                identities(size, width, &zero, lhs.clone(), lhs.clone(), rhs.clone());
                identities(size, width, &zero, lhs.clone(), rhs.clone(), third.clone());
                identities(size, width, &zero, rhs.clone(), lhs.clone(), third.clone());
                identities(size, width, &zero, third.clone(), lhs.clone(), rhs.clone());
                identities(size, width, &zero, lhs.clone(), third.clone(), rhs.clone());
                identities(size, width, &zero, third.clone(), rhs.clone(), lhs.clone());
                identities(size, width, &zero, rhs.clone(), third.clone(), lhs.clone());
            }
        }

        macro_rules! explode {
            ($cd:ident, $temp:ident, $i_zero:ident, $i_one:ident, $inner:tt) => {{
                for $i_zero in 0..(2usize.pow(($cd * 2) as u32)) {
                    let mut $temp: Vec<u64> = Vec::with_capacity($cd);
                    for $i_one in 0..$cd {
                        match ($i_zero >> ($i_one * 2)) & 0b11 {
                            0b0 => $temp.push(0),
                            0b1 => $temp.push(1),
                            0b10 => $temp.push(u64::MAX - 1),
                            0b11 => $temp.push(u64::MAX),
                            _ => unreachable!(),
                        }
                    }
                    $inner
                }
            }};
        }

        // edge and corner case fuzzer
        fn fuzz_edge(size: usize) {
            let width = BitWidth::new(size).unwrap();
            let zero = ApInt::from(0u8).into_zero_resize(width);
            let cd = if (size % 64) == 0 {
                size / 64
            } else {
                (size / 64) + 1
            };
            explode!(cd, temp0, i0, i1, {
                explode!(cd, temp1, i1, i2, {
                    explode!(cd, temp2, i2, i3, {
                        identities(
                            size,
                            width,
                            &zero,
                            ApInt::from_vec_u64(temp0.clone())
                                .unwrap()
                                .into_truncate(size)
                                .unwrap(),
                            ApInt::from_vec_u64(temp1.clone())
                                .unwrap()
                                .into_truncate(size)
                                .unwrap(),
                            ApInt::from_vec_u64(temp2.clone())
                                .unwrap()
                                .into_truncate(size)
                                .unwrap(),
                        );
                    })
                })
            })
        }

        #[test]
        fn fuzz_test() {
            assert_eq!(
                ApInt::from_vec_u64(vec![32u64, 234, 23]).unwrap(),
                ApInt::from([32u64, 234, 23])
            );
            let a = 10000;
            fuzz_random(1, a);
            fuzz_random(2, a);
            fuzz_random(3, a);
            fuzz_random(31, a);
            fuzz_random(32, a);
            fuzz_random(33, a);
            fuzz_random(63, a);
            fuzz_random(64, a);
            fuzz_random(65, a);
            fuzz_random(127, a);
            fuzz_random(128, a);
            fuzz_random(129, a);
            fuzz_random(191, a);
            fuzz_random(192, a);
            fuzz_random(193, a);
            fuzz_random(255, a);
            fuzz_random(256, a);
            fuzz_edge(63);
            fuzz_edge(64);
            fuzz_edge(65);
            fuzz_edge(127);
            fuzz_edge(128);
            fuzz_edge(129);
            fuzz_edge(191);
            fuzz_edge(192);
            // very expensive
            // fuzz_random(512, a);
            // fuzz_random(777, a);
            // fuzz_random(16*64, a);
            // fuzz_edge(193);
            // fuzz_edge(255);
            // fuzz_edge(256);
        }
    }
}
