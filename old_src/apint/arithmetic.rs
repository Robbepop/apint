use apint::{ApInt};
use apint::utils::DataAccessMut;
use apint::utils::{ZipDataAccessMutSelf::{Inl, Ext},ZipDataAccessMutBoth};
use traits::{Width};
use errors::{DivOp, Error, Result};
use digit;
use digit::{Digit, DoubleDigit};
use utils::{try_forward_bin_mut_impl, forward_mut_impl};

use std::ops::{
    Neg,
    Add,
    Sub,
    Mul,
    AddAssign,
    SubAssign,
    MulAssign
};

/// # Division Operations
/// 
/// **Note**: unless otherwise noted in the function specific documentation,
/// 
/// - The functions do **not** allocate memory.
/// - The function works for both signed and unsigned interpretations of an `ApInt`. In other words,
///     in the low-level bit-wise representation there is no difference between a signed and
///     unsigned operation by the function on fixed bit-width integers. (Cite: LLVM)
/// 
/// In almost all integer division algorithms where "just" the quotient is calculated, the remainder
/// is also produced and actually exists in memory (or at least is only one O(n) operation away)
/// prior to being dropped or overwritten, and vice versa for remainder only calculations. Note here
/// that functions with `div` in their names (e.g. `wrapping_div`) should really be called `quo`
/// (quotient) functions, because the division process produces both the quotient and remainder.
/// However, to stay with Rust's naming scheme we have kept `div` naming. The instruction for
/// division on many CPUs sets registers to both results of the division process, and compilers will
/// detect if code uses both results and only use one division instruction. There is no such
/// detection for `ApInt`s, and thus the `divrem` and `remdiv` type instructions exist to explicitly
/// use just one division function for both results.
/// 
/// ## Performance
/// 
/// All of the division functions in this `impl` quickly check for various edge cases and use an
/// efficient algorithm for these cases.
/// Small here means both small ApInt `BitWidth` and/or small **unsigned** numerical significance.
/// (Signed division works, but two's complement negative numbers may have a large number of
/// leading ones, leading to potential inefficiency.)
/// 
/// - division of zero by any size integer (no allocation)
/// - division of small (1 `Digit`) integers (no allocation)
/// - any division that will lead to the quotient being zero or one (no allocation)
/// - division of any integer by small (1 `Digit`) very small (0.5 `Digit`) integers (no allocation)
/// - division where the number of leading zeros of both arguments are within one `Digit` (less
///     allocation than what long division normally requires)
/// - during long division, the algorithm may encounter a case from above and will use that instead
/// - division of medium size (<= 512 bits) integers
/// 
/// Currently, algorithms faster than 𝒪(n^2) are not implemented, so large integer division may be
/// very slow compared to other algorithms.
impl ApInt {
    //Note: the invariant of `ApInt`s where unused bits beyond the bit width must be all zero is
    //used heavily here, so that no `clear_unused_bits` needs to be used.

    /// This function is intended to be inlined into all of the unsigned quotient and remainder
    /// functions for optimal assembly.
    /// `duo` is divided by `div`, and the quotient is assigned to `duo` and remainder assigned
    /// to `div`
    /// `false` is returned if division by zero happened. Nothing is modified in the case of
    /// division by zero.
    #[inline]
    pub(crate) fn aarons_algorithm_divrem(duo: &mut [Digit], div: &mut [Digit]) -> bool {
        //Some parts were put into their own functions and macros because indentation levels were
        //getting too high, even for me.

        //The algorithm here is just like the algorithm in
        //https://github.com/AaronKutch/specialized-div-rem,
        //except that there are more branches and preconditions. There are comments in this function
        //such as  `//quotient is 0 or 1 check` which correspond to comments in that function.
        
        //assumptions:
        //  *ini_duo_sd > 0
        //  *div_sd == 0
        //modifies `duo` to produce the quotient and returns the remainder
        #[inline(always)]
        fn large_div_by_small(duo: &mut [Digit], ini_duo_sd: usize, div: &mut [Digit]) {
            let div_small = div[0];
            let (mut quo,mut rem) = duo[ini_duo_sd].wrapping_divrem(div_small);
            duo[ini_duo_sd] = quo;
            for duo_sd_sub1 in (0..ini_duo_sd).rev() {
                let duo_double = DoubleDigit::from_lo_hi(duo[duo_sd_sub1],rem);
                let temp = duo_double.wrapping_divrem(div_small.dd());
                //the high part is guaranteed to zero out when this is subtracted,
                //so only the low parts need to be calculated
                quo = temp.0.lo();
                rem = temp.1.lo();
                duo[duo_sd_sub1] = quo;
            }
            div[0] = rem;
        }

        //assumptions:
        //  *ini_duo_sd > 0
        //  *div_sd == 0
        //  *div[0].leading_zeros >= 32
        #[inline(always)]
        fn large_div_by_u32(duo: &mut [Digit], ini_duo_sd: usize, div: &mut [Digit]) {
            let div_u32 = div[0].repr() as u32;
            #[inline(always)]
            fn dd(x: u32) -> Digit {Digit(u64::from(x))}
            #[inline(always)]
            fn lo(x: Digit) -> u32 {x.repr() as u32}
            #[inline(always)]
            fn hi(x: Digit) -> u32 {(x.repr() >> 32) as u32}
            #[inline(always)]
            fn from_lo_hi(lo: u32, hi: u32) -> Digit {Digit(u64::from(lo) | (u64::from(hi) << 32))}
            #[inline(always)]
            fn wrapping_divrem(x: u32, y: u32) -> (u32,u32) {(x.wrapping_div(y),x.wrapping_rem(y))}
            let (mut quo_hi,mut rem_hi) = wrapping_divrem(hi(duo[ini_duo_sd]),div_u32);
            let duo_double = from_lo_hi(lo(duo[ini_duo_sd]), rem_hi);
            let temp = duo_double.wrapping_divrem(dd(div_u32));
            let mut quo_lo = lo(temp.0);
            let mut rem_lo = lo(temp.1);
            duo[ini_duo_sd] = from_lo_hi(quo_lo,quo_hi);
            for duo_sd_sub1 in (0..ini_duo_sd).rev() {
                let duo_double_hi = from_lo_hi(hi(duo[duo_sd_sub1]),rem_lo);
                let temp_hi = duo_double_hi.wrapping_divrem(dd(div_u32));
                quo_hi = lo(temp_hi.0);
                rem_hi = lo(temp_hi.1);
                let duo_double_lo = from_lo_hi(lo(duo[duo_sd_sub1]),rem_hi);
                let temp_lo = duo_double_lo.wrapping_divrem(dd(div_u32));
                quo_lo = lo(temp_lo.0);
                rem_lo = lo(temp_lo.1);
                duo[duo_sd_sub1] = from_lo_hi(quo_lo,quo_hi);
            }
            div[0] = Digit(rem_lo as u64);
        }

        // modifies the `$array` to be the two's complement of itself, all the way up to a `$len`
        // number of digits.
        macro_rules! twos_complement {
            ($len:expr, $array:ident) => {
                for i0 in 0..$len {
                    let bitnot = !$array[i0];
                    match bitnot.overflowing_add(Digit::one()) {
                        (v,false) => {
                            $array[i0] = v;
                            for i1 in (i0 + 1)..$len {
                                $array[i1] = !$array[i1]
                            }
                            break;
                        }
                        (v,true) => {
                            $array[i0] = v;
                        }
                    }
                }
            };
        }

        // uge stands for "unsigned greater or equal to"
        // This checks for `$lhs >= $rhs` (checking only up to $lhs_len and $rhs_len respectively),
        // and runs `$ge_branch` if true and `$ln_branch` otherwise
        macro_rules! uge {
            ($lhs_len:expr,
            $lhs:ident,
            $rhs_len:expr,
            $rhs:ident,
            $ge_branch:block,
            $ln_branch:block) => {
                let mut b0 = false;
                //allows lhs.len() to be smaller than rhs.len()
                for i in ($lhs_len..$rhs_len).rev() {
                    if $rhs[i] != Digit::zero() {
                        b0 = true;
                        break
                    }
                }
                if b0 || ({
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
                }) {$ln_branch} else {$ge_branch}
            };
        }

        //ugt stands for "unsigned greater than"
        // This checks for `$lhs > $rhs` (checking only up to $lhs_len and $rhs_len respectively),
        // and runs `$gt_branch` if true and `$le_branch` otherwise
        macro_rules! ugt {
            ($lhs_len:expr,
            $lhs:ident,
            $rhs_len:expr,
            $rhs:ident,
            $gt_branch:block,
            $le_branch:block) => {
                let mut b0 = false;
                //allows lhs.len() to be smaller than rhs.len()
                for i in ($lhs_len..$rhs_len).rev() {
                    if $rhs[i] != Digit::zero() {
                        b0 = true;
                        break
                    }
                }
                if b0 || ({
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
                }) {$le_branch} else {$gt_branch}
            };
        }

        //assigns `$sum + $sub` to `$target`,
        //and zeros out `$sum` except for it sets `$sum[0]` to `$val`
        macro_rules! special0 {
            ($len:expr,$sum:ident,$sub:ident,$target:ident,$val:expr) => {{
                //subtraction (`sub` is the two's complement of some value)
                let (sum, mut carry) = $sum[0].carrying_add($sub[0]);
                $target[0] = sum;
                $sum[0] = $val;
                for i in 1..($len-1) {
                    let temp = $sum[i].dd()
                        .wrapping_add($sub[i].dd())
                        .wrapping_add(carry.dd());
                    $target[i] = temp.lo();
                    $sum[i].unset_all();
                    carry = temp.hi();
                }
                $target[$len-1] = $sum[$len-1]
                    .wrapping_add($sub[$len-1])
                    .wrapping_add(carry);
                $sum[$len-1].unset_all();
            }}
        }

        //assigns `$sum + $sub` to `$target`,
        //and assigns `$val + $add` to `$sum`
        macro_rules! special1 {
            ($len:expr,$sum:ident,$sub:ident,$target:ident,$val:expr,$add:ident) => {{
                //subtraction (`sub` is the two's complement of some value)
                let (temp, mut carry) = $sum[0].carrying_add($sub[0]);
                $target[0] = temp;
                for i in 1..($len-1) {
                    let temp = $sum[i].dd()
                        .wrapping_add($sub[i].dd())
                        .wrapping_add(carry.dd());
                    $target[i] = temp.lo();
                    carry = temp.hi();
                }
                $target[$len-1] = $sum[$len-1]
                    .wrapping_add($sub[$len-1])
                    .wrapping_add(carry);
                let (temp, mut carry) = $add[0].carrying_add($val);
                $sum[0] = temp;
                for i0 in 1..$len {
                    if carry == Digit::zero() {
                        for i1 in i0..$len {
                            $sum[i1] = $add[i1];
                            break
                        }
                    }
                    let temp = $add[i0].carrying_add(carry);
                    $sum[i0] = temp.0;
                    carry = temp.1;
                }
            }}
        }

        //assigns `$sum + $add` to `$sum`
        macro_rules! add {
            ($len:expr,$sum:ident,$add:ident) => {{
                let (sum, mut carry) = $sum[0].carrying_add($add[0]);
                $sum[0] = sum;
                for i in 1..($len-1) {
                    let temp = $sum[i].dd()
                        .wrapping_add($add[i].dd())
                        .wrapping_add(carry.dd());
                    $sum[i] = temp.lo();
                    carry = temp.hi();
                }
                $sum[$len-1] = $sum[$len-1]
                    .wrapping_add($add[$len-1])
                    .wrapping_add(carry);
            }}
        }

        //assumes that:
        //ini_duo_sd > 1
        //div_sd > 1
        #[inline(always)]
        fn large_div_by_large(
            len: usize, //equal to the length of `duo` and `div`, must be > 2
            duo: &mut [Digit], //the dividend which will become the quotient
            ini_duo_sd: usize, //the initial most significant digit of `duo`
            div: &mut [Digit], //the divisor which will become the remainder
            div_sd: usize //the most significant digit of `div`
        ) {
            let ini_duo_lz = duo[ini_duo_sd].leading_zeros() as usize;
            let div_lz = div[div_sd].leading_zeros() as usize;
            //number of significant bits
            let ini_duo_sb = (ini_duo_sd * digit::BITS) + (digit::BITS - (ini_duo_lz as usize));
            let div_sb = (div_sd * digit::BITS) + (digit::BITS - div_lz);
            //quotient is 0 precheck
            if ini_duo_sb < div_sb {
                //the quotient should be 0 and remainder should be `duo`
                for i in 0..=ini_duo_sd {
                    div[i] = duo[i];
                    duo[i].unset_all();
                }
                for i in (ini_duo_sd + 1)..=div_sd {
                    div[i].unset_all();
                }
                return
            }
            //quotient is 0 or 1 check
            if ini_duo_sb == div_sb {
                let place = ini_duo_sd + 1;
                uge!(place,duo,place,div,
                    {
                        twos_complement!(place,div);
                        special0!(place,duo,div,div,Digit::one());
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
            //difference between the places of the significant bits
            if ini_bits < digit::BITS {
                //the `mul` or `mul - 1` algorithm
                let (duo_sig_dd, div_sig_dd) = if ini_duo_lz == 0 {
                    //avoid shr overflow
                    (
                        DoubleDigit::from_lo_hi(duo[ini_duo_sd - 1], duo[ini_duo_sd]),
                        DoubleDigit::from_lo_hi(div[ini_duo_sd - 1], div[ini_duo_sd]) 
                    )
                } else {
                    (
                        (duo[ini_duo_sd].dd() << (ini_duo_lz + digit::BITS)) |
                        (duo[ini_duo_sd - 1].dd() << ini_duo_lz) |
                        (duo[ini_duo_sd - 2].dd() >> (digit::BITS - ini_duo_lz)),
                        (div[ini_duo_sd].dd() << (ini_duo_lz + digit::BITS)) |
                        (div[ini_duo_sd - 1].dd() << ini_duo_lz) |
                        (div[ini_duo_sd - 2].dd() >> (digit::BITS - ini_duo_lz))
                    )
                };
                let mul = duo_sig_dd.wrapping_div(div_sig_dd).lo();
                //Allocation could be avoided but it would involve more long division to recover
                //`div`.
                //this will become `-(div * mul)`
                let mut sub: Vec<Digit> = Vec::with_capacity(len);
                //first digit done and carry
                let temp = mul.carrying_mul(div[0]);
                sub.push(temp.0);
                let mut carry = temp.1;
                //middle of row
                for i in 1..div_sd {
                    let temp = mul.carrying_mul_add(div[i], carry);
                    sub.push(temp.0);
                    carry = temp.1;
                }
                //final digit, test for `div * mul > duo`, and then form the two's complement
                if div_sd == len - 1 {
                    let temp = mul.carrying_mul_add(div[div_sd], carry);
                    sub.push(temp.0);
                    if temp.1 != Digit::zero() {
                        //overflow
                        //the quotient should be `mul - 1` and remainder should be
                        //`duo + (div - div*mul)`
                        twos_complement!(len, sub);
                        add!(len,sub,div);
                        special0!(len,duo,sub,div,mul.wrapping_sub(Digit::one()));
                        return
                    }
                    //if `div * mul > duo`
                    ugt!(len,sub,len,duo,
                        {
                            twos_complement!(len, sub);
                            add!(len,sub,div);
                            special0!(len,duo,sub,div,mul.wrapping_sub(Digit::one()));
                            return
                        },
                        {
                            //the quotient is `mult` and remainder is `duo - (div * mult)`
                            twos_complement!(len, sub);
                            special0!(len,duo,sub,div,mul);
                            return
                        }
                    );
                } else {
                    let temp = mul.carrying_mul_add(div[div_sd], carry);
                    sub.push(temp.0);
                    sub.push(temp.1);
                    for _ in sub.len()..len {
                        sub.push(Digit::zero());
                    }
                    //if `div * mul > duo`
                    ugt!(len,sub,len,duo,
                        {
                            twos_complement!(len, sub);
                            add!(len,sub,div);
                            special0!(len,duo,sub,div,mul.wrapping_sub(Digit::one()));
                            return
                        },
                        {
                            //the quotient is `mult` and remainder is `duo - (div * mult)`
                            twos_complement!(len, sub);
                            special0!(len,duo,sub,div,mul);
                            return
                        }
                    );
                }
            }
            let mut duo_sd = ini_duo_sd;
            let mut duo_lz = ini_duo_lz;
            //the number of lesser significant digits and bits not a part of `div_sig_d`
            let div_lesser_bits = digit::BITS - (div_lz as usize) + (digit::BITS * (div_sd - 1));
            //the most significant `Digit` bits of div
            let div_sig_d = if div_lz == 0 {
                div[div_sd]
            } else {
                (div[div_sd] << div_lz) | (div[div_sd - 1] >> (digit::BITS - div_lz))
            };
            //has to be a `DoubleDigit` in case of overflow
            let div_sig_d_add1 = div_sig_d.dd().wrapping_add(Digit::one().dd());
            let mut duo_lesser_bits;
            let mut duo_sig_dd;
            //TODO: fix sizes here and below
            let quo_potential = len;
                //if ini_bits % digit::BITS == 0 {ini_bits / digit::BITS}
                //else {(ini_bits / digit::BITS) + 1};
            let mut quo: Vec<Digit> = vec![Digit::zero(); quo_potential as usize];
            loop {
                duo_lesser_bits = (digit::BITS - (duo_lz as usize)) + (digit::BITS * (duo_sd - 2));
                duo_sig_dd = if duo_lz == 0 {
                    DoubleDigit::from_lo_hi(duo[duo_sd - 1],duo[duo_sd])
                } else {
                    (duo[duo_sd].dd() << (duo_lz + digit::BITS)) |
                    (duo[duo_sd - 1].dd() << duo_lz) |
                    (duo[duo_sd - 2].dd() >> (digit::BITS - duo_lz))
                };
                if duo_lesser_bits >= div_lesser_bits {
                    let bits = duo_lesser_bits - div_lesser_bits;
                    //bits_ll is the number of lesser bits in the digit that contains lesser and
                    //greater bits
                    let (digits, bits_ll) = (bits / digit::BITS, bits % digit::BITS);
                    //Unfortunately, `mul` here can be up to (2^2n - 1)/(2^(n-1)), where `n`
                    //is the number of bits in a `Digit`. This means that an `n+1` bit
                    //integer is needed to store mul. Because only one extra higher bit is involved,
                    //the algebraic simplification `(mul + 2^n)*div` to `mul*div + div*2^n` can be
                    //used when that highest bit is set. This just requires faster and simpler
                    //addition inlining hell instead of long multiplication inlining hell.
                    let mul = duo_sig_dd.wrapping_div(div_sig_d_add1);
                    //add `mul << bits` to `quo`
                    //no inlining hell here because `bits_ll < n` and it takes a shift of `n`
                    //to overflow
                    let split_mul = mul << bits_ll;
                    let (temp, mut carry) = split_mul.lo().carrying_add(quo[digits]);
                    quo[digits] = temp;
                    let temp = split_mul.hi().dd()
                        .wrapping_add(quo[digits + 1].dd())
                        .wrapping_add(carry.dd());
                    quo[digits + 1] = temp.lo();
                    carry = temp.hi();
                    for i in (digits+2)..quo.len() {
                        if carry == digit::ZERO {break}
                        let temp = quo[i].carrying_add(carry);
                        quo[i] = temp.0;
                        carry = temp.1;
                    }
                    //special long division algorithm core.
                    //Note that nearly all branches before this are not just wanted for performance
                    //reasons but are actually required in order to not break this.
                    //these blocks subtract `(mul * div) << bits` from `duo`
                    //check for highest bit set
                    if mul.hi() == Digit::zero() {
                        let mul = mul.lo();
                        //carry for bits that wrap across digit boundaries when `<< bits_ll` applied
                        let (temp0, mut wrap_carry) = (div[0].dd() << bits_ll).lo_hi();
                        //the regular multiplication carry
                        let (temp1, mut mul_carry) = mul.dd().wrapping_mul(temp0.dd()).lo_hi();
                        //this carry includes the two's complement increment carry
                        let (temp2, mut add_carry) = (!temp1).dd()
                            .wrapping_add(duo[digits].dd())
                            .wrapping_add(Digit::one().dd())
                            .lo_hi();
                        duo[digits] = temp2;
                        for i in (digits + 1)..=duo_sd {
                            let temp0 = (
                                (div[i - digits].dd() << bits_ll) | wrap_carry.dd()
                                ).lo_hi();
                            wrap_carry = temp0.1;
                            let temp1 = mul.dd()
                                .wrapping_mul(temp0.0.dd())
                                .wrapping_add(mul_carry.dd())
                                .lo_hi();
                            mul_carry = temp1.1;
                            let temp2 = (!temp1.0).dd()
                                .wrapping_add(duo[i].dd())
                                .wrapping_add(add_carry.dd()).lo_hi();
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
                        // subtract duo by temp1 negated (with the carry from the two's complement
                        //being put into `wrap_carry`) and shifted (with `wrap_carry`)

                        let mul = mul.lo();
                        let (temp0, mut mul_carry) = mul.carrying_mul(div[0]);
                        let temp1 = temp0;
                        let mut add0_carry = Digit::zero();
                        //the increment from the two's complement can be stored in `wrap_carry`
                        let (temp2, mut wrap_carry) =
                            (
                                (!temp1).dd()
                                .wrapping_add(Digit::one().dd())
                                << bits_ll
                            ).lo_hi();
                        let (temp3, mut add1_carry) = temp2.carrying_add(duo[digits]);
                        duo[digits] = temp3;
                        for i in (digits + 1)..=duo_sd {
                            let temp0 = 
                                mul.dd()
                                .wrapping_mul(div[i - digits].dd())
                                .wrapping_add(mul_carry.dd());
                            mul_carry = temp0.hi();
                            let temp1 =
                                temp0.lo().dd()
                                .wrapping_add(div[i - digits - 1].dd())
                                .wrapping_add(add0_carry.dd());
                            add0_carry = temp1.hi();
                            let temp2 =
                                ((!temp1.lo()).dd() << bits_ll)
                                .wrapping_add(wrap_carry.dd());
                            wrap_carry = temp2.hi();
                            let temp3 =
                                temp2.lo().dd()
                                .wrapping_add(duo[i].dd())
                                .wrapping_add(add1_carry.dd());
                            add1_carry = temp3.hi();
                            duo[i] = temp3.lo();
                        }
                    }
                } else {
                    //the `mul` or `mul - 1` algorithm with addition from `quo`
                    let div_sig_dd = if duo_lz == 0 {
                        //avoid shr overflow
                        DoubleDigit::from_lo_hi(div[duo_sd - 1], div[duo_sd])
                    } else {
                        (div[duo_sd].dd() << (duo_lz + digit::BITS)) |
                        (div[duo_sd - 1].dd() << duo_lz) |
                        (div[duo_sd - 2].dd() >> (digit::BITS - duo_lz))
                    };
                    let mul = duo_sig_dd.wrapping_div(div_sig_dd).lo();
                    //I could avoid allocation but it would involve more long division to recover
                    //`div`, followed by a second long multiplication with `mul - 1`.
                    //this will become `-(div * mul)`
                    //note: div_sd != len - 1 because it would be caught by the first `mul` or
                    //`mul-1` algorithm
                    let mut sub: Vec<Digit> = Vec::with_capacity(len);
                    //first digit done and carry
                    let (temp, mut mul_carry) = mul.dd().wrapping_mul(div[0].dd()).lo_hi();
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
                        sub.push(Digit::zero());
                    }
                    let sub_len = sub.len();
                    ugt!(sub_len,sub,len,duo,
                        {
                            //the quotient is `quo + (mult - 1)` and remainder is
                            //`duo + (div - div*mul)`
                            twos_complement!(sub_len, sub);
                            add!(sub_len,sub,div);
                            special1!(sub_len,duo,sub,div,mul.wrapping_sub(Digit::one()),quo);
                            return
                        },
                        {
                            //the quotient is `quo + mult` and remainder is `duo - (div * mult)`
                            twos_complement!(sub_len, sub);
                            special1!(sub_len,duo,sub,div,mul,quo);
                            return
                        }
                    );
                }
                //find the new `duo_sd`
                for i in (0..=duo_sd).rev() {
                    if duo[i] != Digit::zero() {
                        duo_sd = i;
                        break
                    }
                    if i == 0 {
                        //the quotient should be `quo` and remainder should be zero
                        for i in 0..len {
                            div[i] = Digit::zero();
                            duo[i] = quo[i];
                        }
                        return
                    }
                }
                duo_lz = duo[duo_sd].leading_zeros() as usize;
                let duo_sb = (duo_sd * digit::BITS) + (digit::BITS - duo_lz);
                //`quo` should have 0 or 1 added to it check
                if duo_sb == div_sb {
                    //if `div <= duo`
                    uge!(len,duo,len,div,
                        {
                            //the quotient should be `quo + 1` and remainder should be `duo - div`
                            twos_complement!(len,div);
                            add!(len,div,duo);
                            for i0 in 0..len {
                                match quo[i0].overflowing_add(Digit::one()) {
                                    (v,false) => {
                                        duo[i0] = v;
                                        for i1 in (i0 + 1)..len {
                                            duo[i1] = quo[i1];
                                        }
                                        break;
                                    }
                                    (v,true) => {
                                        duo[i0] = v;
                                    }
                                }
                            }
                            return
                        },
                        {
                            //the quotient should be `quo` and remainder should be `duo`
                            for i in 0..len {
                                div[i] = duo[i];
                                duo[i] = quo[i];
                            }
                            return
                        }
                    );
                }
                //more 0 cases check
                if div_sb > duo_sb {
                    //the quotient should be `quo` and remainder should be `duo`
                    for i in 0..len {
                        div[i] = duo[i];
                        duo[i] = quo[i];
                    }
                    return
                }
                //this can only happen if `div_sd < 2` (because of above branches),
                //but it is not worth it to unroll further
                if duo_sd < 2 {
                    //duo_sd < 2 because of the "if `duo >= div`" branch above
                    //simple division and addition
                    let duo_dd = DoubleDigit::from_lo_hi(duo[0],duo[1]);
                    let div_dd = DoubleDigit::from_lo_hi(div[0],div[1]);
                    let (mul, rem) = duo_dd.wrapping_divrem(div_dd);
                    //the quotient should be `quo + mul` and remainder should be `rem`
                    div[0] = rem.lo();
                    div[1] = rem.hi();
                    let (temp, mut carry) = quo[0].carrying_add(mul.lo());
                    duo[0] = temp;
                    let temp = quo[1].dd()
                        .wrapping_add(mul.hi().dd())
                        .wrapping_add(carry.dd());
                    duo[1] = temp.lo();
                    carry = temp.hi();
                    for i0 in 2..len {
                        if carry == Digit::zero() {
                            for i1 in i0..len {
                                duo[i1] = quo[i1];
                            }
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

        //Note: Special cases are aggressively taken care of throughout this function, both because
        //the core long division algorithm does not work on many edges, and because of optimization.
        //find the most significant non zeroes, check for `duo` < `div`, and check for division by
        //zero
        match div.iter().rposition(|x| x != &Digit::zero()) {
            Some(div_sd) => {
                //the initial most significant nonzero duo digit
                let ini_duo_sd: usize = match duo.iter().rposition(|x| x != &Digit::zero()) {
                    Some(x) => x,
                    None => {
                        //quotient and remainder should be 0
                        //duo is already zero
                        for x in div.iter_mut() {
                            x.unset_all()
                        }
                        return true
                    },
                };
                if ini_duo_sd < div_sd {
                    //the divisor is larger than the dividend
                    //quotient should be 0 and remainder is `duo`
                    for (duo_d,div_d) in duo.iter_mut().zip(div.iter_mut()) {
                        *div_d = *duo_d;
                        (*duo_d).unset_all()
                    }
                    return true
                }
                match (ini_duo_sd == 0, div_sd == 0) {
                    (false,false) => {
                        //ini_duo_sd cannot be 0 or 1 for `large_div_by_large`
                        if ini_duo_sd == 1 {
                            let temp = DoubleDigit::from_lo_hi(duo[0], duo[1]).wrapping_divrem(DoubleDigit::from_lo_hi(div[0],div[1]));
                            duo[0] = temp.0.lo();
                            duo[1] = temp.0.hi();
                            div[0] = temp.1.lo();
                            div[1] = temp.1.hi();
                            return true
                        }
                        large_div_by_large(
                            duo.len(),
                            duo,
                            ini_duo_sd,
                            div,
                            div_sd
                        );
                        return true
                    },
                    (true,false) => unreachable!(),
                    (false,true) => {
                        if div[0].leading_zeros() >= 32 {
                            large_div_by_u32(duo,ini_duo_sd,div);
                            return true
                        } else {
                            large_div_by_small(duo, ini_duo_sd, div);
                            return true
                        }
                    },
                    (true,true) => {
                        let temp = duo[0].wrapping_divrem(div[0]);
                        duo[0] = temp.0;
                        div[0] = temp.1;
                        return true
                    }
                }
            },
            None => return false,
        }
    }

    /// This function is intended to be inlined into all of the unsigned quotient and remainder
    /// functions for optimal assembly.
    /// `duo` is divided by `div`, and the remainder is assigned to `duo` and quotient assigned
    /// to `div`
    /// `false` is returned if division by zero happened. Nothing is modified in the case of
    /// division by zero.
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

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and sets `lhs` equal to the
    /// quotient and `rhs` equal to the remainder. This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_udivrem_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        match ApInt::zip_access_data_mut_both(lhs, rhs)? {
            ZipDataAccessMutBoth::Inl(duo,div) => {
                if *div != Digit::zero() {
                    let temp = duo.wrapping_divrem(*div);
                    *duo = temp.0;
                    *div = temp.1;
                    return Ok(())
                }
            }
            ZipDataAccessMutBoth::Ext(duo,div) => {
                if ApInt::aarons_algorithm_divrem(duo, div) {
                    return Ok(())
                }
            }
        }
        //Note that the typical places `Err` `Ok` are returned is switched. This is because
        //`rhs.is_zero()` is found as part of finding `duo_sd` inside `aarons_algorithm_divrem`,
        //and `lhs.clone()` cannot be performed inside the match statement
		return Err(Error::division_by_zero(DivOp::UnsignedDivRem, lhs.clone()))
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and sets `lhs` equal to the
    /// remainder and `rhs` equal to the quotient. This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_uremdiv_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        match ApInt::zip_access_data_mut_both(lhs, rhs)? {
            ZipDataAccessMutBoth::Inl(duo,div) => {
                if *div != Digit::zero() {
                    let temp = duo.wrapping_divrem(*div);
                    *duo = temp.1;
                    *div = temp.0;
                    return Ok(())
                }
            }
            ZipDataAccessMutBoth::Ext(duo,div) => {
                if ApInt::aarons_algorithm_remdiv(duo, div) {
                    return Ok(())
                }
            }
        }
		return Err(Error::division_by_zero(DivOp::UnsignedRemDiv, lhs.clone()))
    }

    /// Quotient-assigns `lhs` by `rhs` inplace using **unsigned** interpretation.
    /// This function **may** allocate memory.
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
		return Err(Error::division_by_zero(DivOp::UnsignedDiv, self.clone()))
	}

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and returns the quotient.
    /// This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_udiv(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_udiv_assign)
    }

    /// Remainder-assigns `lhs` by `rhs` inplace using **unsigned** interpretation.
    /// This function **may** allocate memory.
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
		return Err(Error::division_by_zero(DivOp::UnsignedRem, self.clone()))
    }

    /// Divides `lhs` by `rhs` using **unsigned** interpretation and returns the remainder.
    /// This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_urem(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_urem_assign)
    }

    /// Divides `lhs` by `rhs` using **signed** interpretation and sets `lhs` equal to the
    /// quotient and `rhs` equal to the remainder. This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_sdivrem_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedDivRem, lhs.clone()))
        }
        let (negate_lhs, negate_rhs) = match ((*lhs).is_negative(), (*rhs).is_negative()) {
            (false,false) => (false,false),
            (true,false) => {
                lhs.wrapping_neg();
                (true, true)
            },
            (false,true) => {
                rhs.wrapping_neg();
                (true, false)
            },
            (true,true) => {
                lhs.wrapping_neg();
                rhs.wrapping_neg();
                (false, true)
            },
        };
        ApInt::wrapping_udivrem_assign(lhs, rhs).unwrap();
        if negate_lhs {lhs.wrapping_neg()}
        if negate_rhs {rhs.wrapping_neg()}
        //clearing unused bits is handled by `wrapping_neg()`
        return Ok(());
    }

    /// Divides `lhs` by `rhs` using **signed** interpretation and sets `lhs` equal to the
    /// remainder and `rhs` equal to the quotient. This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn wrapping_sremdiv_assign(lhs: &mut ApInt, rhs: &mut ApInt) -> Result<()> {
        if rhs.is_zero() {
            return Err(Error::division_by_zero(DivOp::SignedRemDiv, lhs.clone()))
        }
        let (negate_lhs, negate_rhs) = match ((*lhs).is_negative(), (*rhs).is_negative()) {
            (false,false) => (false,false),
            (true,false) => {
                lhs.wrapping_neg();
                (true, true)
            },
            (false,true) => {
                rhs.wrapping_neg();
                (false, true)
            },
            (true,true) => {
                lhs.wrapping_neg();
                rhs.wrapping_neg();
                (true, false)
            },
        };
        ApInt::wrapping_uremdiv_assign(lhs, rhs).unwrap();
        if negate_lhs {lhs.wrapping_neg()}
        if negate_rhs {rhs.wrapping_neg()}
        //clearing unused bits is handled by `wrapping_neg()`
        return Ok(());
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
        let negate_lhs = match ((*self).is_negative(), rhs_clone.is_negative()) {
            (false,false) => false,
            (true,false) => {
                self.wrapping_neg();
                true
            },
            (false,true) => {
                rhs_clone.wrapping_neg();
                true
            },
            (true,true) => {
                self.wrapping_neg();
                rhs_clone.wrapping_neg();
                false
            },
        };
        ApInt::wrapping_udivrem_assign(self, &mut rhs_clone).unwrap();
        if negate_lhs {self.wrapping_neg()}
        //clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Divides `self` by `rhs` using **signed** interpretation and returns the quotient.
    /// This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    /// 
    pub fn into_wrapping_sdiv(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_sdiv_assign)
    }

    /// Remainder-assigns `lhs` by `rhs` inplace using **signed** interpretation.
    /// This function **may** allocate memory.
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
        let negate_lhs = match ((*self).is_negative(), rhs_clone.is_negative()) {
            (false,false) => false,
            (true,false) => {
                self.wrapping_neg();
                true
            },
            (false,true) => {
                rhs_clone.wrapping_neg();
                false
            },
            (true,true) => {
                self.wrapping_neg();
                rhs_clone.wrapping_neg();
                true
            },
        };
        ApInt::wrapping_uremdiv_assign(self, &mut rhs_clone).unwrap();
        if negate_lhs {self.wrapping_neg()}
        //clearing unused bits is handled by `wrapping_neg()`
        Ok(())
    }

    /// Divides `self` by `rhs` using **signed** interpretation and returns the remainder.
    /// This function **may** allocate memory.
    /// 
    /// # Errors
    /// 
    /// - If `self` and `rhs` have unmatching bit widths.
    /// - If division by zero is attempted
    pub fn into_wrapping_srem(self, rhs: &ApInt) -> Result<ApInt> {
        try_forward_bin_mut_impl(self, rhs, ApInt::wrapping_srem_assign)
    }
}

/// ============================================================================
///  Standard `ops` trait implementations.
/// ----------------------------------------------------------------------------
///  **Note:** These ops will panic if their corresponding functions return an
///  error. They may also allocate memory.
/// 
///  `ApInt` implements some `std::ops` traits for improved usability.
///  Only traits for operations that do not depend on the signedness
///  interpretation of the specific `ApInt` instance are actually implemented.
///  Operations like `div` and `rem` are not expected to have an
///  implementation since a favor in unsigned or signed cannot be decided.
/// ============================================================================

impl Neg for ApInt {
    type Output = ApInt;

    fn neg(self) -> Self::Output {
        self.into_wrapping_neg()
    }
}

impl<'a> Neg for &'a ApInt {
    type Output = ApInt;

    fn neg(self) -> Self::Output {
        self.clone().into_wrapping_neg()
    }
}

impl<'a> Neg for &'a mut ApInt {
    type Output = &'a mut ApInt;

    fn neg(self) -> Self::Output {
        self.wrapping_neg();
        self
    }
}

impl<'a> Add<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn add(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_add(rhs).unwrap()
    }
}

impl<'a, 'b> Add<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn add(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_wrapping_add(rhs).unwrap()
    }
}

impl<'a> AddAssign<&'a ApInt> for ApInt {
    fn add_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_add_assign(rhs).unwrap()
    }
}

impl<'a> Sub<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn sub(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_sub(rhs).unwrap()
    }
}

impl<'a, 'b> Sub<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn sub(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_wrapping_sub(rhs).unwrap()
    }
}

impl<'a> SubAssign<&'a ApInt> for ApInt {
    fn sub_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_sub_assign(rhs).unwrap()
    }
}

impl<'a> Mul<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn mul(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_mul(rhs).unwrap()
    }
}

impl<'a, 'b> Mul<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn mul(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_wrapping_mul(rhs).unwrap()
    }
}

impl<'a> MulAssign<&'a ApInt> for ApInt {
    fn mul_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_mul_assign(rhs).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;


    mod div_rem {
        use super::*;
        use bitwidth::BitWidth;
        use std::u64;

        //TODO: add division by zero testing after error refactoring is finished
        //use errors::ErrorKind;
        #[test]
        fn simple() {
            /// does all of the simple division tests
            /// - `$signed`: if the functions are signed divisions or not
            /// - `$fun_assign`: a division function such as `wrapping_udiv_assign` with that
            ///     signature
            /// - `$fun_into`: a division function such as `into_wrapping_udiv` with that signature
            /// - `$fun`: a division function such as `wrapping_udivrem_assign` with that signature
            /// - `$r0`: the quotient or remainder or both of 80 by 7, depending on division
            ///     function type
            /// - `$r1`, `$r2`, `$r3`: 80 by -7, -80 by 7, -80 by -7. These can be 0 if `$signed` is
            ///     false.
            macro_rules! s {
                ($signed:expr,$fun_assign:ident,$fun_into:ident,$r0:expr,$r1:expr,$r2:expr,$r3:expr/*,$div_op:ident*/) => {
                    /*match $fun_assign
                    match ApInt::from(123u8).$fun_into(&ApInt::from(0u8)) {
                        Err(Error{kind: ErrorKind::DivisionByZero{op: DivOp::$div_op, lhs: x}, message: _, annotation: _}) => {
                            assert_eq!(x,ApInt::from(123u8));
                        },
                        _ => unreachable!(),
                    }
                    match ApInt::from(12345678912345689123456789123456789u128).*/
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
                ($signed:expr,$fun:ident,$r0:expr,$r1:expr,$r2:expr,$r3:expr/*,$div_op:ident*/) => {
                    {
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
                    }
                }
            }
            s!(false,wrapping_udiv_assign,into_wrapping_udiv,11i8,0,0,0);
            s!(false,wrapping_urem_assign,into_wrapping_urem,3i8,0,0,0);
            s!(true,wrapping_sdiv_assign,into_wrapping_sdiv,11i8,-11i8,-11i8,11i8);
            s!(true,wrapping_srem_assign,into_wrapping_srem,3i8,3i8,-3i8,-3i8);
            s!(false,wrapping_udivrem_assign,(11i8,3i8),(0,0),(0,0),(0,0));
            s!(false,wrapping_uremdiv_assign,(3i8,11i8),(0,0),(0,0),(0,0));
            s!(true,wrapping_sdivrem_assign,(11i8,3i8),(-11i8,3i8),(-11i8,-3i8),(11i8,-3i8));
            s!(true,wrapping_sremdiv_assign,(3i8,11i8),(3i8,-11i8),(-3i8,-11i8),(-3i8,11i8));
        }

        //NOTE: this test only works if multiplication and a few other functions work
        #[test]
        fn complex() {
            //there are many special case and size optimization paths,
            //so this test must be very rigorous.
            assert_eq!(
                ApInt::from(123u8)
                .into_wrapping_udiv(&ApInt::from(7u8)).unwrap(),
                ApInt::from(17u8));
            assert_eq!(
                ApInt::from([0u64,0,0,123])
                .into_wrapping_udiv(&ApInt::from([0u64,0,0,7])).unwrap(),
                ApInt::from([0u64,0,0,17]));
            assert_eq!(
                ApInt::from([0u64,0,0,0])
                .into_wrapping_udiv(&ApInt::from([0u64,0,0,7])).unwrap(),
                ApInt::from([0u64,0,0,0]));
            assert_eq!(
                ApInt::from([0u64,0,0,3])
                .into_wrapping_udiv(&ApInt::from([0u64,0,0,7])).unwrap(),
                ApInt::from([0u64,0,0,0]));
            assert_eq!(
                ApInt::from([0u64,0,0,0])
                .into_wrapping_udiv(&ApInt::from([0u64,7,0,0])).unwrap(),
                ApInt::from([0u64,0,0,0]));
            assert_eq!(
                ApInt::from([0u64,0,0,7])
                .into_wrapping_udiv(&ApInt::from([0u64,4,0,0])).unwrap(),
                ApInt::from([0u64,0,0,0]));
            assert_eq!(
                ApInt::from([0u64,0,3,0])
                .into_wrapping_udiv(&ApInt::from([0u64,4,0,0])).unwrap(),
                ApInt::from([0u64,0,0,0]));
            assert_eq!(
                ApInt::from([0u64,1,0,0])
                .into_wrapping_udiv(&ApInt::from([0u64,0,0,4])).unwrap(),
                ApInt::from([0u64,0,u64::MAX / 4 + 1,0]));
            assert_eq!(//this one
                ApInt::from([0u64,1,0,0])
                .into_wrapping_udiv(&ApInt::from([0u64,0,1,0])).unwrap(),
                ApInt::from([0u64,0,1,0]));
            assert_eq!(
                ApInt::from([1u64,2,3,4])
                .into_wrapping_udiv(&ApInt::from([1u64,2,3,4])).unwrap(),
                ApInt::from([0u64,0,0,1]));
            assert_eq!(
                ApInt::from([0u64,1,u64::MAX,u64::MAX,u64::MAX,u64::MAX,u64::MAX,u64::MAX])
                .into_wrapping_udiv(&ApInt::from([0u64,0,0,0,0,0,0,2])).unwrap()
                ,ApInt::from([0u64,0,u64::MAX,u64::MAX,u64::MAX,u64::MAX,u64::MAX,u64::MAX]));
            assert_eq!(
                ApInt::from([u64::MAX,u64::MAX - 1,1,u64::MAX - 1,u64::MAX - 1,2,u64::MAX - 1,1])
                .into_wrapping_udiv(&ApInt::from([0,0,0,0,u64::MAX,u64::MAX,0,u64::MAX])).unwrap(),
                ApInt::from([0,0,0,0,u64::MAX,u64::MAX,0,u64::MAX])
            );
            assert_eq!(ApInt::from(61924494876344321u128).into_wrapping_urem(&ApInt::from(167772160u128)).unwrap(),ApInt::from(1u128));
            assert_eq!(ApInt::from([18446744073709551615u64, 18446744073709551615, 1048575, 18446462598732840960]).into_wrapping_urem(&ApInt::from([0u64, 0, 140668768878592, 0])).unwrap(), ApInt::from([0,0, 136545601323007, 18446462598732840960u64]));
            assert_eq!(ApInt::from([1u64, 17293821508111564796, 2305843009213693952]).into_wrapping_urem(&ApInt::from([0u64,1,18446742978492891132])).unwrap(),ApInt::from([0u64,0,0]));
            assert_eq!(ApInt::from([1u64,18446744073692774368,268435456]).into_wrapping_add(&ApInt::from([0u64,1,18446744073709519359])).unwrap().into_wrapping_udiv(&ApInt::from([0u64,1,18446744073709551584])).unwrap(),ApInt::from([0u64,0,18446744073701163008]));
            assert_eq!(ApInt::from([18446744073709551615u64,18446744073709551615,18446739675663040512,2199023255552]).into_wrapping_urem(&ApInt::from([18446744073709551615u64,18446744073709551615,18446739675663040512,2199023255552])).unwrap(),ApInt::from([0u64,0,0,0]));
            assert_eq!(ApInt::from([1u64,18446462598730776592,1047972020113]).into_wrapping_udiv(&ApInt::from([0u64,16383,18446744056529682433])).unwrap(),ApInt::from([0u64,0,2251782633816065]));
            assert_eq!(ApInt::from([54467619767447688u64, 18446739675392512496, 5200531536562092095, 18446744073709551615]).into_wrapping_udiv(&ApInt::from([0u64, 8255, 18446462598732840960, 0])).unwrap(), ApInt::from([0u64,0, 6597337677824, 288230376151678976]));
            let resize = [
                7usize, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 137, 200, 255,
                256, 700, 907, 1024, 2018, 2019,
            ];
            let lhs_shl = [
                0usize, 1, 0, 1, 4, 6, 4, 10, 13, 0, 31, 25, 7, 17, 32, 50, 0, 64, 249, 8, 777, 0,
                900, 0,
            ];
            let rhs_shl = [
                0usize, 0, 1, 1, 3, 5, 4, 14, 10, 0, 0, 25, 0, 18, 32, 49, 100, 64, 0, 256, 64,
                900, 1000, 0,
            ];
            for (i, _) in resize.iter().enumerate() {
                let mut lhs = ApInt::from(5u8)
                    .into_zero_resize(BitWidth::new(resize[i]).unwrap())
                    .into_wrapping_shl(lhs_shl[i])
                    .unwrap();
                let mut rhs = ApInt::from(11u8)
                    .into_zero_resize(BitWidth::new(resize[i]).unwrap())
                    .into_wrapping_shl(rhs_shl[i])
                    .unwrap();
                let mut zero = ApInt::from(0u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
                let mut one = ApInt::from(1u8).into_zero_resize(BitWidth::new(resize[i]).unwrap());
                let mut product = lhs.clone().into_wrapping_mul(&rhs).unwrap();
                assert_eq!(zero.clone().into_wrapping_udiv(&lhs).unwrap(), zero);
                assert_eq!(zero.clone().into_wrapping_udiv(&rhs).unwrap(), zero);
                assert_eq!(lhs.clone().into_wrapping_udiv(&one).unwrap(), lhs);
                assert_eq!(rhs.clone().into_wrapping_udiv(&one).unwrap(), rhs);
                assert_eq!(lhs.clone().into_wrapping_udiv(&lhs).unwrap(), one);
                assert_eq!(rhs.clone().into_wrapping_udiv(&rhs).unwrap(), one);
                let temp = product.clone().into_wrapping_udiv(&lhs).unwrap();
                if temp != rhs {
                    panic!("lhs_shl:{:?}\nrhs_shl:{:?}\nlhs:{:?}\nrhs:{:?}\n={:?}\ntemp:{:?}",lhs_shl[i],rhs_shl[i],lhs,rhs,product,temp);
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
                assert_eq!(product.clone().into_wrapping_add(&one).unwrap().into_wrapping_urem(&lhs).unwrap(), one);
                assert_eq!(product.clone().into_wrapping_add(&one).unwrap().into_wrapping_urem(&rhs).unwrap(), one);
            }
        }
    }