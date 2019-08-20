use crate::info::{BitPos,BitWidth,Error,Result,Width};

use std::ops::{
    BitAnd,
    BitOr,
    BitXor,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,

    Shl,
    Shr,
    ShlAssign,
    ShrAssign,
    Not,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
};

use std::fmt;

/// The type for the internal `Digit` representation.
/// 
/// Must be exactly half the size of `DoubleDigitRepr`.
/// 
/// Note: When changing this to other built in integers, be sure to change `DoubleDigitRepr` and `Digit::BITS`.
pub(crate) type DigitRepr = u64;

/// The type for the internal `DoubleDigit` representation.
/// 
/// Must be exactly double the size of `DigitRepr`.
pub(crate) type DoubleDigitRepr = u128;

const REPR_ONE : DigitRepr = 0x1;
const REPR_ZERO: DigitRepr = 0x0;
const REPR_ONES: DigitRepr = !REPR_ZERO;

/// A (big) digit within an `ApInt` or similar representations.
/// 
/// It uses the `DoubleDigit` as computation unit.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Digit(pub DigitRepr);

/// # Constructors
impl Digit {
    /// The amount of bits within a single `Digit`.
    pub(crate) const BITS: usize = 64;
    pub(crate) const ONE : Digit = Digit(REPR_ONE);
    pub(crate) const ZERO: Digit = Digit(REPR_ZERO);
    pub(crate) const ONES: Digit = Digit(REPR_ONES);

    /// Creates a digit that represents the value `0`.
    /// 
    /// **Note:** In twos-complement this means that all bits are `0`.
    pub fn zero() -> Digit { Digit::ZERO }

    /// Creates a digit that represents the value `1`.
    pub fn one() -> Digit { Digit::ONE	}

    /// Returns `true` if this `Digit` is zero (`0`).
    pub fn is_zero(self) -> bool { self == Digit::ZERO }

    /// Returns `true` if this `Digit` is one (`1`).
    pub fn is_one(self) -> bool { self == Digit::ONE }

    /// Returns `true` if this `Digit` has all bits set.
    pub fn is_all_set(self) -> bool { self == Digit::ONES }

    /// Creates a digit where all bits are initialized to `1`.
    pub fn all_set() -> Digit { Digit::ONES }
}

/// # Utility & helper methods.
impl Digit {
    /// Returns the `Digit`'s value as internal representation.
    pub fn repr(self) -> DigitRepr {
        self.0
    }

    /// Returns a mutable reference to the underlying representation
    /// of this `Digit`.
    pub fn repr_mut(&mut self) -> &mut DigitRepr {
        &mut self.0
    }

    /// Returns the `DoubleDigit` representation of this `Digit`.
    pub(crate) fn dd(self) -> DoubleDigit {
        DoubleDigit(DoubleDigitRepr::from(self.repr()))
    }

    pub(crate) fn leading_zeros(self) -> u32 {
        self.repr().leading_zeros()
    }

    pub(crate) fn wrapping_add(self, other: Digit) -> Self {
        Digit(self.repr().wrapping_add(other.repr()))
    }

    pub(crate) fn carrying_add(self, other: Digit) -> (Digit, Digit) {
        //this is to make sure that the assembly compiles down to the `adc` function
        match self.repr().overflowing_add(other.repr()) {
            (x,false) => (Digit(x),Digit::zero()),
            (x,true) => (Digit(x),Digit::one()),
        }
    }

    pub(crate) fn overflowing_add(self, other: Digit) -> (Digit, bool) {
        match self.repr().overflowing_add(other.repr()) {
            (x,false) => (Digit(x),false),
            (x,true) => (Digit(x),true),
        }
    }

    pub(crate) fn overflowing_sub(self, other: Digit) -> (Digit, bool) {
        match self.repr().overflowing_sub(other.repr()) {
            (x,false) => (Digit(x),false),
            (x,true) => (Digit(x),true),
        }
    }

    pub(crate) fn wrapping_sub(self, other: Digit) -> Self {
        Digit(self.repr().wrapping_sub(other.repr()))
    }

    pub(crate) fn wrapping_mul(self, other: Digit) -> Self {
        Digit(self.repr().wrapping_mul(other.repr()))
    }

    #[cfg(test)]
    pub(crate) fn overflowing_mul(self, other: Digit) -> (Digit, bool) {
        match self.repr().overflowing_mul(other.repr()) {
            (x,false) => (Digit(x), false),
            (x,true) => (Digit(x), true),
        }
    }

    //TODO if and when `carrying_mul` (rust-lang rfc #2417) is stabilized, this function and others in this crate should use `carrying_mul` as the operation
    pub(crate) fn carrying_mul(self, other: Digit) -> (Digit, Digit) {
        let temp = self.dd().wrapping_mul(other.dd());
        (temp.lo(), temp.hi())
    }

    pub(crate) fn wrapping_mul_add(self, mul: Digit, add: Digit) -> Digit {
        Digit(
            self.repr()
                .wrapping_mul(mul.repr())
                .wrapping_add(add.repr()),
        )
    }

    pub(crate) fn carrying_mul_add(self, mul: Digit, add: Digit) -> (Digit, Digit) {
        let temp = self.dd().wrapping_mul(mul.dd()).wrapping_add(add.dd());
        (temp.lo(), temp.hi())
    }

    pub(crate) fn wrapping_divrem(self,other: Digit) -> (Digit,Digit) {
        (self.wrapping_div(other),self.wrapping_rem(other))
    }

    pub(crate) fn wrapping_div(self, other: Digit) -> Self {
        Digit(self.repr().wrapping_div(other.repr()))
    }

    pub(crate) fn wrapping_rem(self, other: Digit) -> Self {
        Digit(self.repr().wrapping_rem(other.repr()))
    }
}

impl Digit {
    /// Validates the given `BitWidth` for `Digit` instances and returns
    /// an appropriate error if the given `BitWidth` is invalid.
    fn verify_valid_bitwidth<W>(self, width: W) -> Result<()>
        where W: Into<BitWidth>
    {
        let width = width.into();
        if width.to_usize() > Digit::BITS {
            return Err(Error::invalid_bitwidth(width.to_usize())
                .with_annotation("Encountered invalid `BitWidth` for operating \
                                          on a `Digit`."))
        }
        Ok(())
    }

    /// Truncates this `Digit` to the given `BitWidth`.
    /// 
    /// This operation just zeros out any bits on this `Digit` 
    /// with bit positions above the given `BitWidth`.
    /// 
    /// # Note
    /// 
    /// This is equal to calling `Digit::retain_last_n`.
    /// 
    /// # Errors
    /// 
    /// - If the given `BitWidth` is invalid for `Digit` instances.
    pub(crate) fn truncate_to<W>(&mut self, to: W) -> Result<()>
        where W: Into<BitWidth>
    {
        let to = to.into();
        self.verify_valid_bitwidth(to)?;
        self.0 &= !(REPR_ONES << to.to_usize());
        Ok(())
    }

    /// Sign extends this `Digit` from a given `BitWidth` to `64` bits.
    /// 
    /// # Note
    /// 
    /// - This can be truncated again to a real target `BitWidth` afterwards if
    ///   the users wishes to.
    /// 
    /// - Implementation inspired by
    ///   [Bit Twiddling Hacks](https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtend).
    /// 
    /// # Errors
    /// 
    /// - If the given `BitWidth` is invalid for `Digit` instances.
    pub(crate) fn sign_extend_from<W>(&mut self, from: W) -> Result<()>
        where W: Into<BitWidth>,
    {
        let from = from.into();
        self.verify_valid_bitwidth(from)?;

        let b = from.to_usize();    // number of bits representing the number in x
        let x = self.repr() as i64; // sign extend this b-bit number to r
        let m: i64 = 1 << (b - 1);       // mask can be pre-computed if b is fixed
        // x = x & ((1 << b) - 1);  // (Skip this if bits in x above position b are already zero.)
                                    // We don't need this step since this condition is an invariant of `Digit`.
        let r: i64 = (x ^ m).wrapping_sub(m);   // resulting sign-extended number
        self.0 = r as u64;
        Ok(())
    }
}

/// # Bitwise access
impl Digit {
    /// Returns the least significant bit, as a `bool`, of this `Digit`.
    /// 
    /// # Note
    /// 
    /// In this context, a `bool` is interpreted as a single bit, where `false`
    /// is 0 and `true` is 1.
    #[inline]
    pub fn least_significant_bit(self) -> bool {
        (self.repr() & 0x1) != 0
    }

    /// Returns `true` if the `n`th bit is set to `1`, else returns `false`.
    /// 
    /// # Errors
    /// 
    /// If the given `n` is greater than the digit size.
    #[inline]
    pub fn get<P>(self, pos: P) -> Result<bool>
        where P: Into<BitPos>
    {
        let pos = pos.into();
        pos.verify_bit_access(&self)?;
        Ok(((self.repr() >> pos.to_usize()) & 0x1) == 1)
    }

    /// Sets the bit at position `pos` to `1`.
    /// 
    /// # Errors
    /// 
    /// If the given `n` is greater than the digit size.
    #[inline]
    pub fn set<P>(&mut self, pos: P) -> Result<()>
        where P: Into<BitPos>
    {
        let pos = pos.into();
        pos.verify_bit_access(self)?;
        self.0 |= 0x1 << pos.to_usize();
        Ok(())
    }

    /// Sets the bit at position `pos` to `0`.
    /// 
    /// # Errors
    /// 
    /// If the given `n` is greater than the digit size.
    #[inline]
    pub fn unset<P>(&mut self, pos: P) -> Result<()>
        where P: Into<BitPos>
    {
        let pos = pos.into();
        pos.verify_bit_access(self)?;
        self.0 &= !(0x1 << pos.to_usize());
        Ok(())
    }

    /// Flips the bit at position `pos`.
    /// 
    /// # Errors
    /// 
    /// If the given `n` is greater than the digit size.
    #[inline]
    pub fn flip<P>(&mut self, pos: P) -> Result<()>
        where P: Into<BitPos>
    {
        let pos = pos.into();
        pos.verify_bit_access(self)?;
        self.0 ^= 0x1 << pos.to_usize();
        Ok(())
    }

    /// Sets all bits in this digit to `1`.
    #[inline]
    pub fn set_all(&mut self) {
        self.0 |= REPR_ONES
    }

    /// Sets all bits in this digit to `0`.
    #[inline]
    pub fn unset_all(&mut self) {
        self.0 &= REPR_ZERO
    }

    /// Flips all bits in this digit.
    #[inline]
    pub fn flip_all(&mut self) {
        self.0 ^= REPR_ONES
    }

    /// Unsets all bits but the last `n` ones.
    /// 
    /// # Note
    /// 
    /// This is equal to calling `Digit::truncate_to`.
    /// 
    /// # Errors
    /// 
    /// If the given `n` is greater than the digit size.
    #[inline]
    pub fn retain_last_n(&mut self, n: usize) -> Result<()> {
        BitPos::from(n).verify_bit_access(self)?;
        self.0 &= !(REPR_ONES << n);
        Ok(())
    }
}

impl fmt::Binary for Digit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.repr().fmt(f)
    }
}

impl fmt::Octal for Digit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.repr().fmt(f)
    }
}

impl fmt::LowerHex for Digit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.repr().fmt(f)
    }
}

impl fmt::UpperHex for Digit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.repr().fmt(f)
    }
}

impl Not for Digit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Digit(!self.repr())
    }
}

impl BitOr for Digit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Digit(self.repr() | rhs.repr())
    }
}

impl BitAnd for Digit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Digit(self.repr() & rhs.repr())
    }
}

impl BitXor for Digit {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Digit(self.repr() ^ rhs.repr())
    }
}

impl BitOrAssign for Digit {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.repr()
    }
}

impl BitAndAssign for Digit {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.repr()
    }
}

impl BitXorAssign for Digit {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.repr()
    }
}

impl Shl<usize> for Digit {
    type Output = Digit;

    fn shl(self, rhs: usize) -> Self::Output {
        Digit(self.repr().wrapping_shl(rhs as u32))
    }
}

impl Shr<usize> for Digit {
    type Output = Digit;

    fn shr(self, rhs: usize) -> Self::Output {
        Digit(self.repr().wrapping_shr(rhs as u32))
    }
}

impl ShlAssign<usize> for Digit {
    fn shl_assign(&mut self, rhs: usize) {
        *self = *self << rhs;
    }
}

impl ShrAssign<usize> for Digit {
    fn shr_assign(&mut self, rhs: usize) {
        *self = *self >> rhs;
    }
}

impl Width for Digit {
    fn width(&self) -> BitWidth {
        BitWidth::from(Digit::BITS)
    }
}

/// A doubled digit.
/// 
/// This is used as a compute unit for `Digit`'s since many `Digit` arithmetic operations
/// may overflow or have carries this is required in order to not lose those overflow- and underflow values.
/// 
/// Has wrapping arithmetics for better machine emulation and improved performance.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct DoubleDigit(pub DoubleDigitRepr);

impl DoubleDigit {
    /// Returns the value as its internal representation.
    pub(crate) fn repr(self) -> DoubleDigitRepr {
        self.0
    }

    /// Returns the hi part of this `DoubleDigit` as `Digit`.
    pub(crate) fn hi(self) -> Digit {
        Digit((self.0 >> Digit::BITS) as DigitRepr)
    }

    /// Returns the hi part of this `DoubleDigit` as `Digit`.
    pub(crate) fn lo(self) -> Digit {
        Digit(self.0 as DigitRepr)
    }

    /// Returns the lo and hi parts of this `DoubleDigit` as `Digit` each.
    pub(crate) fn lo_hi(self) -> (Digit, Digit) {
        (self.lo(), self.hi())
    }

    /// Returns a `DoubleDigit` from the given lo and hi raw `Digit` parts.
    pub(crate) fn from_lo_hi(lo: Digit, hi: Digit) -> DoubleDigit {
        DoubleDigit(DoubleDigitRepr::from(lo.repr()) | (DoubleDigitRepr::from(hi.repr()) << Digit::BITS))
    }

    pub(crate) fn wrapping_add(self, other: DoubleDigit) -> Self {
        DoubleDigit(self.repr().wrapping_add(other.repr()))
    }

    pub(crate) fn wrapping_mul(self, other: DoubleDigit) -> Self {
        DoubleDigit(self.repr().wrapping_mul(other.repr()))
    }

    pub(crate) fn wrapping_div(self, other: DoubleDigit) -> Self {
        self.wrapping_divrem(other).0
    }

    #[cfg(not(feature = "specialized_div_rem"))]
    pub(crate) fn wrapping_divrem(self,other: DoubleDigit) -> (DoubleDigit,DoubleDigit) {
        (
            DoubleDigit(self.repr().wrapping_div(other.repr())),
            DoubleDigit(self.repr().wrapping_rem(other.repr()))
        )
    }

    #[cfg(feature = "specialized_div_rem")]
    pub(crate) fn wrapping_divrem(self,other: DoubleDigit) -> (DoubleDigit,DoubleDigit) {
        let temp = specialized_div_rem::u128_div_rem(self.repr(),other.repr());
        (DoubleDigit(temp.0),DoubleDigit(temp.1))
    }
}

impl Not for DoubleDigit {
    type Output = Self;

    fn not(self) -> Self::Output {
        DoubleDigit(!self.repr())
    }
}

impl BitOr for DoubleDigit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        DoubleDigit(self.repr() | rhs.repr())
    }
}

impl BitAnd for DoubleDigit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        DoubleDigit(self.repr() & rhs.repr())
    }
}

impl Shl<usize> for DoubleDigit {
    type Output = DoubleDigit;

    fn shl(self, rhs: usize) -> Self::Output {
        assert!(rhs < (Digit::BITS * 2));
        DoubleDigit(self.repr().wrapping_shl(rhs as u32))
    }
}

impl Shr<usize> for DoubleDigit {
    type Output = DoubleDigit;

    fn shr(self, rhs: usize) -> Self::Output {
        assert!(rhs < (Digit::BITS * 2));
        DoubleDigit(self.repr().wrapping_shr(rhs as u32))
    }
}

impl Add for DoubleDigit {
    type Output = DoubleDigit;

    fn add(self, rhs: DoubleDigit) -> Self::Output {
        DoubleDigit(self.repr().wrapping_add(rhs.repr()))
    }
}

impl Sub for DoubleDigit {
    type Output = DoubleDigit;

    fn sub(self, rhs: DoubleDigit) -> Self::Output {
        DoubleDigit(self.repr().wrapping_sub(rhs.repr()))
    }
}

impl Mul for DoubleDigit {
    type Output = DoubleDigit;

    fn mul(self, rhs: DoubleDigit) -> Self::Output {
        DoubleDigit(self.repr().wrapping_mul(rhs.repr()))
    }
}

impl Div for DoubleDigit {
    type Output = DoubleDigit;

    fn div(self, rhs: DoubleDigit) -> Self::Output {
        DoubleDigit(self.repr().wrapping_div(rhs.repr()))
    }
}

impl Rem for DoubleDigit {
    type Output = DoubleDigit;

    fn rem(self, rhs: DoubleDigit) -> Self::Output {
        DoubleDigit(self.repr().wrapping_rem(rhs.repr()))
    }
}

impl Width for DoubleDigit {
    fn width(&self) -> BitWidth {
        BitWidth::from(Digit::BITS * 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod double_digit {
        use super::*;
        use crate::info::Width;

        static TEST_VALUES: &[DoubleDigitRepr] = &[0, 1, 2, 10, 42, 1337];

        #[test]
        fn ops_add() {
            fn assert_for(lhs: DoubleDigitRepr, rhs: DoubleDigitRepr) {
                assert_eq!(
                    DoubleDigit(lhs) + DoubleDigit(rhs),
                    DoubleDigit(lhs.wrapping_add(rhs))
                )
            }
            for &lhs in TEST_VALUES {
                for &rhs in TEST_VALUES {
                    assert_for(lhs, rhs)
                }
            }
        }

        #[test]
        fn ops_sub() {
            fn assert_for(lhs: DoubleDigitRepr, rhs: DoubleDigitRepr) {
                assert_eq!(
                    DoubleDigit(lhs) - DoubleDigit(rhs),
                    DoubleDigit(lhs.wrapping_sub(rhs))
                )
            }
            for &lhs in TEST_VALUES {
                for &rhs in TEST_VALUES {
                    assert_for(lhs, rhs)
                }
            }
        }

        #[test]
        fn ops_mul() {
            fn assert_for(lhs: DoubleDigitRepr, rhs: DoubleDigitRepr) {
                assert_eq!(
                    DoubleDigit(lhs) * DoubleDigit(rhs),
                    DoubleDigit(lhs.wrapping_mul(rhs))
                )
            }
            for &lhs in TEST_VALUES {
                for &rhs in TEST_VALUES {
                    assert_for(lhs, rhs)
                }
            }
        }

        #[test]
        fn ops_div() {
            fn assert_for(lhs: DoubleDigitRepr, rhs: DoubleDigitRepr) {
                assert_eq!(
                    DoubleDigit(lhs) / DoubleDigit(rhs),
                    DoubleDigit(lhs.wrapping_div(rhs))
                )
            }
            for &lhs in TEST_VALUES {
                for &rhs in TEST_VALUES {
                    // Avoid division by zero.
                    if rhs != 0 {
                        assert_for(lhs, rhs)
                    }
                }
            }
        }

        #[test]
        fn ops_rem() {
            fn assert_for(lhs: DoubleDigitRepr, rhs: DoubleDigitRepr) {
                assert_eq!(
                    DoubleDigit(lhs) % DoubleDigit(rhs),
                    DoubleDigit(lhs.wrapping_rem(rhs))
                )
            }
            for &lhs in TEST_VALUES {
                for &rhs in TEST_VALUES {
                    // Avoid division by zero.
                    if rhs != 0 {
                        assert_for(lhs, rhs)
                    }
                }
            }
        }

        #[test]
        fn width() {
            for &val in TEST_VALUES {
                assert_eq!(DoubleDigit(val).width(), BitWidth::w128());
            }
        }

        #[test]
        fn repr() {
            fn assert_for(val: DoubleDigitRepr) {
                assert_eq!(DoubleDigit(val).repr(), val)
            }
            for &val in TEST_VALUES {
                assert_for(val)
            }
        }

        #[test]
        fn hi() {
            fn assert_for(input: DoubleDigitRepr, expected: DigitRepr) {
                assert_eq!(DoubleDigit(input).hi(), Digit(expected))
            }
            let test_values = &[
                (0,0),
                (1,0),
                (0x0000_0000_0000_0001_0000_0000_0000_0000, 1),
                (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF),
                (0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF, 0),
                (0x0000_0000_FFFF_FFFF_FFFF_FFFF_0000_0000, 0xFFFF_FFFF),
                (0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF),
                (0x0123_4567_8910_ABCD_EF00_0000_0000_0000, 0x0123_4567_8910_ABCD),
                (0x0000_0000_0000_00FE_DCBA_0198_7654_3210, 0xFE)
            ];
            for &(input, expected) in test_values {
                assert_for(input, expected)
            }
        }

        #[test]
        fn lo() {
            fn assert_for(input: DoubleDigitRepr, expected: DigitRepr) {
                assert_eq!(DoubleDigit(input).lo(), Digit(expected))
            }
            let test_values = &[
                (0,0),
                (1,1),
                (0x0000_0000_0000_0001_0000_0000_0000_0000, 0),
                (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF),
                (0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF),
                (0x0000_0000_FFFF_FFFF_FFFF_FFFF_0000_0000, 0xFFFF_FFFF_0000_0000),
                (0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000, 0),
                (0x0123_4567_8910_ABCD_EF00_0000_0000_0000, 0xEF00_0000_0000_0000),
                (0x0000_0000_0000_00FE_DCBA_0198_7654_3210, 0xDCBA_0198_7654_3210)
            ];
            for &(input, expected) in test_values {
                assert_for(input, expected)
            }
        }

        #[test]
        fn lo_hi() {
            fn assert_for(input: DoubleDigitRepr, expected_hi: DigitRepr, expected_lo: DigitRepr) {
                assert_eq!(DoubleDigit(input).lo_hi(), (Digit(expected_lo), Digit(expected_hi)))
            }
            let test_values = &[
                (0, (0, 0)),
                (1, (0, 1)),
                (0x0000_0000_0000_0001_0000_0000_0000_0000, (1, 0)),
                (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, (0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF)),
                (0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF, (0, 0xFFFF_FFFF_FFFF_FFFF)),
                (0x0000_0000_FFFF_FFFF_FFFF_FFFF_0000_0000, (0xFFFF_FFFF, 0xFFFF_FFFF_0000_0000)),
                (0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000, (0xFFFF_FFFF_FFFF_FFFF, 0)),
                (0x0123_4567_8910_ABCD_EF00_0000_0000_0000, (0x0123_4567_8910_ABCD, 0xEF00_0000_0000_0000)),
                (0x0000_0000_0000_00FE_DCBA_0198_7654_3210, (0x0000_0000_0000_00FE, 0xDCBA_0198_7654_3210))
            ];
            for &(input, (expected_hi, expected_lo)) in test_values {
                assert_for(input, expected_hi, expected_lo)
            }
        }

        #[test]
        fn from_lo_hi() {
            fn assert_for(hi: DigitRepr, lo: DigitRepr, expected: DoubleDigitRepr) {
                assert_eq!(DoubleDigit::from_lo_hi(Digit(lo), Digit(hi)), DoubleDigit(expected))
            }
            let test_values = &[
                (0, (0, 0)),
                (1, (0, 1)),
                (0x0000_0000_0000_0001_0000_0000_0000_0000, (1, 0)),
                (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, (0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF)),
                (0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF, (0, 0xFFFF_FFFF_FFFF_FFFF)),
                (0x0000_0000_FFFF_FFFF_FFFF_FFFF_0000_0000, (0xFFFF_FFFF, 0xFFFF_FFFF_0000_0000)),
                (0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000, (0xFFFF_FFFF_FFFF_FFFF, 0)),
                (0x0123_4567_8910_ABCD_EF00_0000_0000_0000, (0x0123_4567_8910_ABCD, 0xEF00_0000_0000_0000)),
                (0x0000_0000_0000_00FE_DCBA_0198_7654_3210, (0x0000_0000_0000_00FE, 0xDCBA_0198_7654_3210))
            ];
            for &(expected, (hi, lo)) in test_values {
                assert_for(hi, lo, expected)
            }
        }
    }

    mod digit {
        use super::*;
        use crate::info::Width;

        use std::usize;

        static VALID_TEST_POS_VALUES: &[usize] = &[
            0, 1, 2, 3, 10, 32, 42, 48, 63
        ];

        static INVALID_TEST_POS_VALUES: &[usize] = &[
            64, 65, 100, 1337, usize::MAX
        ];

        static TEST_DIGIT_REPRS: &[DigitRepr] = &[
            digit::REPR_ZERO,
            digit::REPR_ONE,
            digit::REPR_ONES,
            0x5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA,
            0xFFFF_FFFF_0000_0000,
            0x0000_FFFF_FFFF_0000,
            0x0000_0000_FFFF_FFFF
        ];

        /// Returns a digit that has every even bit set, starting at index 0.
        /// 
        /// E.g.: `0x....010101`
        fn even_digit() -> Digit {
            Digit(0x5555_5555_5555_5555)
        }

        /// Returns a digit that has every odd bit set, starting at index 0.
        /// 
        /// E.g.: `0x....101010`
        fn odd_digit() -> Digit {
            Digit(0xAAAA_AAAA_AAAA_AAAA)
        }

        #[test]
        fn repr() {
            for &val in TEST_DIGIT_REPRS {
                assert_eq!(Digit(val).repr(), val);
            }
        }

        #[test]
        fn dd() {
            for &val in TEST_DIGIT_REPRS {
                assert_eq!(Digit(val).dd(), DoubleDigit(val as DoubleDigitRepr));
            }
        }

        #[test]
        fn width() {
            assert_eq!(Digit::ONES.width(), BitWidth::w64());
            assert_eq!(Digit::ZERO.width(), BitWidth::w64());
            assert_eq!(even_digit().width(), BitWidth::w64());
            assert_eq!(odd_digit().width(), BitWidth::w64());
        }

        #[test]
        fn get_ok() {
            for &pos in VALID_TEST_POS_VALUES {
                assert_eq!(Digit::ONES.get(pos), Ok(true));
                assert_eq!(Digit::ZERO.get(pos), Ok(false));
                assert_eq!(even_digit().get(pos), Ok(pos % 2 == 0));
                assert_eq!(odd_digit().get(pos), Ok(pos % 2 == 1));
            }
        }

        #[test]
        fn get_fail() {
            for &pos in INVALID_TEST_POS_VALUES {
                let expected_err = Err(Error::invalid_bit_access(pos, BitWidth::w64()));
                assert_eq!(Digit::ONES.get(pos), expected_err);
                assert_eq!(Digit::ZERO.get(pos), expected_err);
                assert_eq!(digit::even_digit().get(pos), expected_err);
                assert_eq!(digit::odd_digit().get(pos), expected_err);
            }
        }

        #[test]
        fn set_ok() {
            for &val in TEST_DIGIT_REPRS {
                let mut digit = Digit(val);
                for &pos in VALID_TEST_POS_VALUES {
                    digit.set(pos).unwrap();
                    assert_eq!(digit.get(pos), Ok(true));
                }
            }
        }

        #[test]
        fn set_fail() {
            for &pos in INVALID_TEST_POS_VALUES {
                let expected_err = Err(Error::invalid_bit_access(pos, BitWidth::w64()));
                assert_eq!(Digit::ONES.set(pos), expected_err);
                assert_eq!(Digit::ZERO.set(pos), expected_err);
                assert_eq!(digit::even_digit().set(pos), expected_err);
                assert_eq!(digit::odd_digit().set(pos), expected_err);
            }
        }

        // pub fn set(&mut self, n: usize) -> Result<()> {
        // pub fn unset(&mut self, n: usize) -> Result<()> {
        // pub fn flip(&mut self, n: usize) -> Result<()> {
        // pub fn set_all(&mut self) {
        // pub fn unset_all(&mut self) {
        // pub fn flip_all(&mut self) {
        // pub fn set_first_n(&mut self, n: usize) -> Result<()> {
        // pub fn unset_first_n(&mut self, n: usize) -> Result<()> {
        // pub fn retain_last_n(&mut self, n: usize) -> Result<()> {

        #[test]
        fn retain_last_n() {
            let mut d = Digit::ONES;
            d.retain_last_n(32).unwrap();
            assert_eq!(d, Digit(0x0000_0000_FFFF_FFFF));
        }
    }
}
