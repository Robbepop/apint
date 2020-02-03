//! ============================================================================
//!  Standard `std::ops` trait implementations.
//! ----------------------------------------------------------------------------
//!  **Note:** These ops will panic if their corresponding functions return an
//!  error. These ops all happen inplace and no cloning is happening internally,
//!  but they can allocate memory if their corresponding function does.
//!
//!  `ApInt` implements some `std::ops` traits for improved usability.
//!  Only traits for operations that do not depend on the signedness
//!  interpretation of the specific `ApInt` instance are actually implemented.
//!  Operations like `div` and `rem` are not expected to have an
//!  implementation since a favor in unsigned or signed cannot be decided.
//!
//!  Also note that no traits have been implemented `for &'b ApInt` or
//!  `for &'b mut ApInt`, because doing so involves cloning. This crate strives
//!  for clearly exposing where expensive operations happen, so in this case we
//!  favor the user side to use explicit `.clone()`s.
//! ============================================================================

use crate::{
    ApInt,
    ShiftAmount,
};

use std::ops::{
    Add,
    AddAssign,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Mul,
    MulAssign,
    Neg,
    Not,
    Shl,
    ShlAssign,
    Sub,
    SubAssign,
};

// unary

impl Not for ApInt {
    type Output = ApInt;

    fn not(self) -> Self::Output {
        self.into_bitnot()
    }
}

// `std` implements this even for unsigned primitives, and this crate does so
// too.
impl Neg for ApInt {
    type Output = ApInt;

    fn neg(self) -> Self::Output {
        self.into_wrapping_neg()
    }
}

impl<S> Shl<S> for ApInt
where
    S: Into<ShiftAmount>,
{
    type Output = ApInt;

    fn shl(self, shift_amount: S) -> Self::Output {
        self.into_wrapping_shl(shift_amount).unwrap()
    }
}

// binary ops

impl<'a> BitAnd<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitand(rhs).unwrap()
    }
}

impl<'a> BitOr<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitor(rhs).unwrap()
    }
}

impl<'a> BitXor<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitxor(rhs).unwrap()
    }
}

impl<'a> Add<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn add(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_add(rhs).unwrap()
    }
}

impl<'a> Sub<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn sub(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_sub(rhs).unwrap()
    }
}

impl<'a> Mul<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn mul(self, rhs: &'a ApInt) -> Self::Output {
        self.into_wrapping_mul(rhs).unwrap()
    }
}

// assignment ops

impl<S> ShlAssign<S> for ApInt
where
    S: Into<ShiftAmount>,
{
    fn shl_assign(&mut self, shift_amount: S) {
        self.wrapping_shl_assign(shift_amount).unwrap();
    }
}

impl<'a> BitAndAssign<&'a ApInt> for ApInt {
    fn bitand_assign(&mut self, rhs: &'a ApInt) {
        self.bitand_assign(rhs).unwrap();
    }
}

impl<'a> BitOrAssign<&'a ApInt> for ApInt {
    fn bitor_assign(&mut self, rhs: &'a ApInt) {
        self.bitor_assign(rhs).unwrap();
    }
}

impl<'a> BitXorAssign<&'a ApInt> for ApInt {
    fn bitxor_assign(&mut self, rhs: &'a ApInt) {
        self.bitxor_assign(rhs).unwrap();
    }
}

impl<'a> AddAssign<&'a ApInt> for ApInt {
    fn add_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_add_assign(rhs).unwrap()
    }
}

impl<'a> SubAssign<&'a ApInt> for ApInt {
    fn sub_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_sub_assign(rhs).unwrap()
    }
}

impl<'a> MulAssign<&'a ApInt> for ApInt {
    fn mul_assign(&mut self, rhs: &'a ApInt) {
        self.wrapping_mul_assign(rhs).unwrap();
    }
}

// check that all the operations exist and have the right methods
#[cfg(test)]
mod tests {
    use super::*;

    mod std_ops {
        use super::*;

        #[test]
        fn unary() {
            assert_eq!(-ApInt::from(123i8), ApInt::from(-123i8));
            assert_eq!(!ApInt::from(0b01101001u8), ApInt::from(0b10010110u8));
            assert_eq!(ApInt::from(0b1001u8) << 4, ApInt::from(0b10010000u8));
        }

        #[test]
        fn binary() {
            assert_eq!(
                ApInt::from(0b0110u8) & &ApInt::from(0b1010u8),
                ApInt::from(0b0010u8)
            );
            assert_eq!(
                ApInt::from(0b0110u8) | &ApInt::from(0b1010u8),
                ApInt::from(0b1110u8)
            );
            assert_eq!(
                ApInt::from(0b0110u8) ^ &ApInt::from(0b1010u8),
                ApInt::from(0b1100u8)
            );

            assert_eq!(ApInt::from(3u8) + &ApInt::from(7u8), ApInt::from(10u8));
            assert_eq!(ApInt::from(3i8) - &ApInt::from(7i8), ApInt::from(-4i8));
            assert_eq!(ApInt::from(3u8) * &ApInt::from(7u8), ApInt::from(21u8));
        }

        #[test]
        fn assign() {
            let mut tmp = ApInt::from(0b1001u8);
            tmp <<= 4;
            assert_eq!(tmp, ApInt::from(0b10010000u8));

            let mut x = ApInt::from(0b0110u8);
            let y = ApInt::from(0b1010u8);
            x &= &y;
            assert_eq!(x, ApInt::from(0b0010u8));
            x = ApInt::from(0b0110u8);
            x |= &y;
            assert_eq!(x, ApInt::from(0b1110u8));
            x = ApInt::from(0b0110u8);
            x ^= &y;
            assert_eq!(x, ApInt::from(0b1100u8));

            let mut x = ApInt::from(3i8);
            let y = ApInt::from(7i8);
            x += &y;
            assert_eq!(x, ApInt::from(10u8));
            x = ApInt::from(3i8);
            x -= &y;
            assert_eq!(x, ApInt::from(-4i8));
            x = ApInt::from(3i8);
            x *= &y;
            assert_eq!(x, ApInt::from(21u8));
        }
    }
}
