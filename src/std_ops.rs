//! `std::ops` trait implementations. See the docs in `lib.rs` for more.

use crate::{ApInt, Int, ShiftAmount, UInt};

use core::ops::{
    Add,
    AddAssign,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Div,
    DivAssign,
    Mul,
    MulAssign,
    Neg,
    Not,
    Rem,
    RemAssign,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    Sub,
    SubAssign,
};

// This is done through a macro to decrease the amount of testing needed, since
// if it works for the `ApInt` case, it will also work for `Int` and `UInt`. It
// also decreases code duplication.
macro_rules! common_std_ops {
    ($ty:ty) => {
        // unary

        impl Not for $ty {
            type Output = Self;

            fn not(self) -> Self::Output {
                self.into_bitnot()
            }
        }

        // `std` implements this even for unsigned primitives, and this crate does so
        // too.
        impl Neg for $ty {
            type Output = Self;

            fn neg(self) -> Self::Output {
                self.into_wrapping_neg()
            }
        }

        impl<S> Shl<S> for $ty
        where
            S: Into<ShiftAmount>,
        {
            type Output = Self;

            fn shl(self, shift_amount: S) -> Self::Output {
                self.into_wrapping_shl(shift_amount).unwrap()
            }
        }

        // binary ops

        impl<'a> BitAnd<&'a $ty> for $ty {
            type Output = Self;

            fn bitand(self, rhs: &'a Self) -> Self::Output {
                self.into_bitand(rhs).unwrap()
            }
        }

        impl<'a> BitOr<&'a $ty> for $ty {
            type Output = Self;

            fn bitor(self, rhs: &'a Self) -> Self::Output {
                self.into_bitor(rhs).unwrap()
            }
        }

        impl<'a> BitXor<&'a $ty> for $ty {
            type Output = Self;

            fn bitxor(self, rhs: &'a Self) -> Self::Output {
                self.into_bitxor(rhs).unwrap()
            }
        }

        impl<'a> Add<&'a $ty> for $ty {
            type Output = Self;

            fn add(self, rhs: &'a Self) -> Self::Output {
                self.into_wrapping_add(rhs).unwrap()
            }
        }

        impl<'a> Sub<&'a $ty> for $ty {
            type Output = Self;

            fn sub(self, rhs: &'a Self) -> Self::Output {
                self.into_wrapping_sub(rhs).unwrap()
            }
        }

        impl<'a> Mul<&'a $ty> for $ty {
            type Output = Self;

            fn mul(self, rhs: &'a Self) -> Self::Output {
                self.into_wrapping_mul(rhs).unwrap()
            }
        }

        // assignment ops

        impl<S> ShlAssign<S> for $ty
        where
            S: Into<ShiftAmount>,
        {
            fn shl_assign(&mut self, shift_amount: S) {
                self.wrapping_shl_assign(shift_amount).unwrap();
            }
        }

        impl<'a> BitAndAssign<&'a $ty> for $ty {
            fn bitand_assign(&mut self, rhs: &'a Self) {
                self.bitand_assign(rhs).unwrap();
            }
        }

        impl<'a> BitOrAssign<&'a $ty> for $ty {
            fn bitor_assign(&mut self, rhs: &'a Self) {
                self.bitor_assign(rhs).unwrap();
            }
        }

        impl<'a> BitXorAssign<&'a $ty> for $ty {
            fn bitxor_assign(&mut self, rhs: &'a Self) {
                self.bitxor_assign(rhs).unwrap();
            }
        }

        impl<'a> AddAssign<&'a $ty> for $ty {
            fn add_assign(&mut self, rhs: &'a Self) {
                self.wrapping_add_assign(rhs).unwrap()
            }
        }

        impl<'a> SubAssign<&'a $ty> for $ty {
            fn sub_assign(&mut self, rhs: &'a Self) {
                self.wrapping_sub_assign(rhs).unwrap()
            }
        }

        impl<'a> MulAssign<&'a $ty> for $ty {
            fn mul_assign(&mut self, rhs: &'a Self) {
                self.wrapping_mul_assign(rhs).unwrap();
            }
        }
    };
}

common_std_ops!(ApInt);
common_std_ops!(UInt);
common_std_ops!(Int);

// For signedness dependent cases
macro_rules! signed_std_ops {
    ($ty:ty) => {
        impl<S> Shr<S> for $ty
        where
            S: Into<ShiftAmount>,
        {
            type Output = Self;

            fn shr(self, shift_amount: S) -> Self::Output {
                self.into_wrapping_shr(shift_amount).unwrap()
            }
        }

        impl<'a> Div<&'a $ty> for $ty {
            type Output = Self;

            fn div(self, rhs: &'a Self) -> Self::Output {
                self.into_wrapping_div(rhs).unwrap()
            }
        }

        impl<'a> Rem<&'a $ty> for $ty {
            type Output = Self;

            fn rem(self, rhs: &'a Self) -> Self::Output {
                self.into_wrapping_rem(rhs).unwrap()
            }
        }

        impl<S> ShrAssign<S> for $ty
        where
            S: Into<ShiftAmount>,
        {
            fn shr_assign(&mut self, shift_amount: S) {
                self.wrapping_shr_assign(shift_amount).unwrap();
            }
        }

        impl<'a> DivAssign<&'a $ty> for $ty {
            fn div_assign(&mut self, rhs: &'a Self) {
                self.wrapping_div_assign(rhs).unwrap();
            }
        }

        impl<'a> RemAssign<&'a $ty> for $ty {
            fn rem_assign(&mut self, rhs: &'a Self) {
                self.wrapping_rem_assign(rhs).unwrap();
            }
        }
    };
}

signed_std_ops!(UInt);
signed_std_ops!(Int);

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

        #[test]
        fn signed() {
            // Set the sign bit to see if the wrong kind of divisions are being called.
            // -57i8 has the same bit pattern as 199u8
            assert_eq!(UInt::from(199u8) >> 4, UInt::from(12u8));
            assert_eq!(Int::from(-57i8) >> 4, Int::from(-4i8));

            assert_eq!(UInt::from(199u8) / &UInt::from(7u8), UInt::from(28u8));
            assert_eq!(UInt::from(199u8) % &UInt::from(7u8), UInt::from(3u8));
            assert_eq!(Int::from(-57i8) / &Int::from(7i8), Int::from(-8i8));
            assert_eq!(Int::from(-57i8) % &Int::from(7i8), Int::from(-1i8));

            let mut tmp = UInt::from(199u8);
            tmp >>= 4;
            assert_eq!(tmp, UInt::from(12u8));
            let mut tmp = Int::from(-57i8);
            tmp >>= 4;
            assert_eq!(tmp, Int::from(-4i8));

            let mut x = UInt::from(199u8);
            let y = UInt::from(7u8);
            x /= &y;
            assert_eq!(x, UInt::from(28u8));
            x = UInt::from(199u8);
            x %= &y;
            assert_eq!(x, UInt::from(3u8));

            let mut x = Int::from(-57i8);
            let y = Int::from(7i8);
            x /= &y;
            assert_eq!(x, Int::from(-8i8));
            x = Int::from(-57i8);
            x %= &y;
            assert_eq!(x, Int::from(-1i8));
        }
    }
}
