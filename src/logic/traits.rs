use crate::data::ApInt;
use std::hash::{Hash, Hasher};

use std::ops::{
    Not,
    Neg,
    BitAnd,
    BitOr,
    BitXor,
    Add,
    Sub,
    Mul,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    AddAssign,
    SubAssign,
    MulAssign
};

/// ============================================================================
///  Standard `ops` trait implementations.
/// ----------------------------------------------------------------------------
///  **Note:** These ops will panic if their corresponding functions return an
///  error. These ops all happen inplace and no cloning is happening internally,
///  but they can allocate memory if their corresponding function does.
/// 
///  `ApInt` implements some `std::ops` traits for improved usability.
///  Only traits for operations that do not depend on the signedness
///  interpretation of the specific `ApInt` instance are actually implemented.
///  Operations like `div` and `rem` are not expected to have an
///  implementation since a favor in unsigned or signed cannot be decided.
/// 
///  Also note that no traits have been implemented `for &'b ApInt` or
///  `for &'b mut ApInt`, because doing so involves cloning. This crate strives
///  for clearly exposing where expensive operations happen, so in this case we
///  favor the user side to be more explicit.
/// ============================================================================

// miscellanious ops

impl Hash for ApInt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.as_digit_slice().hash(state);
    }
}

// unary ops

impl Not for ApInt {
    type Output = ApInt;

    fn not(self) -> Self::Output {
        self.into_bitnot()
    }
}

impl Neg for ApInt {
    type Output = ApInt;

    fn neg(self) -> Self::Output {
        self.into_wrapping_neg()
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