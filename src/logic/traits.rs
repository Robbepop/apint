use crate::data::ApInt;
use crate::logic::forward_mut_impl;

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
///  error. They may also allocate memory.
/// 
///  `ApInt` implements some `std::ops` traits for improved usability.
///  Only traits for operations that do not depend on the signedness
///  interpretation of the specific `ApInt` instance are actually implemented.
///  Operations like `div` and `rem` are not expected to have an
///  implementation since a favor in unsigned or signed cannot be decided.
/// ============================================================================

//unary ops

impl Not for ApInt {
    type Output = ApInt;

    fn not(self) -> Self::Output {
        forward_mut_impl(self, ApInt::bitnot)
    }
}

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

//plain binary ops

impl<'a> BitAnd<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitand(rhs).unwrap()
    }
}

impl<'a, 'b> BitAnd<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitand(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitand(rhs).unwrap()
    }
}

impl<'a> BitOr<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitor(rhs).unwrap()
    }
}

impl<'a, 'b> BitOr<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitor(rhs).unwrap()
    }
}

impl<'a> BitXor<&'a ApInt> for ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.into_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitxor(rhs).unwrap()
    }
}

impl<'a, 'b> BitXor<&'a ApInt> for &'b mut ApInt {
    type Output = ApInt;

    fn bitxor(self, rhs: &'a ApInt) -> Self::Output {
        self.clone().into_bitxor(rhs).unwrap()
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

//assignment ops

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