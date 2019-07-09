use crate::data::{ApInt, UInt};
use crate::info::{BitWidth, Result, ShiftAmount, BitPos, Width};
use crate::logic::{try_forward_bin_mut_impl, forward_mut_impl, forward_bin_mut_impl};

#[cfg(feature = "rand_support")]
use rand;

use std::cmp::Ordering;
use std::ops::{
    Not,
    BitAnd,
    BitOr,
    BitXor,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    Neg,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign
};
