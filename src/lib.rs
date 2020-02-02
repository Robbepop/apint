//! Arbitrary precision integers library.
//!
//! This library mainly features the **A**rbitrary **p**recision **Int**eger
//! (`ApInt`) type which is an `n-bit` integer type acting like a machine
//! integer working in the twos-complement.
//!
//! This is useful for emulating machine integers for example in constant
//! evaluation of compilers or for solving bitvector formulas of SMT solvers.
//!
//! Internally `ApInt` uses small-value optimization for values with a bit-width
//! less than or equal to `64` bits. It uses `64` bit digits and thus its
//! algorithms computes within the base of 2<sup>64</sup>.
//!
//! The `ApInt` data structure does **not** know signedness. Instead, the
//! operations defined on it (methods) do so. This makes it the perfect building
//! block for higher-level primitives later on.
//!
//! The crate was designed for correctness of emulation and performance in mind
//! and the interface of `ApInt` is very comprehensive.

// #![allow(dead_code)]
// #![deny(missing_docs)]
// #![deny(warnings)]

#![cfg_attr(not(feature = "std"), no_std)]
#![doc(html_root_url = "https://docs.rs/crate/apint/0.2.0")]

#[cfg(not(feature = "std"))]
extern crate alloc;

mod apint;
mod bitpos;
mod bitwidth;
mod checks;
mod digit;
mod digit_seq;
mod errors;
mod int;
mod mem;
mod radix;
mod storage;
mod traits;
mod uint;
mod utils;

pub(crate) use digit::{
    Digit,
    DoubleDigit,
};

pub use crate::{
    apint::{
        ApInt,
        ShiftAmount,
    },
    bitpos::BitPos,
    bitwidth::BitWidth,
    digit::Bit,
    errors::{
        Error,
        ErrorKind,
        Result,
    },
    int::Int,
    radix::Radix,
    traits::Width,
    uint::UInt,
};

/// Re-exports some commonly used items of this crate.
pub mod prelude {
    #[doc(no_inline)]
    pub use super::{
        ApInt,
        BitWidth,
        Int,
        UInt,
        Width,
    };
}
