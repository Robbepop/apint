//! Arbitrary precision integers library. 
//! 
//! This library mainly features the **A**rbitrary **p**recision **Int**eger (`ApInt`) type
//! which is an `n-bit` integer type acting like a machine integer working in the twos-complement.
//! 
//! This is useful for emulating machine integers for example in constant evaluation of compilers
//! or for solving bitvector formulas of SMT solvers.
//! 
//! Internally `ApInt` uses small-value optimization for values with a bit-width less than or
//! equal to `64` bits. It uses `64` bit digits and thus its algorithms computes within the base
//! of 2<sup>64</sup>.
//! 
//! The `ApInt` data structure does **not** know signedness. Instead, the operations defined on it
//! (methods) do so. This makes it the perfect building block for higher-level primitives later on.
//! 
//! The crate was designed for correctness of emulation and performance in mind and the interface
//! of `ApInt` is very comprehensive.

// #![allow(dead_code)]
// #![deny(missing_docs)]
// #![deny(warnings)]

#![doc(html_root_url = "https://docs.rs/crate/apint/0.2.0")]

extern crate smallvec;

#[cfg(feature = "rand_support")]
extern crate rand;

#[cfg(feature = "serde_support")]
extern crate serde;

#[cfg(feature = "serde_support")]
#[macro_use]
extern crate serde_derive;

#[cfg(all(test, feature = "serde_support"))]
extern crate serde_test;

#[cfg(test)]
extern crate itertools;

mod errors;
mod traits;
mod digit;
mod bitwidth;
mod bitpos;
mod storage;
mod radix;
mod apint;
mod digit_seq;
mod checks;
mod ll;
mod uint;
mod int;
mod utils;

pub use apint::{
    ApInt,
    ShiftAmount
};
pub use errors::{
    Result,
    Error,
    ErrorKind
};
pub use bitwidth::BitWidth;
pub use digit::{Bit};
pub use radix::{Radix};
pub use bitpos::{BitPos};
pub use traits::{Width};
pub use uint::{UInt};
pub use int::{Int};

/// Re-exports some commonly used items of this crate.
pub mod prelude {
    #[doc(no_inline)]
    pub use super::{
        ApInt,
        Int,
        UInt,
        BitWidth,
        Width
    };
}
