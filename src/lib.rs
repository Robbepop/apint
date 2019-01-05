//! Arbitrary precision integers library. 
//! 
//! This library mainly features the **A**rbitrary **p**recision **Int**eger (`ApInt`) type
//! which is an `n-bit` integer type acting like a machine integer working in the twos-complement.
//! 
//! This is useful for emulating machine integers for example in constant evaluation of compilers
//! or for solving bitvector formulas of SMT solvers.
//! 
//! Internally `ApInt` uses small-value optimization for values with a bit-width less than or
//! equal to `64` bits. It uses `64` bit `Digit`s (by default, however it can be configured to use
//! other types) and thus its algorithms computes within the base of 2<sup>64</sup>.
//! 
//! The `ApInt` data structure does **not** know signedness. Instead, the operations defined on it
//! (methods) do so. This makes it the perfect building block for higher-level primitives later on.
//! 
//! The crate was designed for correctness of emulation and performance in mind and the interface
//! of `ApInt` is very comprehensive.

#![doc(html_root_url = "https://docs.rs/crate/apint/0.2.0")]

#[cfg(feature = "specialized_div_rem")]
extern crate specialized_div_rem;

#[cfg(feature = "rand_support")]
extern crate rand;

#[cfg(feature = "serde_support")]
extern crate serde;

#[cfg(feature = "serde_support")]
extern crate serde_derive;

#[cfg(all(test, feature = "serde_support"))]
extern crate serde_test;

#[cfg(test)]
extern crate itertools;

//NOTE: the file structure used in this library has less to do with the actual dependencies between
//files and more about organizing files in a way that helps with programmers finding where stuff is.

//The `ApInt` definition and most of the extremely unsafe function impls on `ApInt`s are located in
//`apint.rs`. The other bulk of unsafe functions is found in `access.rs` and `constructors.rs`.

pub(crate) mod info;
pub(crate) mod data;
pub(crate) mod construction;
pub(crate) mod logic;

pub use crate::info::{
    Radix,
    BitWidth,
    BitPos,
    Width,
    ShiftAmount,
    Result,
    Error,
    ErrorKind
};
pub use crate::data::{
    ApInt,
    UInt,
    Int
};

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
