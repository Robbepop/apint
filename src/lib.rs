//! Arbitrary precision integers library.
//!
//! This library mainly features the **A**rbitrary **p**recision **Int**eger
//! (`ApInt`) type which is an `n-bit` integer type acting like a
//! twos-complement machine integer.
//!
//! This is useful for emulating machine integers and anything requiring large
//! bitvectors, e.g. SMT solvers.
//!
//! This crate can be used like a bigint crate, except that most operations are
//! completely inline with no reallocations, resizing is manual, and arithmetic
//! can be purposely overflowed.
//!
//! The crate was designed for correctness of emulation and performance in mind,
//! the interface of `ApInt` is very comprehensive, and functions that allocate
//! are clearly documented.
//!
//! Internally `ApInt` uses small-value optimization (no allocations) for values
//! with a bit-width less than or equal to a `Digit`. It uses `64` bit `Digit`s
//! by default, however it can potentially be configured to use other types.
//!
//! The `ApInt` data structure does **not** know signedness. Instead, the
//! operations defined on it (methods) do so. This makes it the perfect building
//! block for higher-level primitives later on.
//!
//! **Note:** Almost all fallible functions in this crate have return types of
//! `Result` or `Option` to let the user handle errors. The exceptions are the
//! `std::ops` traits which will panic if their corresponding `into_wrapping_`
//! or `wrapping_assign` function does.
//!
//! # `std::ops` trait implementations
//!
//! `ApInt` implements some `std::ops` traits for improved usability.
//! Only traits for operations that do not depend on the signedness
//! interpretation of the specific `ApInt` instance are actually implemented.
//! Operations like `div` and `rem` are not expected to have an
//! implementation since a favor in unsigned or signed cannot be decided.
//!
//! `UInt` and `Int` on the other hand implement `Shr`, `Div`, and `Rem` related
//! traits.
//!
//! These ops all happen inplace and no cloning is happening internally,
//! but they can allocate memory if their corresponding `into_wrapping_`
//! or `wrapping_assign` function does.
//!
//! No traits have been implemented `for &'b ApInt` or
//! `for &'b mut ApInt`, because doing so involves cloning. This crate strives
//! for clearly exposing where expensive operations happen, so in this case we
//! favor the user side to use explicit `.clone()`s.

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
mod std_ops;
mod storage;
mod uint;
mod utils;
mod width;

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
    errors::{
        Error,
        ErrorKind,
        Result,
    },
    int::Int,
    radix::Radix,
    uint::UInt,
    width::Width,
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
