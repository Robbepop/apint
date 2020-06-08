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
//!
//! # `signed_min_value` corner cases
//!
//! Two's complement is a very well defined number representation system that
//! allows for the same addition and multiplication functions to work on both
//! unsigned and signed integers. However, for `Int`s and `ApInt`s interpreted
//! as signed, there is one particular value that can cause unexpected results
//! in many functions: `ApInt::signed_min_value` and the corresponding
//! `Int::min_value`.
//!
//! The root cause of problems for `signed_min_value` of a given bitwidth is
//! that there does not exist a positive version of this value with the same
//! absolute magnitude. Calling `wrapping_neg` or `wrapping_abs` on a
//! `signed_min_value`, for example, will overflow and return
//! `signed_min_value`.
//!
//! The smallest case of this is for single bit width integers, where
//! the most significant bit and least significant bit are the same bit. These
//! integers can only take on the values 0 (when the bit is not set) and -1
//! (when the bit is set). Not accounting for this can cause [very nasty edge
//! cases](https://github.com/rust-lang/rust/issues/51582). For this reason,
//! this crate does not have a `ApInt::one()` constructor or any constructors
//! besides `ApInt::zero()` and the different min/max functions. `UInt` and
//! `Int`, however, do have `one` and `is_one` functions. `Int::one()` has a
//! differing signature from `UInt::one()`, returning a `Option<Int>` because
//! it can fail. Users of this crate are likewise expected to check if
//! `signed_min_value` can cause problems for functions they write using
//! `ApInt`s and `Int`s, and to provide special casing and docs if it does.

// #![allow(dead_code)]
// #![deny(missing_docs)]
// #![deny(warnings)]

#![cfg_attr(not(feature = "std"), no_std)]
#![doc(html_root_url = "https://docs.rs/crate/apint/0.2.0")]

// TODO remove these as soon as they are on stable
#![feature(const_if_match)]
#![feature(const_fn)]
#![feature(const_panic)]
#![feature(const_nonzero_int_methods)]

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
    bitwidth::{
        bw,
        BitWidth,
    },
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
        bw,
        ApInt,
        BitWidth,
        Int,
        UInt,
        Width,
    };
}
