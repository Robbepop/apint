//! Arbitrary precision integers library. 
//! 
//! This library mainly features the **A**rbitrary **p**recision **Int**eger (`ApInt`) type
//! which is an `n-bit` integer type acting like a machine integer working in the twos-complement.
//! 
//! This is useful for emulating machine integers and anything requiring large bitvectors. This
//! crate can be used like a bigint crate, except that most operations are completely inline with no
//! reallocations, resizing is manual, and arithmetic can be purposely overflowed.
//! 
//! The crate was designed for correctness of emulation and performance in mind, the interface
//! of `ApInt` is very comprehensive, and functions that allocate are clearly documented.
//!
//! The `ApInt` data structure does **not** know signedness. Instead, the operations defined on it
//! (methods) do so. This makes it the perfect building block for higher-level primitives later on.
//! 
//! Internally `ApInt` uses small-value optimization for values with a bit-width less than or
//! equal to a `Digit`. It uses `64` bit `Digit`s by default, however it can potentially be
//! configured to use other types.

#![doc(html_root_url = "https://docs.rs/crate/apint/0.3.0")]

// NOTE: The file structure used in this library has less to do with the actual dependencies between
// files and more about organizing files in a way that helps with programmers finding where implementations
// are.

// The `ApInt` definition and most of the extremely unsafe function impls on `ApInt`s are located in
// `apint.rs`. The other bulk of unsafe functions is found in `access.rs` and `constructors.rs`.

// Contains a variety of helper structs used throughout the crate.
pub(crate) mod info;

// Contains large allocating data and data access abstractions.
pub(crate) mod data;

// Contains a variety of construction functions, casting, and implementations of external traits.
pub(crate) mod construction;

// Contains the big integer logical and arithmetic operations
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
