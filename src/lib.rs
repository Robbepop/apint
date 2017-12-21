#![feature(i128_type)]
#![feature(conservative_impl_trait)]
#![feature(unique)]

#![allow(dead_code)]

extern crate smallvec;

#[cfg(feature = "rand_support")]
extern crate rand;

#[cfg(feature = "serde_support")]
extern crate serde;

#[cfg(all(test, feature = "serde_support"))]
extern crate serde_test;

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
// mod algorithm;

pub use apint::ApInt;
pub use errors::{Result, Error, ErrorKind};
pub use bitwidth::BitWidth;
pub use digit::{Bit};
pub use radix::{Radix};
pub use bitpos::{BitPos};
