#![feature(i128_type)]
#![feature(conservative_impl_trait)]

#![allow(dead_code)]
#![allow(unused_variables)]

#[macro_use] extern crate log;

mod errors;
mod traits;
mod digit;
mod bitwidth;
mod bitpos;
mod storage;
mod radix;
mod small_apint;
mod large_apint;
mod apint;
mod digit_seq;
mod checks;
mod algorithm;

pub use apint::ApInt;
pub use errors::{Result, Error, ErrorKind};
pub use bitwidth::BitWidth;
pub use digit::{Bit};
pub use radix::{Radix};
pub use bitpos::{BitPos};
