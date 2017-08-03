#![feature(i128_type)]
#![feature(try_from)]

#![allow(dead_code)]
#![allow(unused_variables)]

#[macro_use] extern crate log;

mod errors;
mod traits;
mod digit;
mod bitwidth;
mod small_apint;
mod large_apint;
mod apint;

pub use apint::APInt;
pub use errors::{Result, Error, ErrorKind};
