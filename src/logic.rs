// iterators tend to actually convolute what should be simple for loop indexing, at least here
#![allow(clippy::needless_range_loop)]
#![allow(clippy::too_many_arguments)]

mod add_sub;
mod bitwise;
mod div;
mod fuzz;
mod mul;
mod cmp;
mod shift;
mod traits;
mod utils;

pub(crate) use self::utils::{forward_mut_impl, forward_bin_mut_impl, try_forward_bin_mut_impl};