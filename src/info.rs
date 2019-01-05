mod bitpos;
mod bitwidth;
mod errors;
mod radix;
mod shiftamount;
mod width;

pub(crate) use self::{errors::DivOp};
pub use self::{radix::Radix, bitpos::BitPos, bitwidth::BitWidth, shiftamount::ShiftAmount, width::Width, errors::{Result, Error, ErrorKind}};