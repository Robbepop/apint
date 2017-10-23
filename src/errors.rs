use bitwidth::BitWidth;

use std::result;
use std::error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	InvalidBinaryStr(String),
	InvalidDecimalStr(String),
	InvalidHexStr(String),

	BitAccessOutOfBounds{
		bit_idx: usize,
		upper_bound: usize
	},

	UnmatchingBitwidth(BitWidth, BitWidth),
	InvalidZeroBitWidth,
	BitWidthOutOfBounds{bitwidth: usize, lo: usize, hi: usize},
	BitWidthTooLarge{bitwidth: usize, upper_bound: usize},
	BitWidthTooSmall{bitwidth: usize, lower_bound: usize}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error{
	kind      : ErrorKind,
	message   : String,
	annotation: Option<String>
}

impl Error {
	/// Returns a reference to the kind of this `Error`.
	#[inline]
	pub fn kind(&self) -> &ErrorKind {
		&self.kind
	}

	/// Returns the error message description of this `Error`.
	#[inline]
	pub fn message(&self) -> &str {
		self.message.as_str()
	}

	/// Returns the optional annotation of this `Error`.
	#[inline]
	pub fn annotation(&self) -> Option<&str> {
		match self.annotation {
			Some(ref ann) => Some(ann.as_str()),
			None          => None
		}
	}

	#[inline]
	pub(crate) fn new(kind: ErrorKind, message: String) -> Error {
		Error{kind, message, annotation: None}
	}

	#[inline]
	pub(crate) fn invalid_zero_bitwidth() -> Error {
		Error{
			kind: ErrorKind::InvalidZeroBitWidth,
			message: "Encountered invalid bitwidth of zero (0).".to_owned(),
			annotation: None
		}
	}

	#[inline]
	pub(crate) fn bitwidth_too_small(bitwidth: usize, lower_bound: usize) -> Error {
		Error{
			kind: ErrorKind::BitWidthTooSmall{bitwidth, lower_bound},
			message: format!("Encountered bitwidth of {:?} smaller than the lower bound of {:?}.", bitwidth, lower_bound),
			annotation: None
		}
	}

	#[inline]
	pub(crate) fn bitwidth_too_large(bitwidth: usize, upper_bound: usize) -> Error {
		Error{
			kind: ErrorKind::BitWidthTooLarge{bitwidth, upper_bound},
			message: format!("Encountered bitwidth of {:?} larger than the upper bound of {:?}.", bitwidth, upper_bound),
			annotation: None
		}
	}

	#[inline]
	pub(crate) fn bitwidth_out_of_bounds(bitwidth: usize, lo: usize, hi: usize) -> Error {
		Error{
			kind: ErrorKind::BitWidthOutOfBounds{bitwidth, lo, hi},
			message: format!("Encountered bitwidth of {:?} out of valid bounds of {:?} to {:?}.", bitwidth, lo, hi),
			annotation: None
		}
	}

	#[inline]
	pub(crate) fn unmatching_bitwidths<W>(lhs: W, rhs: W) -> Error
		where W: Into<BitWidth>
	{
		let lhs = lhs.into();
		let rhs = rhs.into();
		Error{
			kind: ErrorKind::UnmatchingBitwidth(lhs, rhs),
			message: format!("Encountered invalid operation on entities with non-matching bit-widths of {:?} and {:?}.", lhs, rhs),
			annotation: None
		}
	}

	#[inline]
	pub(crate) fn with_annotation<A>(mut self, annotation: A) -> Error
		where A: Into<String>
	{
		self.annotation = Some(annotation.into());
		self
	}

	pub(crate) fn bit_access_out_of_bounds(bit_idx: usize, upper_bound: usize) -> Error {
		Error{
			kind: ErrorKind::BitAccessOutOfBounds{bit_idx, upper_bound},
			message: format!("Encountered invalid bit access at index {:?} with an upper bound of {:?}.", bit_idx, upper_bound),
			annotation: None
		}
	}
}

impl<T> Into<Result<T>> for Error {
	fn into(self) -> Result<T> {
		Err(self)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		<Self as fmt::Debug>::fmt(self, f)
	}
}

impl error::Error for Error {
	fn description(&self) -> &str {
		self.message.as_str()
	}
}

pub type Result<T> = result::Result<T, Error>;
