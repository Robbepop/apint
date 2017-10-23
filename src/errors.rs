use bitwidth::BitWidth;
use bitpos::BitPos;
use radix::Radix;

use std::result;
use std::error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	/// Returned on trying to create a `Radix` from an invalid `usize` representation.
	InvalidRadix(usize),

	/// Returned whenever trying to parse an invalid string representation for an `APInt`.
	InvalidStringRepr{
		/// The string storing the invalid representation of the int for the given radix.
		input: String,
		/// The radix that was used.
		radix: Radix
	},

	/// Returned on trying to access an invalid bit position.
	InvalidBitAccess{
		/// The invalid bit position that was tried to access.
		pos: BitPos,
		/// The upper bound for valid bit positions in this context.
		width: BitWidth
	},

	/// Returned on violation of matching bitwidth constraints of operations.
	UnmatchingBitwidth(BitWidth, BitWidth),

	/// Returned on trying to create a `BitWidth` from an invalid `usize` representation.
	InvalidBitWidth(usize),

	/// Returned on truncating an `APInt` with a bitwidth greater than the current one.
	TruncationBitWidthTooLarge{
		/// The target bit width.
		target: BitWidth,
		/// The current actual bit width.
		current: BitWidth
	},

	/// Returned on extending an `APInt` with a bitwidth less than the current one.
	ExtensionBitWidthTooSmall{
		/// The target bit width.
		target: BitWidth,
		/// The current actual bit width.
		current: BitWidth
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error{
	kind      : ErrorKind,
	message   : String,
	annotation: Option<String>
}

//  ===========================================================================
///  Public getters for `Error`.
/// ===========================================================================
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
}

//  ===========================================================================
///  Extending constructors for `Error`.
/// ===========================================================================
impl Error {
	#[inline]
	pub(crate) fn with_annotation<A>(mut self, annotation: A) -> Error
		where A: Into<String>
	{
		self.annotation = Some(annotation.into());
		self
	}
}

//  ===========================================================================
///  Default constructors for `Error`.
/// ===========================================================================
impl Error {
	pub(crate) fn invalid_radix(val: usize) -> Error {
		Error{
			kind: ErrorKind::InvalidRadix(val),
			message: format!("Encountered an invalid parsing radix of {:?}.", val),
			annotation: None
		}
	}

	pub(crate) fn invalid_string_repr(input: String, radix: Radix) -> Error {
		Error{
			kind: ErrorKind::InvalidStringRepr{input, radix},
			message: format!("Encountered an invalid string representation for the given radix (= {:?}).", radix),
			annotation: None
		}
	}

	pub(crate) fn invalid_bitwidth(val: usize) -> Error {
		Error{
			kind: ErrorKind::InvalidBitWidth(val),
			message: format!("Encountered invalid bitwidth of {:?}.", val),
			annotation: None
		}
	}

	pub(crate) fn invalid_zero_bitwidth() -> Error {
		Error::invalid_bitwidth(0)
	}

	pub(crate) fn extension_bitwidth_too_small<W1, W2>(target: W1, current: W2) -> Error
		where W1: Into<BitWidth>,
		      W2: Into<BitWidth>
	{
		let target = target.into();
		let current = current.into();
		Error{
			kind: ErrorKind::ExtensionBitWidthTooSmall{target, current},
			message: format!("Tried to extend an `APInt` with a width of {:?} to a smaller target width of {:?}", current, target),
			annotation: None
		}
	}

	pub(crate) fn truncation_bitwidth_too_large<W1, W2>(target: W1, current: W2) -> Error
		where W1: Into<BitWidth>,
		      W2: Into<BitWidth>
	{
		let target = target.into();
		let current = current.into();
		Error{
			kind: ErrorKind::TruncationBitWidthTooLarge{target, current},
			message: format!("Tried to truncate an `APInt` with a width of {:?} to a larger target width of {:?}", current, target),
			annotation: None
		}
	}

	pub(crate) fn unmatching_bitwidths<W1, W2>(lhs: W1, rhs: W2) -> Error
		where W1: Into<BitWidth>,
		      W2: Into<BitWidth>
	{
		let lhs = lhs.into();
		let rhs = rhs.into();
		Error{
			kind: ErrorKind::UnmatchingBitwidth(lhs, rhs),
			message: format!("Encountered invalid operation on entities with non-matching bit-widths of {:?} and {:?}.", lhs, rhs),
			annotation: None
		}
	}

	pub(crate) fn invalid_bit_access<P, W>(pos: P, width: W) -> Error
		where P: Into<BitPos>,
		      W: Into<BitWidth>
	{
		let pos = pos.into();
		let width = width.into();
		Error{
			kind: ErrorKind::InvalidBitAccess{pos, width},
			message: format!("Encountered invalid bit access at position {:?} with a total bit-width of {:?}.", pos, width),
			annotation: None
		}
	}
}

impl<T> Into<Result<T>> for Error {
	/// Converts an `Error` into a `Result<T, Error>`.
	/// 
	/// This might be useful to prevent some parentheses spams
	/// because it replaces `Err(my_error)` with `my_error.into()`.
	/// 
	/// On the other hand it might be an abuse of the trait ...
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

/// The `Result` type used in `APInt`.
pub type Result<T> = result::Result<T, Error>;
