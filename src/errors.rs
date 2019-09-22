use crate::bitwidth::BitWidth;
use crate::bitpos::BitPos;
use crate::radix::Radix;
use crate::apint::{ApInt, ShiftAmount};
use crate::apint::{PrimitiveTy};

use std::result;
use std::error;
use std::fmt;

/// Represents the kind of an `Error`.
/// 
/// This also stores the unique information tied to the error report.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// Returned on trying to create a `Radix` from an invalid `u8` representation.
    InvalidRadix(u8),

    /// Returned whenever trying to parse an invalid string representation for an `ApInt`.
    InvalidStringRepr{
        /// The string storing the invalid representation of the int for the given radix.
        input: String,
        /// The radix that was used.
        radix: Radix,
        /// An optional index and character when encountering an invalid character.
        pos_char: Option<(usize, char)>
    },

    /// Returned on trying to access an invalid bit position.
    InvalidBitAccess{
        /// The invalid bit position that was tried to access.
        pos: BitPos,
        /// The upper bound for valid bit positions in this context.
        width: BitWidth
    },

    /// Returned on trying to shift with an invalid shift amount.
    InvalidShiftAmount{
        /// The invalid shift amount.
        shift_amount: ShiftAmount,
        /// The bit width for which this shift amount of invalid.
        width: BitWidth
    },

    /// Returns on trying to cast an `ApInt` to a primitive type
    /// that can not represent the value represented by the `ApInt`.
    ValueUnrepresentable{
        /// The `ApInt` that the user wanted to represent as the given `PrimitiveTy`.
        value: ApInt,
        /// The `PrimitiveTy` that the user wanted for representing the given `ApInt`.
        destination_ty: PrimitiveTy
    },

    /// Returned on violation of matching bitwidth constraints of operations.
    UnmatchingBitwidth(BitWidth, BitWidth),

    /// Returned on trying to create a `BitWidth` from an invalid `usize` representation.
    InvalidBitWidth(usize),

    /// Returned on truncating an `ApInt` with a bitwidth greater than the current one.
    TruncationBitWidthTooLarge{
        /// The target bit width.
        target: BitWidth,
        /// The current actual bit width.
        current: BitWidth
    },

    /// Returned on extending an `ApInt` with a bitwidth less than the current one.
    ExtensionBitWidthTooSmall{
        /// The target bit width.
        target: BitWidth,
        /// The current actual bit width.
        current: BitWidth
    },

    /// Returned on division by zero.
    DivisionByZero {
        /// The exact division operation.
        op: DivOp,
        /// The left-hand side of the division.
        lhs: ApInt
    },

    /// Returned on constructing an `ApInt` from an empty iterator of `Digit`s.
    ExpectedNonEmptyDigits,
}

/// All division operations that may be affected by division-by-zero errors.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DivOp {
    /// The unsigned quotient and remainder operation
    UnsignedDivRem,
    /// The unsigned remainder and quotient operation
    UnsignedRemDiv,
    /// The signed quotient and remainder operation
    SignedDivRem,
    /// The signed remainder and quotient operation
    SignedRemDiv,
    /// The unsigned quotient operation.
    UnsignedDiv,
    /// The unsigned remainder operation.
    UnsignedRem,
    /// The signed quotient operation.
    SignedDiv,
    /// The signed remainder operation.
    SignedRem,
}

/// Represents an error that may occure upon using the `ApInt` library.
/// 
/// All errors have a unique kind which also stores extra information for error reporting.
/// Besides that an `Error` also stores a message and an optional additional annotation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error {
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
    pub(crate) fn invalid_radix(val: u8) -> Error {
        Error{
            kind: ErrorKind::InvalidRadix(val),
            message: format!("Encountered an invalid parsing radix of {:?}.", val),
            annotation: None
        }
    }

    pub(crate) fn invalid_string_repr<S>(input: S, radix: Radix) -> Error
        where S: Into<String>
    {
        let input = input.into();
        Error{
            kind: ErrorKind::InvalidStringRepr{input, radix, pos_char: None},
            message: format!("Encountered an invalid string representation for the given radix (= {:?}).", radix),
            annotation: None
        }
    }

    pub(crate) fn invalid_char_in_string_repr<S>(input: S, radix: Radix, pos: usize, ch: char) -> Error
        where S: Into<String>
    {
        let input = input.into();
        Error{
            kind: ErrorKind::InvalidStringRepr{input, radix, pos_char: None},
            message: format!("Encountered an invalid character (= '{:?}') at position {:?} within the given string \
                              representation for the given radix (= {:?}).", ch, pos, radix),
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
            message: format!("Tried to extend an `ApInt` with a width of {:?} to a smaller target width of {:?}", current, target),
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
            message: format!("Tried to truncate an `ApInt` with a width of {:?} to a larger target width of {:?}", current, target),
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

    pub(crate) fn invalid_shift_amount<S, W>(shift_amount: S, width: W) -> Error
        where S: Into<ShiftAmount>,
              W: Into<BitWidth>
    {
        let shift_amount = shift_amount.into();
        let width = width.into();
        Error{
            kind: ErrorKind::InvalidShiftAmount{shift_amount, width},
            message: format!("Encountered invalid shift amount of {:?} on bit-width with {:?} bits.", shift_amount, width),
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

    pub(crate) fn expected_non_empty_digits() -> Error {
        Error{
            kind: ErrorKind::ExpectedNonEmptyDigits,
            message: "Encountered an empty iterator upon construction of an `ApInt` from a digit iterator.".to_owned(),
            annotation: None
        }
    }

    pub(crate) fn encountered_unrepresentable_value(
        value: ApInt,
        destination_ty: PrimitiveTy
    )
        -> Error
    {
        let message = format!(
            "Encountered a value ({:?}) that is unrepresentable \
             by the destination type {:?}.", value, destination_ty);
        Error{
            kind: ErrorKind::ValueUnrepresentable{value, destination_ty},
            message,
            annotation: None
        }
    }

    pub(crate) fn division_by_zero(op: DivOp, lhs: ApInt) -> Error {
        let message = format!(
            "Encountered a division-by-zero for operation (= {:?}) with the left hand-side value: (= {:?})",
            op, lhs
        );
        Error{
            kind: ErrorKind::DivisionByZero{op, lhs},
            message,
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

/// The `Result` type used in `ApInt`.
pub type Result<T> = result::Result<T, Error>;
