
use storage::{Storage};
use digit::{Digit, Bit};
use apint::{ApInt};
use errors::{Error, Result};
use traits::Width;
use bitwidth::BitWidth;
use digit_seq::{
    ContiguousDigitSeq,
    ContiguousDigitSeqMut
};

use std::fmt;
use std::hash::{Hash, Hasher};

impl fmt::Debug for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ApInt")
         .field("len", &self.width())
         .field("digits", &self.as_digit_slice())
         .finish()
    }
}

impl Hash for ApInt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.as_digit_slice().hash(state);
    }
}

// ============================================================================

impl ApInt {
    pub(in apint) fn digits(&self) -> ContiguousDigitSeq {
        ContiguousDigitSeq::from(self.as_digit_slice())
    }

    pub(in apint) fn digits_mut(&mut self) -> ContiguousDigitSeqMut {
        ContiguousDigitSeqMut::from(self.as_digit_slice_mut())
    }
}

// ============================================================================

