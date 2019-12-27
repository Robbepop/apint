use crate::digit::Digit;

use core::slice;

/// A sequence of digits.
///
/// This is a very efficient `DigitSeq` since its data is contiguous in memory.
#[derive(Debug, Clone)]
pub(crate) struct ContiguousDigitSeq<'a> {
    digits: slice::Iter<'a, Digit>,
}

impl<'a> From<&'a [Digit]> for ContiguousDigitSeq<'a> {
    #[inline]
    fn from(slice: &'a [Digit]) -> ContiguousDigitSeq<'a> {
        ContiguousDigitSeq {
            digits: slice.iter(),
        }
    }
}

impl<'a> Iterator for ContiguousDigitSeq<'a> {
    type Item = Digit;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.digits.next().cloned()
    }
}

/// A sequence of mutable digits.
///
/// This is a very efficient `DigitSeqMut` since its data is contiguous in
/// memory.
#[derive(Debug)]
pub(crate) struct ContiguousDigitSeqMut<'a> {
    digits: slice::IterMut<'a, Digit>,
}

impl<'a> From<&'a mut [Digit]> for ContiguousDigitSeqMut<'a> {
    #[inline]
    fn from(slice: &'a mut [Digit]) -> ContiguousDigitSeqMut<'a> {
        ContiguousDigitSeqMut {
            digits: slice.iter_mut(),
        }
    }
}

impl<'a> Iterator for ContiguousDigitSeqMut<'a> {
    type Item = &'a mut Digit;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.digits.next()
    }
}
