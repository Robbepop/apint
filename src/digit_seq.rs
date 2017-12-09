use digit::Digit;

use std::slice;

/// A digit sequence is an iterator over `Digit` items.
pub(crate) trait DigitSeq<'a>: Iterator<Item=Digit> + 'a {}

/// A mutable digit sequence is an iterator over mutable `Digit` items.
pub(crate) trait DigitSeqMut<'a>: Iterator<Item=&'a mut Digit> {}

/// A sequence of digits.
/// 
/// This is a very efficient `DigitSeq` since its data is contiguous in memory.
#[derive(Debug, Clone)]
pub(crate) struct ContiguousDigitSeq<'a> {
	digits: slice::Iter<'a, Digit>
}

impl<'a> From<&'a [Digit]> for ContiguousDigitSeq<'a> {
	#[inline]
	fn from(slice: &'a [Digit]) -> ContiguousDigitSeq<'a> {
		ContiguousDigitSeq{digits: slice.iter()}
	}
}

impl<'a> Iterator for ContiguousDigitSeq<'a> {
	type Item = Digit;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.digits.next().cloned()
	}
}

impl<'a> DigitSeq<'a> for ContiguousDigitSeq<'a> {}

/// A sequence of mutable digits.
/// 
/// This is a very efficient `DigitSeqMut` since its data is contiguous in memory.
#[derive(Debug)]
pub(crate) struct ContiguousDigitSeqMut<'a> {
	digits: slice::IterMut<'a, Digit>
}

impl<'a> From<&'a mut [Digit]> for ContiguousDigitSeqMut<'a> {
	#[inline]
	fn from(slice: &'a mut [Digit]) -> ContiguousDigitSeqMut<'a> {
		ContiguousDigitSeqMut{digits: slice.iter_mut()}
	}
}

impl<'a> Iterator for ContiguousDigitSeqMut<'a> {
	type Item = &'a mut Digit;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.digits.next()
	}
}

impl<'a> DigitSeqMut<'a> for ContiguousDigitSeqMut<'a> {}

/// A type that acts as a sequence of digits.
/// 
/// This is used as abstraction over the different low-level representations
/// of an `ApInt`.
pub(crate) trait AsDigitSeq<'a> {
	type Seq: DigitSeq<'a>;

	/// Returns a sequence of digits.
	fn digits(self) -> Self::Seq;
}

/// A type that acts as a sequence of mutable digits.
/// 
/// This is used as abstraction over the different low-level representations
/// of an `ApInt`.
pub(crate) trait AsDigitSeqMut<'a> {
	type SeqMut: DigitSeqMut<'a>;

	/// Returns a sequence of mutable digits.
	fn digits_mut(self) -> Self::SeqMut;
}
