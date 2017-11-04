use digit::Digit;

use std::slice;

/// A digit sequence is an iterator over `Digit` items.
pub(crate) trait DigitSeq: Iterator<Item=Digit> {}

/// A mutable digit sequence is an iterator over mutable `Digit` items.
pub(crate) trait DigitSeqMut<'a>: Iterator<Item=&'a mut Digit> {}

/// A sequence of digits.
/// 
/// This is a very efficient `DigitSeq` since its data is contiguous in memory.
#[derive(Debug, Clone)]
pub(crate) struct ContiguousDigitSeq<'a> {
	digits: slice::Iter<'a, Digit>
}

impl<'a> Iterator for ContiguousDigitSeq<'a> {
	type Item = Digit;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.digits.next().cloned()
	}
}

impl<'a> DigitSeq for ContiguousDigitSeq<'a> {}

/// A sequence of mutable digits.
/// 
/// This is a very efficient `DigitSeqMut` since its data is contiguous in memory.
#[derive(Debug)]
pub(crate) struct ContiguousDigitSeqMut<'a> {
	digits: slice::IterMut<'a, Digit>
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
/// of an `APInt`.
pub(crate) trait AsDigitSeq {
	type Seq: DigitSeq;

	/// Returns a sequence of digits.
	fn digits(&self) -> Self::Seq;
}

/// A type that acts as a sequence of mutable digits.
/// 
/// This is used as abstraction over the different low-level representations
/// of an `APInt`.
pub(crate) trait AsDigitSeqMut<'a>: AsDigitSeq {
	type SeqMut: DigitSeqMut<'a>;

	/// Returns a sequence of mutable digits.
	fn digits_mut(&mut self) -> Self::SeqMut;
}
