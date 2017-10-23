use digit;
use bitwidth::BitWidth;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Storage { Inl, Ext }

impl<W> From<W> for Storage
	where W: Into<BitWidth>
{
	#[inline]
	fn from(width: W) -> Storage {
		let width = width.into();
		if Storage::is_inline(width) {
			Storage::Inl
		}
		else {
			Storage::Ext
		}
	}
}

impl Storage {
	/// Returns `true` if the given `BitWidth` is small enough to be stored inline.
	/// 
	/// Note: Inline storage in the context of `APInt` means that it is space-optimized
	///       similar to the well-known small-string optimization.
	#[inline]
	fn is_inline(width: BitWidth) -> bool {
		width.to_usize() < digit::BITS
	}

	/// Returns `true` if the given `BitWidth` is large enough to require it to be stored externally.
	/// 
	/// Note: External storage in the context of `APInt` means that it is **not** space-optimized
	///       and thus stored on the heap with indirect access via pointer-to-data.
	#[inline]
	fn is_extern(width: BitWidth) -> bool {
		!Storage::is_inline(width)
	}
}
