use errors::{Error, Result};

/// A radix for parsing strings as `APInt`s.
/// 
/// A radix represents the range of valid input characters that represent values
/// of the to-be-parsed `APInt`.
/// 
/// Supported radices range from unary radix (`1`) up
/// to full case-insensitive alphabet and numerals (`36`).
/// 
/// # Examples
/// 
/// - The binary 2-radix supports only `0` and `1` as input.
/// - The decimal 10-radix supports `0`,`1`,...`9` as input characters.
/// - The hex-dec 16-radix supports inputs characters within `0`,..,`9` and `a`,..,`f`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Radix(usize);

impl Radix {
	const MAX: usize = 36;

	/// Create a new `Radix` from the given `usize`.
	/// 
	/// # Errors
	/// 
	/// - If the given value is not within the valid radix range of `1..36`.
	#[inline]
	pub fn new(val: usize) -> Result<Radix> {
		if val == 0 || val > Radix::MAX {
			return Err(Error::invalid_radix(val))
		}
		Ok(Radix(val))
	}

	/// Returns the `usize` representation of this `Radix`.
	#[inline]
	pub fn to_usize(self) -> usize {
		self.0
	}
}

impl From<usize> for Radix {
	#[inline]
	fn from(val: usize) -> Radix {
		Radix::new(val).unwrap()
	}
}
