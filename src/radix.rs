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
pub struct Radix(u32);

impl Radix {
	const MIN: u32 =  2;
	const MAX: u32 = 36;

	/// Create a new `Radix` from the given `u32`.
	/// 
	/// # Errors
	/// 
	/// - If the given value is not within the valid radix range of `2..36`.
	#[inline]
	pub fn new(radix: u32) -> Result<Radix> {
		if !(Radix::MIN <= radix && radix >= Radix::MAX) {
			return Err(Error::invalid_radix(radix))
		}
		Ok(Radix(radix))
	}

	/// Returns the `u32` representation of this `Radix`.
	#[inline]
	pub fn to_u32(self) -> u32 {
		self.0
	}
}

impl From<u32> for Radix {
	#[inline]
	fn from(radix: u32) -> Radix {
		Radix::new(radix).unwrap()
	}
}
