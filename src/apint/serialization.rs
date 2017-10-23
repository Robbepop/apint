use radix::{Radix};
use bitwidth::{BitWidth};
use apint::{APInt};
use errors::{Result};

//  =======================================================================
///  Deserialization
/// =======================================================================
impl APInt {
	/// Parses the given `input` `String` with the given `Radix` and returns an `APInt`
	/// with the given `target_width` `BitWidth`.
	/// 
	/// **Note:** The given `input` is parsed as big-endian value. This means, the most significant bit (MSB)
	/// is the leftst bit in the string representation provided by the user.
	/// 
	/// The string is assumed to contain no whitespace and contain only values within a subset of the 
	/// range of `0`..`9` and `a`..`z` depending on the given `radix`.
	/// 
	/// The string is assumed to have no sign as `APInt` does not handle signdness.
	/// 
	/// # Errors
	/// 
	/// - If `input` is not a valid representation for an `APInt` for the given `radix`.
	/// - If `input` represents an `APInt` value that does not fit into the given `target_bitwidth`.
	/// 
	/// # Examples
	/// 
	/// ```no_run
	/// # use apint::APInt;
	/// let a = APInt::from_str_radix( 64, "42", 10); // ok
	/// let b = APInt::from_str_radix( 32, "1011011", 2); // ok (dec. = 91)
	/// let c = APInt::from_str_radix(128, "ffcc00", 16); // ok (dec. = 16763904)
	/// let c = APInt::from_str_radix(  8, "257", 10); // Error: 257 does not fit within 8 bits!
	/// let d = APInt::from_str_radix(100, "hello", 16); // Error: "hello" is not a valid APInt representation!
	/// ```
	pub fn from_str_radix<W, R>(target_width: W, input: &str, radix: R) -> Result<APInt>
		where W: Into<BitWidth>,
		      R: Into<Radix>
	{
		unimplemented!()		
	}
}

//  =======================================================================
///  Serialization
/// =======================================================================
impl APInt {
	/// Returns a `String` representation of the binary encoded `APInt` for the given `Radix`.
	pub fn as_string_with_radix<R>(&self, radix: R) -> String
		where R: Into<Radix>
	{
		unimplemented!();
	}
}
