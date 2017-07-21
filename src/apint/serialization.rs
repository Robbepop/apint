
//  =======================================================================
///  Deserialization
/// =======================================================================
impl APInt {

	/// Creates a new bitvector from the given binary string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the binary string must follow some rules.
	///  - The only allowed characters are digits `'0'`, `'1'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single `'0'` or `'1'` character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"0101"`
	/// - `"0111_0010_0000_1110"`
	/// - `"11__00"`
	/// - `"__0__"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"0102"`
	/// - `"01'0001"`
	/// - `"foo"`
	/// - `"-1001"`
	/// 
	/// # Note
	/// 
	/// - The most significant bit (MSB) is on the left.
	/// - The bitwidth of the resulting `APInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `APInt`.
	pub fn from_bin_str(bitwidth: TargetBitWidth, binary_str: &str) -> Result<APInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given decimal string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the decimal string must follow some rules.
	///  - The only allowed characters are digits `'0'`, `'1'`,..,`'9'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single valid digit character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"3497"`
	/// - `"0323_0321_9876_5432"`
	/// - `"85__132"`
	/// - `"__9__"`
	/// - `"000075"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"0A5C"`
	/// - `"13'8273"`
	/// - `"bar"`
	/// - `"-1337"`
	/// 
	/// # Note
	/// 
	/// - The most significant digit is on the left.
	/// - The bitwidth of the resulting `APInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `APInt`.
	pub fn from_dec_str(bitwidth: TargetBitWidth, dec_str: &str) -> Result<APInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given hexa-decimal string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the decimal string must follow some rules.
	///  - The only allowed characters are the digits `'0'`, `'1'`,..,`'9'` the alphas `'A'`,`'B'`,..,`'F'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single valid alpha-numeric character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"AC08"`
	/// - `"03B8_A30D_EEE2_007"`
	/// - `"FF__A00"`
	/// - `"__E__"`
	/// - `"B008CE"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"ffcc0"`: no small letters!
	/// - `"0K5X"`
	/// - `"13'8273"`
	/// - `"foobar"`
	/// - `"-MCLVII"`
	/// 
	/// # Note
	/// 
	/// - The most significant quad is on the left.
	/// - The bitwidth of the resulting `APInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `APInt`.
	pub fn from_hex_str(bitwidth: TargetBitWidth, hex_str: &str) -> Result<APInt> {
		unimplemented!();
	}

}

//  =======================================================================
///  Serialization
/// =======================================================================
impl APInt {

	/// Returns a string representation of the binary encoded bitvector.
	pub fn to_bin_string(&self) -> String {
		unimplemented!();
	}

	/// Returns a string representation of the decimal encoded bitvector.
	pub fn to_dec_string(&self) -> String {
		unimplemented!();
	}

	/// Returns a string representation of the hex-decimal encoded bitvector.
	pub fn to_hex_string(&self) -> String {
		unimplemented!();
	}

}
