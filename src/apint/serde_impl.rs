use apint::{ApInt};
use digit::{Digit};

use serde::{
    Serialize,
    Serializer
};

impl Serialize for Digit {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_u64(self.repr())
    }
}

impl Serialize for ApInt {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        use serde::ser::SerializeStruct;
        let mut s = serializer.serialize_struct("ApInt", 3)?;
        s.serialize_field("width", &(self.len.to_usize() as u64))?;
        s.serialize_field("digits", self.as_digit_slice())?;
        s.end()
    }
}
