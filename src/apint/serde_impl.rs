use apint::{ApInt};
use digit::{Digit};
use bitwidth::{BitWidth};

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
        use serde::ser::{SerializeStruct, SerializeTuple};

        let len_digits = self.len.to_usize() as u64;

        if serializer.is_human_readable() {
            let mut s = serializer.serialize_struct("ApInt", 2)?;
            s.serialize_field("width", &len_digits)?;
            s.serialize_field("digits", self.as_digit_slice())?;
            s.end()
        }
        else {
            let mut s = serializer.serialize_tuple(2)?;
            s.serialize_element(&len_digits)?;
            s.serialize_element(&self.as_digit_slice())?;
            s.end()
        }
    }
}

use serde::{
    Deserialize,
    Deserializer
};
use serde::de::{
    Visitor,
    SeqAccess,
    MapAccess
};
use serde::de;
use std::fmt;

impl<'de> Deserialize<'de> for Digit {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct DigitVisitor;

        impl<'de> Visitor<'de> for DigitVisitor {
            type Value = Digit;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("`u64` repr of `Digit`")
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
                where E: de::Error
            {
                Ok(Digit(v as u64))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
                where E: de::Error
            {
                Ok(Digit(v))
            }
        }

        deserializer.deserialize_u64(DigitVisitor)
    }
}

impl<'de> Deserialize<'de> for ApInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        enum Field { Width, Digits }
        const FIELDS: &[&str] = &["width", "digits"];

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
                where D: Deserializer<'de>
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("`width` or `digits`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                        where E: de::Error
                    {
                        match value {
                            "width" => Ok(Field::Width),
                            "digits" => Ok(Field::Digits),
                            _ => Err(de::Error::unknown_field(value, FIELDS))
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct HumanReadableApIntVisitor;

        impl<'de> Visitor<'de> for HumanReadableApIntVisitor {
            type Value = ApInt;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct ApInt")
            }

            fn visit_map<V>(self, mut map: V) -> Result<ApInt, V::Error>
                where V: MapAccess<'de>
            {
                let mut width : Option<u64>        = None;
                let mut digits: Option<Vec<Digit>> = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Width => {
                            if width.is_some() {
                                return Err(de::Error::duplicate_field("width"));
                            }
                            width = Some(map.next_value()?);
                        }
                        Field::Digits => {
                            if digits.is_some() {
                                return Err(de::Error::duplicate_field("digits"));
                            }
                            digits = Some(map.next_value()?);
                        }
                    }
                }
                let width = width.ok_or_else(|| de::Error::missing_field("width"))?;
                let digits = digits.ok_or_else(|| de::Error::missing_field("digits"))?;

                let width: BitWidth = BitWidth::new(width as usize)
                    .map_err(|_| de::Error::invalid_value(
                            de::Unexpected::Unsigned(width),
                            &"a valid `u64` `BitWidth` representation"
                        )
                    )?;

                if width.required_digits() != digits.len() {
                    return Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(digits.len() as u64),
                        &"require `width` to be compatible with `digits.len()`"))
                }

                Ok(ApInt::from_iter(digits)
                    .expect("We already asserted that we deserialized the lower-bound \
                             of `required_digits` so `ApInt::from_iter` is fail free.")
                    .into_truncate(width)
                    .expect("An `into_truncate` call to `width` cannot fail since `digits`
                             contains exactly `required_digits` digits and `ApInt::from_iter \
                             always creates an `ApInt` with an upper bound bit width."))
            }
        }

        struct CompactApIntVisitor;

        impl<'de> Visitor<'de> for CompactApIntVisitor {
            type Value = ApInt;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("compact ApInt")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<ApInt, V::Error>
                where V: SeqAccess<'de>
            {
                let width_repr: u64 = seq.next_element()?
                                         .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let width: BitWidth = BitWidth::new(width_repr as usize)
                    .map_err(|_| de::Error::invalid_value(
                            de::Unexpected::Unsigned(width_repr),
                            &"a valid `u64` `BitWidth` representation"
                        )
                    )?;
 
                let digits: Vec<Digit> = seq.next_element()?
                                            .ok_or_else(|| de::Error::invalid_length(1, &self))?;

                if width.required_digits() != digits.len() {
                    return Err(de::Error::invalid_value(
                        de::Unexpected::Seq, &"unexpected number of digits found"))
                }

                Ok(ApInt::from_iter(digits)
                    .expect("We already asserted that we deserialized the lower-bound \
                             of `required_digits` so `ApInt::from_iter` is fail free.")
                    .into_truncate(width)
                    .expect("An `into_truncate` call to `width` cannot fail since `digits`
                             contains exactly `required_digits` digits and `ApInt::from_iter \
                             always creates an `ApInt` with an upper bound bit width."))
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_struct("ApInt", FIELDS, HumanReadableApIntVisitor)
        }
        else {
            deserializer.deserialize_tuple(2, CompactApIntVisitor)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use serde_test::{
        Token,
        Configure,
        assert_tokens
    };

    mod compact {
        use super::*;

        #[test]
        fn test_small() {
            let x = ApInt::from_u64(0xFEDC_BA98_7654_3210);
            let expected = &[
                Token::Tuple{ len: 2 },
                Token::U64(64),
                Token::Seq{ len: Some(1) },
                Token::U64(0xFEDC_BA98_7654_3210),
                Token::SeqEnd,
                Token::TupleEnd
            ];
            assert_tokens(&x.compact(), expected)
        }

        #[test]
        fn test_large() {
            let x = ApInt::from_u128(
                0xFEDC_BA98_7654_3210__0101_1010_0110_1001);
            let expected = &[
                Token::Tuple{ len: 2 },
                Token::U64(128),
                Token::Seq{ len: Some(2) },
                Token::U64(0x0101_1010_0110_1001),
                Token::U64(0xFEDC_BA98_7654_3210),
                Token::SeqEnd,
                Token::TupleEnd
            ];
            assert_tokens(&x.compact(), expected)
        }
    }

    mod human_readable {
        use super::*;

        #[test]
        fn test_small() {
            let x = ApInt::from_u64(42);
            let expected = &[
                Token::Struct{
                    name: "ApInt",
                    len: 2
                },
                Token::Str("width"),
                Token::U64(64),
                Token::Str("digits"),
                Token::Seq{ len: Some(1) },
                Token::U64(42),
                Token::SeqEnd,
                Token::StructEnd
            ];
            // assert_tokens(&x.clone().compact(), expected);
            assert_tokens(&x.clone().readable(), expected);
        }

        #[test]
        fn test_large() {
            let x = ApInt::from_u128(1337);
            let expected = &[
                Token::Struct{
                    name: "ApInt",
                    len: 2
                },
                Token::Str("width"),
                Token::U64(128),
                Token::Str("digits"),
                Token::Seq{ len: Some(2) },
                Token::U64(1337),
                Token::U64(0),
                Token::SeqEnd,
                Token::StructEnd
            ];
            // assert_tokens(&x.clone().compact(), expected);
            assert_tokens(&x.clone().readable(), expected);
        }
    }
}
