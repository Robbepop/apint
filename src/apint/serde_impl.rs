use crate::{mem::vec::Vec, ApInt, BitWidth, Digit};

use serde::{ser::SerializeTupleStruct, Serialize, Serializer};

impl Serialize for Digit {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(self.repr())
    }
}

impl Serialize for BitWidth {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            let mut s = serializer.serialize_tuple_struct("BitWidth", 1)?;
            s.serialize_field(&(self.to_usize() as u64))?;
            s.end()
        } else {
            serializer.serialize_u64(self.to_usize() as u64)
        }
    }
}

impl Serialize for ApInt {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::{SerializeStruct, SerializeTuple};

        if serializer.is_human_readable() {
            let mut s = serializer.serialize_struct("ApInt", 2)?;
            s.serialize_field("width", &self.len)?;
            s.serialize_field("digits", self.as_digit_slice())?;
            s.end()
        } else {
            let mut s = serializer.serialize_tuple(2)?;
            s.serialize_element(&self.len)?;
            s.serialize_element(&self.as_digit_slice())?;
            s.end()
        }
    }
}

use core::fmt;
use serde::{
    de,
    de::{MapAccess, SeqAccess, Visitor},
    Deserialize,
    Deserializer,
};

impl<'de> Deserialize<'de> for BitWidth {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct HumanReadableBitWidthVisitor;

        fn try_new_bitwidth<E>(width: usize) -> Result<BitWidth, E>
        where
            E: de::Error,
        {
            BitWidth::new(width as usize).map_err(|_| {
                de::Error::invalid_value(
                    de::Unexpected::Unsigned(width as u64),
                    &"a valid `u64` `BitWidth` representation",
                )
            })
        }

        impl<'de> Visitor<'de> for HumanReadableBitWidthVisitor {
            type Value = BitWidth;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("human-readable repr of `BitWidth`")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let width_repr: u64 = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                try_new_bitwidth(width_repr as usize)
            }
        }

        struct CompactBitWidthVisitor;

        impl<'de> Visitor<'de> for CompactBitWidthVisitor {
            type Value = BitWidth;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("compact repr of `BitWidth`")
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                try_new_bitwidth(v as usize)
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_tuple_struct(
                "BitWidth",
                1,
                HumanReadableBitWidthVisitor,
            )
        } else {
            deserializer.deserialize_u64(CompactBitWidthVisitor)
        }
    }
}

impl<'de> Deserialize<'de> for Digit {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct DigitVisitor;

        impl<'de> Visitor<'de> for DigitVisitor {
            type Value = Digit;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("`u64` repr of `Digit`")
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Digit(v))
            }
        }

        deserializer.deserialize_u64(DigitVisitor)
    }
}

impl<'de> Deserialize<'de> for ApInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            Width,
            Digits,
        }
        const FIELDS: &[&str] = &["width", "digits"];

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(
                        &self,
                        formatter: &mut fmt::Formatter,
                    ) -> fmt::Result {
                        formatter.write_str("`width` or `digits`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "width" => Ok(Field::Width),
                            "digits" => Ok(Field::Digits),
                            _ => Err(de::Error::unknown_field(value, FIELDS)),
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
            where
                V: MapAccess<'de>,
            {
                let mut width: Option<BitWidth> = None;
                let mut digits: Option<Vec<Digit>> = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Width => {
                            if width.is_some() {
                                return Err(de::Error::duplicate_field("width"))
                            }
                            width = Some(map.next_value()?);
                        }
                        Field::Digits => {
                            if digits.is_some() {
                                return Err(de::Error::duplicate_field("digits"))
                            }
                            digits = Some(map.next_value()?);
                        }
                    }
                }
                let width =
                    width.ok_or_else(|| de::Error::missing_field("width"))?;
                let digits =
                    digits.ok_or_else(|| de::Error::missing_field("digits"))?;

                if width.required_digits() != digits.len() {
                    return Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(digits.len() as u64),
                        &"require `width` to be compatible with `digits.len()`",
                    ))
                }

                Ok(ApInt::from_iter(digits)
                    .expect(
                        "We already asserted that we deserialized the lower-bound of \
                         `required_digits` so `ApInt::from_iter` is fail free.",
                    )
                    .into_truncate(width)
                    .expect(
                        "An `into_truncate` call to `width` cannot fail since `digits`
                             contains exactly `required_digits` digits and \
                         `ApInt::from_iter always creates an `ApInt` with an upper \
                         bound bit width.",
                    ))
            }
        }

        struct CompactApIntVisitor;

        impl<'de> Visitor<'de> for CompactApIntVisitor {
            type Value = ApInt;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("compact ApInt")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<ApInt, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let width: BitWidth = seq.next_element()?.unwrap();
                let digits: Vec<Digit> = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;

                if width.required_digits() != digits.len() {
                    return Err(de::Error::invalid_value(
                        de::Unexpected::Seq,
                        &"unexpected number of digits found",
                    ))
                }

                Ok(ApInt::from_iter(digits)
                    .expect(
                        "We already asserted that we deserialized the lower-bound of \
                         `required_digits` so `ApInt::from_iter` is fail free.",
                    )
                    .into_truncate(width)
                    .expect(
                        "An `into_truncate` call to `width` cannot fail since `digits` \
                         contains exactly `required_digits` digits and \
                         `ApInt::from_iter always creates an `ApInt` with an upper \
                         bound bit width.",
                    ))
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_struct(
                "ApInt",
                FIELDS,
                HumanReadableApIntVisitor,
            )
        } else {
            deserializer.deserialize_tuple(2, CompactApIntVisitor)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use serde_test::{assert_tokens, Token};

    mod compact {
        use super::*;
        use serde_test::Configure;

        #[test]
        fn test_small() {
            let x = ApInt::from_u64(0xFEDC_BA98_7654_3210);
            let expected = &[
                Token::Tuple { len: 2 },
                Token::U64(64),
                Token::Seq { len: Some(1) },
                Token::U64(0xFEDC_BA98_7654_3210),
                Token::SeqEnd,
                Token::TupleEnd,
            ];
            assert_tokens(&x.compact(), expected)
        }

        #[test]
        fn test_large() {
            let x =
                ApInt::from_u128(0xFEDC_BA98_7654_3210__0101_1010_0110_1001);
            let expected = &[
                Token::Tuple { len: 2 },
                Token::U64(128),
                Token::Seq { len: Some(2) },
                Token::U64(0x0101_1010_0110_1001),
                Token::U64(0xFEDC_BA98_7654_3210),
                Token::SeqEnd,
                Token::TupleEnd,
            ];
            assert_tokens(&x.compact(), expected)
        }
    }

    mod human_readable {
        use super::*;
        use serde_test::Configure;

        #[test]
        fn test_small() {
            let x = ApInt::from_u64(42);
            let expected = &[
                Token::Struct {
                    name: "ApInt",
                    len: 2,
                },
                Token::Str("width"),
                Token::TupleStruct {
                    name: "BitWidth",
                    len: 1,
                },
                Token::U64(64),
                Token::TupleStructEnd,
                Token::Str("digits"),
                Token::Seq { len: Some(1) },
                Token::U64(42),
                Token::SeqEnd,
                Token::StructEnd,
            ];
            assert_tokens(&x.clone().readable(), expected);
        }

        #[test]
        fn test_large() {
            let x = ApInt::from_u128(1337);
            let expected = &[
                Token::Struct {
                    name: "ApInt",
                    len: 2,
                },
                Token::Str("width"),
                Token::TupleStruct {
                    name: "BitWidth",
                    len: 1,
                },
                Token::U64(128),
                Token::TupleStructEnd,
                Token::Str("digits"),
                Token::Seq { len: Some(2) },
                Token::U64(1337),
                Token::U64(0),
                Token::SeqEnd,
                Token::StructEnd,
            ];
            assert_tokens(&x.clone().readable(), expected);
        }
    }
}
