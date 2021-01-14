//! Deserialize JSON data to a Rust data structure

mod enum_;
mod errors;
mod map;
mod seq;
mod unescape;

pub use errors::{Error, Result};

use std::str::{self, FromStr};

use serde::de::{self, Visitor};

use self::enum_::{UnitVariantAccess, VariantAccess};
use self::map::MapAccess;
use self::seq::SeqAccess;
use std::str::from_utf8;

/// Deserializer will parse serde-json-wasm flavored JSON into a
/// serde-annotated struct
pub struct Deserializer<'b> {
    slice: &'b [u8],
    index: usize,
}

enum StringLike<'a> {
    Borrowed(&'a str),
    Owned(String),
}

impl<'a> Deserializer<'a> {
    /// Create a new `Deserializer`
    pub fn new(slice: &'a [u8]) -> Deserializer<'_> {
        Deserializer { slice, index: 0 }
    }

    fn eat_char(&mut self) {
        self.index += 1;
    }

    /// Check whether there is any unexpected data left in the buffer
    /// and return the amount of data consumed
    pub fn end(&mut self) -> Result<usize> {
        match self.parse_whitespace() {
            Some(_) => Err(Error::TrailingCharacters),
            None => Ok(self.index),
        }
    }

    fn end_seq(&mut self) -> Result<()> {
        match self.parse_whitespace().ok_or(Error::EofWhileParsingList)? {
            b']' => {
                self.eat_char();
                Ok(())
            }
            b',' => {
                self.eat_char();
                match self.parse_whitespace() {
                    Some(b']') => Err(Error::TrailingComma),
                    _ => Err(Error::TrailingCharacters),
                }
            }
            _ => Err(Error::TrailingCharacters),
        }
    }

    fn end_map(&mut self) -> Result<()> {
        match self
            .parse_whitespace()
            .ok_or(Error::EofWhileParsingObject)?
        {
            b'}' => {
                self.eat_char();
                Ok(())
            }
            b',' => Err(Error::TrailingComma),
            _ => Err(Error::TrailingCharacters),
        }
    }

    fn next_char(&mut self) -> Option<u8> {
        let ch = self.slice.get(self.index);

        if ch.is_some() {
            self.index += 1;
        }

        ch.cloned()
    }

    fn parse_ident(&mut self, ident: &[u8]) -> Result<()> {
        for c in ident {
            if Some(*c) != self.next_char() {
                return Err(Error::ExpectedSomeIdent);
            }
        }

        Ok(())
    }

    fn parse_object_colon(&mut self) -> Result<()> {
        match self
            .parse_whitespace()
            .ok_or(Error::EofWhileParsingObject)?
        {
            b':' => {
                self.eat_char();
                Ok(())
            }
            _ => Err(Error::ExpectedColon),
        }
    }

    fn parse_string(&mut self) -> Result<StringLike<'a>> {
        let start = self.index;
        let mut contains_backslash = false;
        let mut escaped = false;
        loop {
            match self.peek() {
                Some(b'"') => {
                    if escaped {
                        escaped = false;
                        self.eat_char(); // just continue
                    } else {
                        let end = self.index;
                        self.eat_char();
                        return if contains_backslash {
                            Ok(StringLike::Owned(unescape::unescape(
                                &self.slice[start..end],
                            )?))
                        } else {
                            Ok(StringLike::Borrowed(
                                from_utf8(&self.slice[start..end])
                                    .map_err(|_| Error::InvalidUnicodeCodePoint)?,
                            ))
                        };
                    }
                }
                Some(b'\\') => {
                    contains_backslash = true;
                    escaped = !escaped;
                    self.eat_char()
                }
                Some(_) => {
                    escaped = false;
                    self.eat_char()
                }
                None => return Err(Error::EofWhileParsingString),
            }
        }
    }

    /// Consumes all the whitespace characters and returns a peek into the next character
    fn parse_whitespace(&mut self) -> Option<u8> {
        loop {
            match self.peek() {
                Some(b' ') | Some(b'\n') | Some(b'\t') | Some(b'\r') => {
                    self.eat_char();
                }
                other => {
                    return other;
                }
            }
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.slice.get(self.index).cloned()
    }
}

// NOTE(deserialize_*signed) we avoid parsing into u64 and then casting to a smaller integer, which
// is what upstream does, to avoid pulling in 64-bit compiler intrinsics, which waste a few KBs of
// Flash, when targeting non 64-bit architectures
macro_rules! deserialize_unsigned {
    ($self:ident, $visitor:ident, $uxx:ident, $visit_uxx:ident) => {{
        let peek = $self
            .parse_whitespace()
            .ok_or(Error::EofWhileParsingValue)?;

        match peek {
            b'-' => Err(Error::InvalidNumber),
            b'0' => {
                $self.eat_char();
                $visitor.$visit_uxx(0)
            }
            b'1'..=b'9' => {
                $self.eat_char();

                let mut number = (peek - b'0') as $uxx;
                loop {
                    match $self.peek() {
                        Some(c @ b'0'..=b'9') => {
                            $self.eat_char();
                            number = number
                                .checked_mul(10)
                                .ok_or(Error::InvalidNumber)?
                                .checked_add((c - b'0') as $uxx)
                                .ok_or(Error::InvalidNumber)?;
                        }
                        _ => return $visitor.$visit_uxx(number),
                    }
                }
            }
            _ => Err(Error::InvalidType),
        }
    }};
}

macro_rules! deserialize_signed {
    ($self:ident, $visitor:ident, $ixx:ident, $visit_ixx:ident) => {{
        let signed = match $self
            .parse_whitespace()
            .ok_or(Error::EofWhileParsingValue)?
        {
            b'-' => {
                $self.eat_char();
                true
            }
            _ => false,
        };

        match $self.peek().ok_or(Error::EofWhileParsingValue)? {
            b'0' => {
                $self.eat_char();
                $visitor.$visit_ixx(0)
            }
            c @ b'1'..=b'9' => {
                $self.eat_char();

                let mut number = (c - b'0') as $ixx * if signed { -1 } else { 1 };
                loop {
                    match $self.peek() {
                        Some(c @ b'0'..=b'9') => {
                            $self.eat_char();
                            number = number
                                .checked_mul(10)
                                .ok_or(Error::InvalidNumber)?
                                .checked_add((c - b'0') as $ixx * if signed { -1 } else { 1 })
                                .ok_or(Error::InvalidNumber)?;
                        }
                        _ => return $visitor.$visit_ixx(number),
                    }
                }
            }
            _ => return Err(Error::InvalidType),
        }
    }};
}

macro_rules! deserialize_fromstr {
    ($self:ident, $visitor:ident, $typ:ident, $visit_fn:ident, $pattern:expr) => {{
        match $self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
            b'n' => {
                $self.eat_char();
                $self.parse_ident(b"ull")?;
                $visitor.$visit_fn($typ::NAN)
            }
            _ => {
                let start = $self.index;
                while $self.peek().is_some() {
                    let c = $self.peek().unwrap();
                    if $pattern.iter().find(|&&d| d == c).is_some() {
                        $self.eat_char();
                    } else {
                        break;
                    }
                }

                // Note(unsafe): We already checked that it only contains ascii. This is only true if the
                // caller has guaranteed that `pattern` contains only ascii characters.
                let s = unsafe { str::from_utf8_unchecked(&$self.slice[start..$self.index]) };

                let v = $typ::from_str(s).or(Err(Error::InvalidNumber))?;

                $visitor.$visit_fn(v)
            }
        }
    }};
}

impl<'a, 'de> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    /// Unsupported. We rely on typed deserialization methods, even if a JSON
    /// has enough type information to detect types in many cases.
    ///
    /// See https://serde.rs/impl-deserialize.html to learn more about the differentiation
    /// between `deserialize_{type}` and `deserialize_any`.
    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unreachable!()
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let peek = self.parse_whitespace().ok_or(Error::EofWhileParsingValue)?;

        match peek {
            b't' => {
                self.eat_char();
                self.parse_ident(b"rue")?;
                visitor.visit_bool(true)
            }
            b'f' => {
                self.eat_char();
                self.parse_ident(b"alse")?;
                visitor.visit_bool(false)
            }
            _ => Err(Error::InvalidType),
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_signed!(self, visitor, i8, visit_i8)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_signed!(self, visitor, i16, visit_i16)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_signed!(self, visitor, i32, visit_i32)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_signed!(self, visitor, i64, visit_i64)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_unsigned!(self, visitor, u8, visit_u8)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_unsigned!(self, visitor, u16, visit_u16)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_unsigned!(self, visitor, u32, visit_u32)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_unsigned!(self, visitor, u64, visit_u64)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_fromstr!(self, visitor, f32, visit_f32, b"0123456789+-.eE")
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        deserialize_fromstr!(self, visitor, f64, visit_f64, b"0123456789+-.eE")
    }

    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unreachable!()
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let peek = self.parse_whitespace().ok_or(Error::EofWhileParsingValue)?;

        match peek {
            b'"' => {
                self.eat_char();
                let str_like = self.parse_string()?;
                match str_like {
                    StringLike::Borrowed(str) => visitor.visit_borrowed_str(str),
                    StringLike::Owned(string) => visitor.visit_string(string),
                }
            }
            _ => Err(Error::InvalidType),
        }
    }

    /// Unsupported
    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unreachable!()
    }

    /// Unsupported
    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unreachable!()
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
            b'n' => {
                self.eat_char();
                self.parse_ident(b"ull")?;
                visitor.visit_none()
            }
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let peek = match self.parse_whitespace() {
            Some(b) => b,
            None => {
                return Err(Error::EofWhileParsingValue);
            }
        };

        match peek {
            b'n' => {
                self.eat_char();
                self.parse_ident(b"ull")?;
                visitor.visit_unit()
            }
            _ => Err(Error::InvalidType),
        }
    }

    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let peek = self.parse_whitespace().ok_or(Error::EofWhileParsingValue)?;

        if peek == b'n' {
            self.eat_char();
            self.parse_ident(b"ull")?;
            let ret = visitor.visit_unit()?;
            Ok(ret)
        } else {
            self.deserialize_unit(visitor)
        }
    }

    /// Unsupported. We can’t parse newtypes because we don’t know the underlying type.
    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
            b'[' => {
                self.eat_char();
                let ret = visitor.visit_seq(SeqAccess::new(self))?;

                self.end_seq()?;

                Ok(ret)
            }
            _ => Err(Error::InvalidType),
        }
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let peek = self.parse_whitespace().ok_or(Error::EofWhileParsingValue)?;

        if peek == b'{' {
            self.eat_char();

            let ret = visitor.visit_map(MapAccess::new(self))?;

            self.end_map()?;

            Ok(ret)
        } else {
            Err(Error::InvalidType)
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
            // if it is a string enum
            b'"' => visitor.visit_enum(UnitVariantAccess::new(self)),
            b'{' => {
                self.eat_char();
                let value = visitor.visit_enum(VariantAccess::new(self))?;
                match self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
                    b'}' => {
                        self.eat_char();
                        Ok(value)
                    }
                    _ => Err(Error::ExpectedSomeValue),
                }
            }
            _ => Err(Error::ExpectedSomeValue),
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    /// Used to throw out fields from JSON objects that we don’t want to
    /// keep in our structs.
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.parse_whitespace().ok_or(Error::EofWhileParsingValue)? {
            b'"' => self.deserialize_str(visitor),
            b'[' => self.deserialize_seq(visitor),
            b'{' => self.deserialize_struct("ignored", &[], visitor),
            b',' | b'}' | b']' => Err(Error::ExpectedSomeValue),
            // If it’s something else then we chomp until we get to an end delimiter.
            // This does technically allow for illegal JSON since we’re just ignoring
            // characters rather than parsing them.
            _ => loop {
                match self.peek() {
                    // The visitor is expected to be UnknownAny’s visitor, which
                    // implements visit_unit to return its unit Ok result.
                    Some(b',') | Some(b'}') | Some(b']') => break visitor.visit_unit(),
                    Some(_) => self.eat_char(),
                    None => break Err(Error::EofWhileParsingString),
                }
            },
        }
    }
}

/// Deserializes an instance of type `T` from bytes of JSON text
pub fn from_slice<T>(v: &[u8]) -> Result<T>
where
    T: de::DeserializeOwned,
{
    let mut de = Deserializer::new(v);
    let value = de::Deserialize::deserialize(&mut de)?;
    de.end()?;

    Ok(value)
}

/// Deserializes an instance of type T from a string of JSON text
pub fn from_str<T>(s: &str) -> Result<T>
where
    T: de::DeserializeOwned,
{
    from_slice(s.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::from_str;
    use serde_derive::Deserialize;

    #[derive(Debug, Deserialize, PartialEq)]
    enum Type {
        #[serde(rename = "boolean")]
        Boolean,
        #[serde(rename = "number")]
        Number,
        #[serde(rename = "thing")]
        Thing,
    }

    #[test]
    fn parse_whitespace() {
        assert_eq!(from_str(" true"), Ok(true));
        assert_eq!(from_str("\ttrue"), Ok(true));
        assert_eq!(from_str("\ntrue"), Ok(true));
        assert_eq!(from_str("\rtrue"), Ok(true));
        assert_eq!(from_str("\n\rtrue"), Ok(true));
        assert_eq!(from_str("\r\ntrue"), Ok(true));
        assert_eq!(from_str("true "), Ok(true));
        assert_eq!(from_str("true\t"), Ok(true));
        assert_eq!(from_str("true\n"), Ok(true));
        assert_eq!(from_str("true\r"), Ok(true));
        assert_eq!(from_str("true\n\r"), Ok(true));
        assert_eq!(from_str("true\r\n"), Ok(true));

        assert_eq!(from_str("[4,5]"), Ok([4, 5]));
        assert_eq!(from_str(" [4,5]"), Ok([4, 5]));
        assert_eq!(from_str("\t[4,5]"), Ok([4, 5]));
        assert_eq!(from_str("\n[4,5]"), Ok([4, 5]));
        assert_eq!(from_str("\r[4,5]"), Ok([4, 5]));
        assert_eq!(from_str("\n\r[4,5]"), Ok([4, 5]));
        assert_eq!(from_str("\r\n[4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[ 4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[\t4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[\n4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[\r4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[\n\r4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[\r\n4,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4 ,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4\t,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4\n,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4\r,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4\n\r,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4\r\n,5]"), Ok([4, 5]));
        assert_eq!(from_str("[4, 5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,\t5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,\n5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,\r5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,\n\r5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,\r\n5]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5 ]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5\t]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5\n]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5\r]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5\n\r]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5\r\n]"), Ok([4, 5]));
        assert_eq!(from_str("[4,5] "), Ok([4, 5]));
        assert_eq!(from_str("[4,5]\t"), Ok([4, 5]));
        assert_eq!(from_str("[4,5]\n"), Ok([4, 5]));
        assert_eq!(from_str("[4,5]\r"), Ok([4, 5]));
        assert_eq!(from_str("[4,5]\n\r"), Ok([4, 5]));
        assert_eq!(from_str("[4,5]\r\n"), Ok([4, 5]));
    }

    #[test]
    fn array() {
        assert_eq!(from_str::<[i32; 0]>("[]"), Ok([]));
        assert_eq!(from_str("[0, 1, 2]"), Ok([0, 1, 2]));

        // errors
        assert!(from_str::<[i32; 2]>("[0, 1,]").is_err());
    }

    #[test]
    fn tuple_variant() {
        #[derive(Debug, Deserialize, PartialEq)]
        enum Ops {
            Exit(),
            Square(i32),
            Add(i64, i64),
        }
        assert_eq!(from_str(r#"{"Exit":[]}"#), Ok(Ops::Exit()));
        assert_eq!(
            serde_json::from_str::<Ops>(r#"{"Exit":[]}"#).unwrap(),
            Ops::Exit()
        );
        assert_eq!(from_str(r#"{"Square":1}"#), Ok(Ops::Square(1)));
        assert_eq!(
            serde_json::from_str::<Ops>(r#"{"Square":1}"#).unwrap(),
            Ops::Square(1)
        );
        assert_eq!(from_str(r#"{"Add":[2,3]}"#), Ok(Ops::Add(2, 3)));
        assert_eq!(
            serde_json::from_str::<Ops>(r#"{"Add":[2,3]}"#).unwrap(),
            Ops::Add(2, 3)
        );
    }

    #[test]
    fn bool() {
        assert_eq!(from_str("true"), Ok(true));
        assert_eq!(from_str(" true"), Ok(true));
        assert_eq!(from_str("true "), Ok(true));

        assert_eq!(from_str("false"), Ok(false));
        assert_eq!(from_str(" false"), Ok(false));
        assert_eq!(from_str("false "), Ok(false));

        // errors
        assert!(from_str::<bool>("true false").is_err());
        assert!(from_str::<bool>("tru").is_err());
    }

    #[test]
    fn floating_point() {
        assert_eq!(from_str("5.0"), Ok(5.0));
        assert_eq!(from_str("1"), Ok(1.0));
        assert_eq!(from_str("1e5"), Ok(1e5));
        assert!(from_str::<f32>("a").is_err());
        assert!(from_str::<f32>(",").is_err());
    }

    #[test]
    fn integer() {
        assert_eq!(from_str("5"), Ok(5));
        assert_eq!(from_str("101"), Ok(101));
        assert!(dbg!(from_str::<u16>("1e5")).is_err());
        assert!(from_str::<u8>("256").is_err());
        assert!(from_str::<f32>(",").is_err());
    }

    #[test]
    fn enum_clike() {
        assert_eq!(from_str(r#" "boolean" "#), Ok(Type::Boolean));
        assert_eq!(from_str(r#" "number" "#), Ok(Type::Number));
        assert_eq!(from_str(r#" "thing" "#), Ok(Type::Thing));
    }

    #[test]
    fn str() {
        assert_eq!(from_str(r#" "hello" "#), Ok("hello".to_string()));
        assert_eq!(from_str(r#" "" "#), Ok("".to_string()));
        assert_eq!(from_str(r#" " " "#), Ok(" ".to_string()));
        assert_eq!(from_str(r#" "👏" "#), Ok("👏".to_string()));

        // Unescapes things
        assert_eq!(from_str(r#" "hel\tlo" "#), Ok("hel\tlo".to_string()));
        assert_eq!(from_str(r#" "hel\\lo" "#), Ok("hel\\lo".to_string()));

        // escaped " in the string content
        assert_eq!(from_str(r#" "foo\"bar" "#), Ok(r#"foo"bar"#.to_string()));
        assert_eq!(from_str(r#" "foo\\\"ba" "#), Ok(r#"foo\"ba"#.to_string()));
        assert_eq!(from_str(r#" "foo\"\"ba" "#), Ok(r#"foo""ba"#.to_string()));
        assert_eq!(from_str(r#" "\"bar" "#), Ok(r#""bar"#.to_string()));
        assert_eq!(from_str(r#" "foo\"" "#), Ok(r#"foo""#.to_string()));
        assert_eq!(from_str(r#" "\"" "#), Ok(r#"""#.to_string()));

        // non-escaped " preceded by backslashes
        assert_eq!(from_str(r#" "foo bar\\" "#), Ok(r#"foo bar\"#.to_string()));
        assert_eq!(
            from_str(r#" "foo bar\\\\" "#),
            Ok(r#"foo bar\\"#.to_string())
        );
        assert_eq!(
            from_str(r#" "foo bar\\\\\\" "#),
            Ok(r#"foo bar\\\"#.to_string())
        );
        assert_eq!(
            from_str(r#" "foo bar\\\\\\\\" "#),
            Ok(r#"foo bar\\\\"#.to_string())
        );
        assert_eq!(from_str(r#" "\\" "#), Ok(r#"\"#.to_string()));
        assert_eq!(from_str(r#" "" "#), Ok("".to_string()));
        assert_eq!(from_str(r#" " " "#), Ok(" ".to_string()));
        assert_eq!(from_str(r#" "👏" "#), Ok("👏".to_string()));
    }

    #[test]
    fn string() {
        assert_eq!(from_str(r#" "hello" "#), Ok(String::from("hello")));
        assert_eq!(from_str(r#" "" "#), Ok(String::from("")));
        assert_eq!(from_str(r#" " " "#), Ok(String::from(" ")));
        assert_eq!(from_str(r#" "👏" "#), Ok(String::from("👏")));

        // escaped " in the string content
        // (note: no unescaping is performed, as documented as a known issue in lib.rs)
        assert_eq!(from_str(r#" "foo\"bar" "#), Ok(String::from(r#"foo"bar"#)));
    }

    #[test]
    fn struct_bool() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Led {
            led: bool,
        }

        assert_eq!(from_str(r#"{ "led": true }"#), Ok(Led { led: true }));
        assert_eq!(from_str(r#"{ "led": false }"#), Ok(Led { led: false }));
    }

    #[test]
    fn struct_i8() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Temperature {
            temperature: i8,
        }

        assert_eq!(
            from_str(r#"{ "temperature": -17 }"#),
            Ok(Temperature { temperature: -17 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": -0 }"#),
            Ok(Temperature { temperature: -0 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": 0 }"#),
            Ok(Temperature { temperature: 0 })
        );

        // out of range
        assert!(from_str::<Temperature>(r#"{ "temperature": 128 }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": -129 }"#).is_err());
    }

    #[test]
    fn struct_f32() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Temperature {
            temperature: f32,
        }

        assert_eq!(
            from_str(r#"{ "temperature": -17.2 }"#),
            Ok(Temperature { temperature: -17.2 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": -0.0 }"#),
            Ok(Temperature { temperature: -0. })
        );

        assert_eq!(
            from_str(r#"{ "temperature": -2.1e-3 }"#),
            Ok(Temperature {
                temperature: -2.1e-3
            })
        );

        assert_eq!(
            from_str(r#"{ "temperature": -3 }"#),
            Ok(Temperature { temperature: -3. })
        );

        use core::f32;

        assert_eq!(
            from_str(r#"{ "temperature": -1e500 }"#),
            Ok(Temperature {
                temperature: f32::NEG_INFINITY
            })
        );

        // NaNs will always compare unequal.
        let r: Temperature = from_str(r#"{ "temperature": null }"#).unwrap();
        assert!(r.temperature.is_nan());

        assert!(from_str::<Temperature>(r#"{ "temperature": 1e1e1 }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": -2-2 }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": 1 1 }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": 0.0. }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": ä }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": None }"#).is_err());
    }

    #[test]
    fn struct_option() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Property {
            description: Option<String>,
        }

        assert_eq!(
            from_str(r#"{ "description": "An ambient temperature sensor" }"#),
            Ok(Property {
                description: Some("An ambient temperature sensor".to_string()),
            })
        );

        assert_eq!(
            from_str(r#"{ "description": null }"#),
            Ok(Property { description: None })
        );

        assert_eq!(from_str(r#"{}"#), Ok(Property { description: None }));
    }

    #[test]
    fn struct_u8() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Temperature {
            temperature: u8,
        }

        assert_eq!(
            from_str(r#"{ "temperature": 20 }"#),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": 0 }"#),
            Ok(Temperature { temperature: 0 })
        );

        // out of range
        assert!(from_str::<Temperature>(r#"{ "temperature": 256 }"#).is_err());
        assert!(from_str::<Temperature>(r#"{ "temperature": -1 }"#).is_err());
    }

    #[test]
    fn test_unit() {
        assert_eq!(from_str::<()>(r#"null"#), Ok(()));
    }

    #[test]
    fn newtype_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct A(pub u32);

        assert_eq!(from_str::<A>(r#"54"#), Ok(A(54)));
    }

    #[test]
    fn test_newtype_variant() {
        #[derive(Deserialize, Debug, PartialEq)]
        enum A {
            A(u32),
        }
        let a = A::A(54);
        let x = from_str::<A>(r#"{"A":54}"#);
        assert_eq!(x, Ok(a));
    }

    #[test]
    fn test_struct_variant() {
        #[derive(Deserialize, Debug, PartialEq)]
        enum A {
            A { x: u32, y: u16 },
        }
        let a = A::A { x: 54, y: 720 };
        let x = from_str::<A>(r#"{"A": {"x":54,"y":720 } }"#);
        assert_eq!(x, Ok(a));
    }

    #[test]
    fn struct_tuple() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Xy(i8, i8);

        assert_eq!(from_str(r#"[10, 20]"#), Ok(Xy(10, 20)));
        assert_eq!(from_str(r#"[10, -20]"#), Ok(Xy(10, -20)));

        // wrong number of args
        assert_eq!(
            from_str::<Xy>(r#"[10]"#),
            Err(crate::de::Error::Custom(String::from(
                "invalid length 1, expected tuple struct Xy with 2 elements"
            )))
        );
        assert_eq!(
            from_str::<Xy>(r#"[10, 20, 30]"#),
            Err(crate::de::Error::TrailingCharacters)
        );
    }

    #[test]
    fn struct_with_array_field() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Test {
            status: bool,
            point: [u32; 3],
        }

        assert_eq!(
            from_str(r#"{ "status": true, "point": [1, 2, 3] }"#),
            Ok(Test {
                status: true,
                point: [1, 2, 3]
            })
        );
    }

    #[test]
    fn struct_with_tuple_field() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Test {
            status: bool,
            point: (u32, u32, u32),
        }

        assert_eq!(
            from_str(r#"{ "status": true, "point": [1, 2, 3] }"#),
            Ok(Test {
                status: true,
                point: (1, 2, 3)
            })
        );

        #[derive(Debug, Deserialize, PartialEq)]
        struct Xy(i8, i8);

        match from_str::<Xy>(r#"[10]"#) {
            Err(super::Error::Custom(_)) => {}
            _ => panic!("expect custom error"),
        }
        assert_eq!(
            from_str::<Xy>(r#"[10, 20, 30]"#),
            Err(crate::de::Error::TrailingCharacters)
        );
    }

    #[test]
    fn struct_empty() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Empty {}

        assert_eq!(from_str(r#"{}"#), Ok(Empty {}));
        assert_eq!(serde_json::from_str::<Empty>(r#"{}"#).unwrap(), Empty {});
    }

    #[test]
    fn struct_nothing() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Nothing;

        assert_eq!(from_str(r#"null"#), Ok(Nothing));
        assert_eq!(serde_json::from_str::<Nothing>(r#"null"#).unwrap(), Nothing);
    }

    #[test]
    fn ignoring_extra_fields() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Temperature {
            temperature: u8,
        }

        assert_eq!(
            from_str(r#"{ "temperature": 20, "high": 80, "low": -10, "updated": true }"#),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": 20, "conditions": "windy", "forecast": "cloudy" }"#),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": 20, "hourly_conditions": ["windy", "rainy"] }"#),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str(
                r#"{ "temperature": 20, "source": { "station": "dock", "sensors": ["front", "back"] } }"#
            ),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str(r#"{ "temperature": 20, "invalid": this-is-ignored }"#),
            Ok(Temperature { temperature: 20 })
        );

        assert_eq!(
            from_str::<Temperature>(r#"{ "temperature": 20, "broken": }"#),
            Err(crate::de::Error::ExpectedSomeValue)
        );

        assert_eq!(
            from_str::<Temperature>(r#"{ "temperature": 20, "broken": [ }"#),
            Err(crate::de::Error::ExpectedSomeValue)
        );

        assert_eq!(
            from_str::<Temperature>(r#"{ "temperature": 20, "broken": ] }"#),
            Err(crate::de::Error::ExpectedSomeValue)
        );
    }

    #[test]
    fn newtypes() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Address(String);

        #[derive(Deserialize, Debug, PartialEq)]
        struct CommentId(u32);

        #[derive(Deserialize, Debug, PartialEq)]
        struct NewtypeDemo {
            address: Address,
            comment: CommentId,
        }

        let element: Address = from_str(r#""johnny""#).unwrap();
        assert_eq!(element, Address("johnny".to_string()));

        let element: CommentId = from_str(r#"5464813"#).unwrap();
        assert_eq!(element, CommentId(5464813));

        let element: NewtypeDemo = from_str(r#"{"address": "johnny", "comment": 9897}"#).unwrap();
        assert_eq!(
            element,
            NewtypeDemo {
                address: Address("johnny".to_string()),
                comment: CommentId(9897),
            }
        );
    }

    #[test]
    fn deserialize_optional_vector() {
        #[derive(Debug, Deserialize, PartialEq)]
        pub struct Response {
            pub log: Option<String>,
            pub messages: Vec<Msg>,
        }

        #[derive(Debug, Deserialize, PartialEq, serde_derive::Serialize)]
        pub struct Msg {
            pub name: String,
        }

        #[derive(Debug, Deserialize, PartialEq)]
        pub struct OptIn {
            pub name: Option<String>,
        }

        let m: Msg = from_str(
            r#"{
          "name": "one"
        }"#,
        )
        .expect("simple");
        assert_eq!(
            m,
            Msg {
                name: "one".to_string()
            }
        );

        let o: OptIn = from_str(
            r#"{
          "name": "two"
        }"#,
        )
        .expect("opt");
        assert_eq!(
            o,
            OptIn {
                name: Some("two".to_string())
            }
        );

        let res: Response = from_str(
            r#"{
          "log": "my log",
          "messages": [{"name": "one"}]
        }"#,
        )
        .expect("fud");
        assert_eq!(
            res,
            Response {
                log: Some("my log".to_string()),
                messages: vec![Msg {
                    name: "one".to_string()
                }],
            }
        );

        let res: Response = from_str(r#"{"log": null,"messages": []}"#).expect("fud");
        assert_eq!(
            res,
            Response {
                log: None,
                messages: Vec::new()
            }
        );
    }

    #[test]
    fn deserialize_embedded_enum() {
        #[derive(Debug, Deserialize, PartialEq)]
        #[serde(rename_all = "lowercase")]
        pub enum MyResult {
            Ok(Response),
            Err(String),
        }

        #[derive(Debug, Deserialize, PartialEq)]
        pub struct Response {
            pub log: Option<String>,
            pub messages: Vec<Msg>,
        }

        #[derive(Debug, Deserialize, PartialEq)]
        pub struct Msg {
            pub name: String,
            pub amount: Option<String>,
        }

        let res: MyResult = from_str(
            r#"{
                "ok": {
                    "log": "hello",
                    "messages": [{
                        "name": "fred",
                        "amount": "15"
                    }]
                }
            }"#,
        )
        .expect("goo");
        assert_eq!(
            res,
            MyResult::Ok(Response {
                log: Some("hello".to_string()),
                messages: vec![Msg {
                    name: "fred".to_string(),
                    amount: Some("15".to_string())
                }]
            })
        );

        let res: MyResult = from_str(
            r#"{
          "ok": {
            "log": "hello",
            "messages": []
          }
        }"#,
        )
        .expect("goo");
        assert_eq!(
            res,
            MyResult::Ok(Response {
                log: Some("hello".to_string()),
                messages: Vec::new()
            })
        );

        let res: MyResult = from_str(
            r#"{
          "ok": {
            "log": null,
            "messages": []
          }
        }"#,
        )
        .expect("goo");
        assert_eq!(
            res,
            MyResult::Ok(Response {
                log: None,
                messages: Vec::new()
            })
        );
    }

    #[test]
    fn preserve_short_error_message() {
        use serde::de::Error;
        assert_eq!(
            crate::de::Error::custom("something bad happened"),
            crate::de::Error::Custom(String::from("something bad happened"))
        );
    }

    // See https://iot.mozilla.org/wot/#thing-resource
    #[test]
    fn wot() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Thing {
            properties: Properties,
            #[serde(rename = "type")]
            ty: Type,
        }

        #[derive(Debug, Deserialize, PartialEq)]
        struct Properties {
            temperature: Property,
            humidity: Property,
            led: Property,
        }

        #[derive(Debug, Deserialize, PartialEq)]
        struct Property {
            #[serde(rename = "type")]
            ty: Type,
            unit: Option<String>,
            description: Option<String>,
            href: String,
        }

        assert_eq!(
            from_str::<Thing>(
                r#"
                    {
                        "type": "thing",
                        "properties": {
                            "temperature": {
                                "type": "number",
                                "unit": "celsius",
                                "description": "An ambient temperature sensor",
                                "href": "/properties/temperature",
                                "owned": "own temperature"
                            },
                            "humidity": {
                                "type": "number",
                                "unit": "percent",
                                "href": "/properties/humidity",
                                "owned": null
                            },
                            "led": {
                                "type": "boolean",
                                "unit": null,
                                "description": "A red LED",
                                "href": "/properties/led",
                                "owned": "own led"
                            }
                        }
                    }
                "#
            ),
            Ok(Thing {
                properties: Properties {
                    temperature: Property {
                        ty: Type::Number,
                        unit: Some("celsius".to_string()),
                        description: Some("An ambient temperature sensor".to_string()),
                        href: "/properties/temperature".to_string(),
                    },
                    humidity: Property {
                        ty: Type::Number,
                        unit: Some("percent".to_string()),
                        description: None,
                        href: "/properties/humidity".to_string(),
                    },
                    led: Property {
                        ty: Type::Boolean,
                        unit: None,
                        description: Some("A red LED".to_string()),
                        href: "/properties/led".to_string(),
                    },
                },
                ty: Type::Thing,
            })
        )
    }
}
