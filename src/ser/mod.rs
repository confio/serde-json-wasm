//! Serialize a Rust data structure into JSON data

use std::{error, fmt, str};

use serde::ser;
use serde::ser::SerializeStruct as _;
use serde::Serialize;

use std::vec::Vec;

use self::map::SerializeMap;
use self::seq::SerializeSeq;
use self::struct_::{SerializeStruct, SerializeStructVariant};

mod map;
mod seq;
mod struct_;

/// Serialization result
pub type Result<T> = ::core::result::Result<T, Error>;

/// This type represents all possible errors that can occur when serializing JSON data
#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[non_exhaustive]
pub enum Error {
    /// Buffer is full
    BufferFull,

    /// Custom error message from serde
    Custom(String),
}

impl From<()> for Error {
    fn from(_: ()) -> Error {
        Error::BufferFull
    }
}

impl From<u8> for Error {
    fn from(_: u8) -> Error {
        Error::BufferFull
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        "(use display)"
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::BufferFull => write!(f, "Buffer is full"),
            Error::Custom(msg) => write!(f, "{}", &msg),
        }
    }
}

/// A structure that serializes Rust values as JSON into a buffer.
pub struct Serializer {
    buf: Vec<u8>,
}

/// Number of bytes reserved by default for the output JSON
static INITIAL_CAPACITY: usize = 1024;

impl Serializer {
    /// Create a new `Serializer`
    fn new() -> Self {
        Serializer {
            buf: Vec::with_capacity(INITIAL_CAPACITY),
        }
    }

    pub(crate) fn push(&mut self, c: u8) -> Result<()> {
        self.buf.push(c);
        Ok(())
    }

    fn extend_from_slice(&mut self, other: &[u8]) -> Result<()> {
        self.buf.extend_from_slice(other);
        Ok(())
    }

    fn push_char(&mut self, c: char) -> Result<()> {
        // Do escaping according to "6. MUST represent all strings (including object member names) in
        // their minimal-length UTF-8 encoding": https://gibson042.github.io/canonicaljson-spec/
        //
        // We don't need to escape lone surrogates because surrogate pairs do not exist in valid UTF-8,
        // even if they can exist in JSON or JavaScript strings (UCS-2 based). As a result, lone surrogates
        // cannot exist in a Rust String. If they do, the bug is in the String constructor.
        // An excellent explanation is available at https://www.youtube.com/watch?v=HhIEDWmQS3w

        // Temporary storage for encoded a single char.
        // A char is up to 4 bytes long when encoded to UTF-8.
        let mut encoding_tmp = [0u8; 4];

        match c {
            '\\' => {
                self.push(b'\\')?;
                self.push(b'\\')?;
            }
            '"' => {
                self.push(b'\\')?;
                self.push(b'"')?;
            }
            '\u{0008}' => {
                self.push(b'\\')?;
                self.push(b'b')?;
            }
            '\u{0009}' => {
                self.push(b'\\')?;
                self.push(b't')?;
            }
            '\u{000A}' => {
                self.push(b'\\')?;
                self.push(b'n')?;
            }
            '\u{000C}' => {
                self.push(b'\\')?;
                self.push(b'f')?;
            }
            '\u{000D}' => {
                self.push(b'\\')?;
                self.push(b'r')?;
            }
            '\u{0000}'..='\u{001F}' => {
                self.push(b'\\')?;
                self.push(b'u')?;
                self.push(b'0')?;
                self.push(b'0')?;
                let (hex1, hex2) = hex(c as u8);
                self.push(hex1)?;
                self.push(hex2)?;
            }
            _ => {
                let encoded = c.encode_utf8(&mut encoding_tmp as &mut [u8]);
                self.extend_from_slice(encoded.as_bytes())?;
            }
        }

        Ok(())
    }
}

// NOTE(serialize_*signed) This is basically the numtoa implementation minus the lookup tables,
// which take 200+ bytes of ROM / Flash
macro_rules! serialize_unsigned {
    ($self:ident, $N:expr, $v:expr) => {{
        let mut buf: [core::mem::MaybeUninit<u8>; $N] = [core::mem::MaybeUninit::uninit(); $N];

        let mut v = $v;
        let mut i = $N - 1;
        loop {
            buf[i].write((v % 10) as u8 + b'0');
            v /= 10;

            if v == 0 {
                break;
            } else {
                i -= 1;
            }
        }

        // Note(feature): maybe_uninit_slice
        let buf = unsafe { &*(&buf[i..] as *const _ as *const [u8]) };

        $self.extend_from_slice(buf)
    }};
}
// Export for use in map
pub(crate) use serialize_unsigned;

macro_rules! serialize_signed {
    ($self:ident, $N:expr, $v:expr, $ixx:ident, $uxx:ident) => {{
        let v = $v;
        let (signed, mut v) = if v == $ixx::MIN {
            (true, $ixx::MAX as $uxx + 1)
        } else if v < 0 {
            (true, -v as $uxx)
        } else {
            (false, v as $uxx)
        };

        let mut buf: [core::mem::MaybeUninit<u8>; $N] = [core::mem::MaybeUninit::uninit(); $N];
        let mut i = $N - 1;
        loop {
            buf[i].write((v % 10) as u8 + b'0');
            v /= 10;

            i -= 1;

            if v == 0 {
                break;
            }
        }

        if signed {
            buf[i].write(b'-');
        } else {
            i += 1;
        }

        // Note(feature): maybe_uninit_slice
        let buf = unsafe { &*(&buf[i..] as *const _ as *const [u8]) };

        $self.extend_from_slice(buf)
    }};
}

macro_rules! serialize_ryu {
    ($self:ident, $v:expr) => {{
        let mut buffer = ryu::Buffer::new();
        let printed = buffer.format($v);
        $self.extend_from_slice(printed.as_bytes())
    }};
}
// Export for use in map
pub(crate) use serialize_signed;

/// Upper-case hex for value in 0..16, encoded as ASCII bytes
fn hex_4bit(c: u8) -> u8 {
    if c <= 9 {
        0x30 + c
    } else {
        0x41 + (c - 10)
    }
}

/// Upper-case hex for value in 0..256, encoded as ASCII bytes
fn hex(c: u8) -> (u8, u8) {
    (hex_4bit(c >> 4), hex_4bit(c & 0x0F))
}

impl<'a> ser::Serializer for &'a mut Serializer {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = SerializeSeq<'a>;
    type SerializeTuple = SerializeSeq<'a>;
    type SerializeTupleStruct = SerializeSeq<'a>;
    type SerializeTupleVariant = SerializeSeq<'a>;
    type SerializeMap = SerializeMap<'a>;
    type SerializeStruct = SerializeStruct<'a>;
    type SerializeStructVariant = SerializeStructVariant<'a>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok> {
        if v {
            self.extend_from_slice(b"true")
        } else {
            self.extend_from_slice(b"false")
        }
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok> {
        // -128
        serialize_signed!(self, 4, v, i8, u8)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok> {
        // -32768
        serialize_signed!(self, 6, v, i16, u16)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok> {
        // -2147483648
        serialize_signed!(self, 11, v, i32, u32)
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok> {
        // -9223372036854775808
        serialize_signed!(self, 20, v, i64, u64)
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok> {
        // -170141183460469231731687303715884105728
        serialize_signed!(self, 40, v, i128, u128)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok> {
        // 255
        serialize_unsigned!(self, 3, v)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok> {
        // 65535
        serialize_unsigned!(self, 5, v)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok> {
        // 4294967295
        serialize_unsigned!(self, 10, v)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok> {
        // 18446744073709551615
        serialize_unsigned!(self, 20, v)
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok> {
        // 340282366920938463463374607431768211455
        serialize_unsigned!(self, 39, v)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok> {
        if v.is_finite() {
            serialize_ryu!(self, v)
        } else {
            self.serialize_none()
        }
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok> {
        if v.is_finite() {
            serialize_ryu!(self, v)
        } else {
            self.serialize_none()
        }
    }

    fn serialize_char(self, _v: char) -> Result<Self::Ok> {
        unreachable!()
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok> {
        self.push(b'"')?;

        for c in v.chars() {
            self.push_char(c)?;
        }

        self.push(b'"')
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok> {
        self.extend_from_slice(v)
    }

    fn serialize_none(self) -> Result<Self::Ok> {
        self.extend_from_slice(b"null")
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok>
    where
        T: ser::Serialize + ?Sized,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok> {
        // The unit type is a zero element tuple, so the consistent way to serialize this would be "[]".
        // However, for compatibility with serde_json we serialize to "null".
        self.serialize_none()
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok> {
        // Unit struct is serialized to (serde_json compatible) "null"
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<Self::Ok>
    where
        T: ser::Serialize + ?Sized,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok>
    where
        T: ser::Serialize + ?Sized,
    {
        self.push(b'{')?;
        let mut s = SerializeStruct::new(self);
        s.serialize_field(variant, value)?;
        s.end()?;
        Ok(())
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        self.push(b'[')?;

        Ok(SerializeSeq::new(self))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple> {
        self.serialize_seq(Some(_len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        self.buf.push(b'{');
        self.serialize_str(variant)?;
        self.buf.push(b':');
        self.serialize_tuple(len)
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap> {
        self.push(b'{')?;

        Ok(SerializeMap::new(self))
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeStruct> {
        self.push(b'{')?;

        Ok(SerializeStruct::new(self))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        self.extend_from_slice(b"{\"")?;
        self.extend_from_slice(variant.as_bytes())?;
        self.extend_from_slice(b"\":{")?;

        Ok(SerializeStructVariant::new(self))
    }

    fn collect_str<T>(self, value: &T) -> Result<Self::Ok>
    where
        T: fmt::Display + ?Sized,
    {
        self.serialize_str(&value.to_string())
    }
}

/// Serializes the given data structure as a string of JSON text
pub fn to_string<T>(value: &T) -> Result<String>
where
    T: ser::Serialize + ?Sized,
{
    Ok(unsafe { String::from_utf8_unchecked(to_vec::<T>(value)?) })
}

/// Serializes the given data structure as a JSON byte vector
pub fn to_vec<T>(value: &T) -> Result<Vec<u8>>
where
    T: ser::Serialize + ?Sized,
{
    let mut ser = Serializer::new();
    value.serialize(&mut ser)?;
    Ok(ser.buf)
}

impl ser::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error::Custom(msg.to_string())
    }
}

#[cfg(test)]
mod tests {

    use super::to_string;
    use serde::{Deserialize, Serialize, Serializer};

    #[macro_export]
    macro_rules! assert_serde_json_serialize_eq {
        ($target:expr,) => {
            assert_serde_json_serialize_eq!($target);
        };
        ($target:expr) => {
            assert_eq!(
                $crate::to_string($target).unwrap(),
                ::serde_json::to_string($target).unwrap(),
                "Serialization does not match serde_json"
            );
        };
    }

    #[test]
    fn number() {
        assert_eq!(to_string::<u8>(&0).unwrap(), "0");
        assert_eq!(to_string::<u8>(&1).unwrap(), "1");
        assert_eq!(to_string::<u8>(&u8::MAX).unwrap(), "255");

        assert_eq!(to_string::<i8>(&0).unwrap(), "0");
        assert_eq!(to_string::<i8>(&1).unwrap(), "1");
        assert_eq!(to_string::<i8>(&127).unwrap(), "127");
        assert_eq!(to_string::<i8>(&-1).unwrap(), "-1");
        assert_eq!(to_string::<i8>(&i8::MIN).unwrap(), "-128");

        assert_eq!(to_string::<u16>(&0).unwrap(), "0");
        assert_eq!(to_string::<u16>(&1).unwrap(), "1");
        assert_eq!(to_string::<u16>(&550).unwrap(), "550");
        assert_eq!(to_string::<u16>(&u16::MAX).unwrap(), "65535");

        assert_eq!(to_string::<i16>(&0).unwrap(), "0");
        assert_eq!(to_string::<i16>(&1).unwrap(), "1");
        assert_eq!(to_string::<i16>(&550).unwrap(), "550");
        assert_eq!(to_string::<i16>(&i16::MAX).unwrap(), "32767");
        assert_eq!(to_string::<i16>(&-1).unwrap(), "-1");
        assert_eq!(to_string::<i16>(&i16::MIN).unwrap(), "-32768");

        assert_eq!(to_string::<u32>(&0).unwrap(), "0");
        assert_eq!(to_string::<u32>(&1).unwrap(), "1");
        assert_eq!(to_string::<u32>(&456789).unwrap(), "456789");
        assert_eq!(to_string::<u32>(&u32::MAX).unwrap(), "4294967295");

        assert_eq!(to_string::<i32>(&0).unwrap(), "0");
        assert_eq!(to_string::<i32>(&1).unwrap(), "1");
        assert_eq!(to_string::<i32>(&456789).unwrap(), "456789");
        assert_eq!(to_string::<i32>(&i32::MAX).unwrap(), "2147483647");
        assert_eq!(to_string::<i32>(&-1).unwrap(), "-1");
        assert_eq!(to_string::<i32>(&i32::MIN).unwrap(), "-2147483648");

        assert_eq!(to_string::<u64>(&0).unwrap(), "0");
        assert_eq!(to_string::<u64>(&1).unwrap(), "1");
        assert_eq!(to_string::<u64>(&456789).unwrap(), "456789");
        assert_eq!(to_string::<u64>(&4294967295).unwrap(), "4294967295");
        assert_eq!(to_string::<u64>(&4294967296).unwrap(), "4294967296");
        assert_eq!(
            to_string::<u64>(&9007199254740991).unwrap(),
            "9007199254740991"
        ); // Number.MAX_SAFE_INTEGER
        assert_eq!(
            to_string::<u64>(&9007199254740992).unwrap(),
            "9007199254740992"
        ); // Number.MAX_SAFE_INTEGER+1
        assert_eq!(to_string::<u64>(&u64::MAX).unwrap(), "18446744073709551615");

        assert_eq!(to_string::<i64>(&0).unwrap(), "0");
        assert_eq!(to_string::<i64>(&1).unwrap(), "1");
        assert_eq!(to_string::<i64>(&456789).unwrap(), "456789");
        assert_eq!(to_string::<i64>(&4294967295).unwrap(), "4294967295");
        assert_eq!(to_string::<i64>(&4294967296).unwrap(), "4294967296");
        assert_eq!(
            to_string::<i64>(&9007199254740991).unwrap(),
            "9007199254740991"
        ); // Number.MAX_SAFE_INTEGER
        assert_eq!(
            to_string::<i64>(&9007199254740992).unwrap(),
            "9007199254740992"
        ); // Number.MAX_SAFE_INTEGER+1
        assert_eq!(to_string::<i64>(&i64::MAX).unwrap(), "9223372036854775807");
        assert_eq!(to_string::<i64>(&-1).unwrap(), "-1");
        assert_eq!(to_string::<i64>(&i64::MIN).unwrap(), "-9223372036854775808");

        assert_eq!(to_string::<u128>(&0).unwrap(), r#"0"#);
        assert_eq!(to_string::<u128>(&1).unwrap(), r#"1"#);
        assert_eq!(to_string::<u128>(&456789).unwrap(), r#"456789"#);
        assert_eq!(to_string::<u128>(&4294967295).unwrap(), r#"4294967295"#);
        assert_eq!(to_string::<u128>(&4294967296).unwrap(), r#"4294967296"#);
        assert_eq!(
            to_string::<u128>(&9007199254740991).unwrap(),
            r#"9007199254740991"#
        ); // Number.MAX_SAFE_INTEGER
        assert_eq!(
            to_string::<u128>(&9007199254740992).unwrap(),
            r#"9007199254740992"#
        ); // Number.MAX_SAFE_INTEGER+1
        assert_eq!(
            to_string::<u128>(&9223372036854775807).unwrap(),
            r#"9223372036854775807"#
        );
        assert_eq!(
            to_string::<u128>(&9223372036854775808).unwrap(),
            r#"9223372036854775808"#
        );
        assert_eq!(
            to_string::<u128>(&u128::MAX).unwrap(),
            r#"340282366920938463463374607431768211455"#
        );
        assert_serde_json_serialize_eq!(&u128::MAX);

        assert_eq!(to_string::<i128>(&0).unwrap(), r#"0"#);
        assert_eq!(to_string::<i128>(&1).unwrap(), r#"1"#);
        assert_eq!(to_string::<i128>(&456789).unwrap(), r#"456789"#);
        assert_eq!(to_string::<i128>(&4294967295).unwrap(), r#"4294967295"#);
        assert_eq!(to_string::<i128>(&4294967296).unwrap(), r#"4294967296"#);
        assert_eq!(
            to_string::<i128>(&9007199254740991).unwrap(),
            r#"9007199254740991"#
        ); // Number.MAX_SAFE_INTEGER
        assert_eq!(
            to_string::<i128>(&9007199254740992).unwrap(),
            r#"9007199254740992"#
        ); // Number.MAX_SAFE_INTEGER+1
        assert_eq!(
            to_string::<i128>(&9223372036854775807).unwrap(),
            r#"9223372036854775807"#
        );
        assert_eq!(
            to_string::<i128>(&9223372036854775808).unwrap(),
            r#"9223372036854775808"#
        );
        assert_eq!(
            to_string::<i128>(&i128::MAX).unwrap(),
            r#"170141183460469231731687303715884105727"#
        );
        assert_eq!(to_string::<i128>(&-1).unwrap(), r#"-1"#);
        assert_eq!(
            to_string::<i128>(&i128::MIN).unwrap(),
            r#"-170141183460469231731687303715884105728"#
        );
        assert_serde_json_serialize_eq!(&i128::MIN);
    }

    #[test]
    fn array() {
        let vec = crate::to_vec(&[0, 1, 2]).unwrap();
        assert_eq!(vec.len(), 7);
        assert_eq!(&vec[..], b"[0,1,2]");
        assert_eq!(to_string::<[u8]>(&[]).unwrap(), "[]");
        assert_eq!(to_string(&[0, 1, 2]).unwrap(), "[0,1,2]");
    }

    #[test]
    fn bool() {
        let vec = crate::to_vec(&true).unwrap();
        assert_eq!(vec.len(), 4);
        assert_eq!(&vec[..], b"true");

        assert_eq!(to_string(&true).unwrap(), "true");
        assert_eq!(to_string(&false).unwrap(), "false");
    }

    #[test]
    fn tuple() {
        type Pair = (i64, i64);
        type Wrapped = (i64,); // Comma differentiates one element tuple from a primary type surrounded by parentheses
        type Unit = ();

        let pair: Pair = (1, 2);
        assert_eq!(to_string(&pair).unwrap(), "[1,2]");
        assert_serde_json_serialize_eq!(&pair);

        let wrapped: Wrapped = (5,);
        assert_eq!(to_string(&wrapped).unwrap(), "[5]");
        assert_serde_json_serialize_eq!(&wrapped);

        #[allow(clippy::let_unit_value)]
        let unit: Unit = ();
        assert_eq!(to_string(&unit).unwrap(), "null");
        assert_serde_json_serialize_eq!(&unit);

        type BigPair = (u128, u128);

        let pair: BigPair = (u128::MAX, u128::MAX);

        assert_eq!(
            to_string(&pair).unwrap(),
            r#"[340282366920938463463374607431768211455,340282366920938463463374607431768211455]"#
        );
        assert_serde_json_serialize_eq!(&pair);
    }

    #[test]
    fn enum_variants_unit_like() {
        #[allow(dead_code)]
        #[derive(Serialize)]
        enum Op {
            Enter,
            Exit,
        }
        assert_eq!(to_string(&Op::Exit).unwrap(), r#""Exit""#);
        assert_serde_json_serialize_eq!(&Op::Exit);

        // Numeric values are ignored 🤷
        #[derive(Serialize)]
        enum Order {
            Unordered = 1,
            Ordered = 42,
        }
        assert_eq!(to_string(&Order::Unordered).unwrap(), r#""Unordered""#);
        assert_serde_json_serialize_eq!(&Order::Unordered);

        assert_eq!(to_string(&Order::Ordered).unwrap(), r#""Ordered""#);
        assert_serde_json_serialize_eq!(&Order::Ordered);
    }

    #[test]
    fn enum_variants_tuple_like_structs() {
        #[derive(Serialize)]
        enum Op {
            Exit(),
            Square(i32),
            Add(i64, i64),
        }
        assert_eq!(to_string(&Op::Exit()).unwrap(), r#"{"Exit":[]}"#);
        assert_serde_json_serialize_eq!(&Op::Exit());

        assert_eq!(to_string(&Op::Square(2)).unwrap(), r#"{"Square":2}"#);
        assert_serde_json_serialize_eq!(&Op::Square(2));

        assert_eq!(to_string(&Op::Add(3, 4)).unwrap(), r#"{"Add":[3,4]}"#);
        assert_serde_json_serialize_eq!(&Op::Add(3, 4));
    }

    #[test]
    fn enum_variants_c_like_structs() {
        #[derive(Serialize)]
        enum Op {
            Exit {},
            Square { input: i32 },
            Add { a: i64, b: i64 },
        }
        assert_eq!(to_string(&Op::Exit {}).unwrap(), r#"{"Exit":{}}"#);
        assert_serde_json_serialize_eq!(&Op::Exit {});

        assert_eq!(
            to_string(&Op::Square { input: 2 }).unwrap(),
            r#"{"Square":{"input":2}}"#
        );
        assert_serde_json_serialize_eq!(&Op::Square { input: 2 });

        assert_eq!(
            to_string(&Op::Add { a: 3, b: 4 }).unwrap(),
            r#"{"Add":{"a":3,"b":4}}"#
        );
        assert_serde_json_serialize_eq!(&Op::Add { a: 3, b: 4 });
    }

    #[test]
    fn enum_mixed() {
        #[derive(Serialize)]
        enum Animal {
            Ant,
            #[serde(rename = "kitty")]
            Cat,
            Dog(),
            Horse {},
            Zebra {
                height: u32,
            },
        }
        assert_eq!(to_string(&Animal::Ant).unwrap(), r#""Ant""#);
        assert_eq!(to_string(&Animal::Cat).unwrap(), r#""kitty""#);
        assert_eq!(to_string(&Animal::Dog()).unwrap(), r#"{"Dog":[]}"#);
        assert_eq!(to_string(&Animal::Horse {}).unwrap(), r#"{"Horse":{}}"#);
        assert_eq!(
            to_string(&Animal::Zebra { height: 273 }).unwrap(),
            r#"{"Zebra":{"height":273}}"#
        );
    }

    #[test]
    fn str() {
        assert_eq!(to_string("hello").unwrap(), r#""hello""#);
        assert_eq!(to_string("").unwrap(), r#""""#);

        // Characters unescaped if possible
        assert_eq!(to_string("ä").unwrap(), r#""ä""#);
        assert_eq!(to_string("৬").unwrap(), r#""৬""#);
        // assert_eq!(to_string("\u{A0}").unwrap(), r#"" ""#); // non-breaking space
        assert_eq!(to_string("ℝ").unwrap(), r#""ℝ""#); // 3 byte character
        assert_eq!(to_string("💣").unwrap(), r#""💣""#); // 4 byte character

        // " and \ must be escaped
        assert_eq!(&*crate::to_string("foo\"bar").unwrap(), r#""foo\"bar""#);
        assert_eq!(&*crate::to_string("foo\\bar").unwrap(), r#""foo\\bar""#);

        // \b, \t, \n, \f, \r must be escaped in their two-character escaping
        assert_eq!(&*crate::to_string(" \u{0008} ").unwrap(), r#"" \b ""#);
        assert_eq!(&*crate::to_string(" \u{0009} ").unwrap(), r#"" \t ""#);
        assert_eq!(&*crate::to_string(" \u{000A} ").unwrap(), r#"" \n ""#);
        assert_eq!(&*crate::to_string(" \u{000C} ").unwrap(), r#"" \f ""#);
        assert_eq!(&*crate::to_string(" \u{000D} ").unwrap(), r#"" \r ""#);

        // U+0000 through U+001F is escaped using six-character \u00xx uppercase hexadecimal escape sequences
        assert_eq!(&*crate::to_string(" \u{0000} ").unwrap(), r#"" \u0000 ""#);
        assert_eq!(&*crate::to_string(" \u{0001} ").unwrap(), r#"" \u0001 ""#);
        assert_eq!(&*crate::to_string(" \u{0007} ").unwrap(), r#"" \u0007 ""#);
        assert_eq!(&*crate::to_string(" \u{000e} ").unwrap(), r#"" \u000E ""#);
        assert_eq!(&*crate::to_string(" \u{001D} ").unwrap(), r#"" \u001D ""#);
        assert_eq!(&*crate::to_string(" \u{001f} ").unwrap(), r#"" \u001F ""#);
        assert_eq!(&*crate::to_string("").unwrap(), r#""""#);

        // " and \ must be escaped
        assert_eq!(to_string("foo\"bar").unwrap(), r#""foo\"bar""#);
        assert_eq!(to_string("foo\\bar").unwrap(), r#""foo\\bar""#);

        // \b, \t, \n, \f, \r must be escaped in their two-character escaping
        assert_eq!(to_string(" \u{0008} ").unwrap(), r#"" \b ""#);
        assert_eq!(to_string(" \u{0009} ").unwrap(), r#"" \t ""#);
        assert_eq!(to_string(" \u{000A} ").unwrap(), r#"" \n ""#);
        assert_eq!(to_string(" \u{000C} ").unwrap(), r#"" \f ""#);
        assert_eq!(to_string(" \u{000D} ").unwrap(), r#"" \r ""#);

        // U+0000 through U+001F is escaped using six-character \u00xx uppercase hexadecimal escape sequences
        assert_eq!(to_string(" \u{0000} ").unwrap(), r#"" \u0000 ""#);
        assert_eq!(to_string(" \u{0001} ").unwrap(), r#"" \u0001 ""#);
        assert_eq!(to_string(" \u{0007} ").unwrap(), r#"" \u0007 ""#);
        assert_eq!(to_string(" \u{000e} ").unwrap(), r#"" \u000E ""#);
        assert_eq!(to_string(" \u{001D} ").unwrap(), r#"" \u001D ""#);
        assert_eq!(to_string(" \u{001f} ").unwrap(), r#"" \u001F ""#);
    }

    #[test]
    fn collect_str_can_be_used_in_custom_seralize_impl() {
        struct SpecialType {
            count: u32,
            on: bool,
        }

        impl Serialize for SpecialType {
            // A custom Serialize implementation for SpecialType. SpecialType is giving us the chance to use
            // an efficient collect_str implementation that is better than allocating the String and running
            // serialize_str on it.
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.collect_str(&format_args!("{}-{}", self.count, self.on))
            }
        }

        let value = SpecialType {
            count: 123,
            on: false,
        };
        assert_eq!(to_string(&value).unwrap(), r#""123-false""#);
    }

    #[test]
    fn newtype() {
        #[derive(Serialize)]
        struct Address(String);
        #[derive(Serialize)]
        struct CommentId(u32);

        // string
        assert_eq!(
            to_string(&Address("home".to_string())).unwrap(),
            r#""home""#
        );
        assert_serde_json_serialize_eq!(&Address("home".to_string()));

        // number
        assert_eq!(to_string(&CommentId(42)).unwrap(), r#"42"#);
        assert_serde_json_serialize_eq!(&CommentId(42));
    }

    #[test]
    fn struct_bool() {
        #[derive(Serialize)]
        struct Led {
            led: bool,
        }

        assert_eq!(to_string(&Led { led: true }).unwrap(), r#"{"led":true}"#);
        assert_serde_json_serialize_eq!(&Led { led: true });
    }

    #[test]
    fn struct_i8() {
        #[derive(Serialize)]
        struct Temperature {
            temperature: i8,
        }

        assert_eq!(
            to_string(&Temperature { temperature: 127 }).unwrap(),
            r#"{"temperature":127}"#
        );
        assert_eq!(
            to_string(&Temperature { temperature: 20 }).unwrap(),
            r#"{"temperature":20}"#
        );
        assert_eq!(
            to_string(&Temperature { temperature: -17 }).unwrap(),
            r#"{"temperature":-17}"#
        );
        assert_eq!(
            to_string(&Temperature { temperature: -128 }).unwrap(),
            r#"{"temperature":-128}"#
        );
        assert_serde_json_serialize_eq!(&Temperature { temperature: -128 });
    }

    #[test]
    fn struct_f32() {
        #[derive(Serialize)]
        struct Temperature {
            temperature: f32,
        }

        assert_eq!(
            &*crate::to_string(&Temperature { temperature: -20. }).unwrap(),
            r#"{"temperature":-20.0}"#
        );

        assert_eq!(
            &*crate::to_string(&Temperature {
                temperature: -20345.
            })
            .unwrap(),
            r#"{"temperature":-20345.0}"#
        );

        assert_eq!(
            &*crate::to_string(&Temperature {
                temperature: -2.345_678_8e-23
            })
            .unwrap(),
            r#"{"temperature":-2.3456788e-23}"#
        );

        assert_eq!(
            &*crate::to_string(&Temperature {
                temperature: f32::NAN
            })
            .unwrap(),
            r#"{"temperature":null}"#
        );

        assert_eq!(
            &*crate::to_string(&Temperature {
                temperature: f32::NEG_INFINITY
            })
            .unwrap(),
            r#"{"temperature":null}"#
        );
    }

    #[test]
    fn struct_option() {
        #[derive(Serialize)]
        struct Property<'a> {
            description: Option<&'a str>,
        }

        assert_eq!(
            to_string(&Property {
                description: Some("An ambient temperature sensor"),
            })
            .unwrap(),
            r#"{"description":"An ambient temperature sensor"}"#
        );
        assert_serde_json_serialize_eq!(&Property {
            description: Some("An ambient temperature sensor"),
        });

        assert_eq!(
            to_string(&Property { description: None }).unwrap(),
            r#"{"description":null}"#
        );
        assert_serde_json_serialize_eq!(&Property { description: None });
    }

    #[test]
    fn struct_u8() {
        #[derive(Serialize)]
        struct Temperature {
            temperature: u8,
        }

        assert_eq!(
            to_string(&Temperature { temperature: 20 }).unwrap(),
            r#"{"temperature":20}"#
        );
        assert_serde_json_serialize_eq!(&Temperature { temperature: 20 });
    }

    #[test]
    fn struct_() {
        #[derive(Serialize)]
        struct Nothing;

        assert_eq!(to_string(&Nothing).unwrap(), r#"null"#);
        assert_serde_json_serialize_eq!(&Nothing);

        #[derive(Serialize)]
        struct Empty {}

        assert_eq!(to_string(&Empty {}).unwrap(), r#"{}"#);
        assert_serde_json_serialize_eq!(&Empty {});

        #[derive(Serialize)]
        struct Tuple {
            a: bool,
            b: bool,
        }

        assert_eq!(
            to_string(&Tuple { a: true, b: false }).unwrap(),
            r#"{"a":true,"b":false}"#
        );
        assert_serde_json_serialize_eq!(&Tuple { a: true, b: false });
    }

    #[test]
    fn test_unit() {
        let a = ();
        assert_eq!(&*crate::to_string(&a).unwrap(), r#"null"#);
    }

    #[test]
    fn test_newtype_struct() {
        #[derive(Serialize)]
        struct A(pub u32);
        let a = A(54);
        assert_eq!(&*crate::to_string(&a).unwrap(), r#"54"#);
    }

    #[test]
    fn test_newtype_variant() {
        #[derive(Serialize)]
        enum A {
            A(u32),
        }
        let a = A::A(54);

        assert_eq!(&*crate::to_string(&a).unwrap(), r#"{"A":54}"#);
    }

    #[test]
    fn test_struct_variant() {
        #[derive(Serialize)]
        enum A {
            A { x: u32, y: u16 },
        }
        let a = A::A { x: 54, y: 720 };

        assert_eq!(&*crate::to_string(&a).unwrap(), r#"{"A":{"x":54,"y":720}}"#);
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(Serialize)]
        struct A<'a>(u32, Option<&'a str>, u16, bool);

        let a = A(42, Some("A string"), 720, false);

        assert_eq!(
            &*crate::to_string(&a).unwrap(),
            r#"[42,"A string",720,false]"#
        );
    }

    #[test]
    fn struct_with_flatten() {
        #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
        struct Pagination {
            limit: u64,
            offset: u64,
            total: u64,
        }

        #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
        struct Users {
            users: Vec<String>,

            #[serde(flatten)]
            pagination: Pagination,
        }

        let users = Users {
            users: vec!["joe".to_string(), "alice".to_string()],
            pagination: Pagination {
                offset: 100,
                limit: 20,
                total: 102,
            },
        };

        assert_eq!(
            to_string(&users).unwrap(),
            r#"{"users":["joe","alice"],"limit":20,"offset":100,"total":102}"#
        );
        assert_serde_json_serialize_eq!(&users);
    }

    #[test]
    fn btree_map() {
        use std::collections::BTreeMap;

        // empty map
        let empty = BTreeMap::<(), ()>::new();
        assert_eq!(to_string(&empty).unwrap(), r#"{}"#);
        assert_serde_json_serialize_eq!(&empty);

        // One element with unit type
        let mut map = BTreeMap::<&str, ()>::new();
        map.insert("set_element", ());
        assert_eq!(to_string(&map).unwrap(), r#"{"set_element":null}"#);
        assert_serde_json_serialize_eq!(&map);

        let mut two_values = BTreeMap::new();
        two_values.insert("my_name", "joseph");
        two_values.insert("her_name", "aline");
        assert_eq!(
            to_string(&two_values).unwrap(),
            r#"{"her_name":"aline","my_name":"joseph"}"#
        );
        assert_serde_json_serialize_eq!(&two_values);

        let mut nested_map = BTreeMap::new();
        nested_map.insert("two_entries", two_values.clone());

        two_values.remove("my_name");
        nested_map.insert("one_entry", two_values);
        assert_eq!(
            to_string(&nested_map).unwrap(),
            r#"{"one_entry":{"her_name":"aline"},"two_entries":{"her_name":"aline","my_name":"joseph"}}"#
        );
        assert_serde_json_serialize_eq!(&nested_map);
    }

    #[test]
    fn test_tuple_struct_roundtrip() {
        #[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
        struct A(u32, Option<String>, u16, bool);

        let a1 = A(42, Some("A string".to_string()), 720, false);
        let serialized = crate::to_string(&a1).unwrap();
        let a2: A = crate::from_str(&serialized).unwrap();
        assert_eq!(a1, a2);
    }

    #[test]
    fn test_serialize_bytes() {
        use core::fmt::Write;

        pub struct SimpleDecimal(f32);

        impl serde::Serialize for SimpleDecimal {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                let mut aux = String::new();
                write!(aux, "{:.2}", self.0).unwrap();
                serializer.serialize_bytes(aux.as_bytes())
            }
        }

        let sd1 = SimpleDecimal(1.55555);
        assert_eq!(&*crate::to_string(&sd1).unwrap(), r#"1.56"#);

        let sd2 = SimpleDecimal(0.000);
        assert_eq!(&*crate::to_string(&sd2).unwrap(), r#"0.00"#);

        let sd3 = SimpleDecimal(22_222.777);
        assert_eq!(&*crate::to_string(&sd3).unwrap(), r#"22222.78"#);
    }

    #[test]
    fn hash_map() {
        use std::collections::HashMap;

        // empty map
        let empty = HashMap::<(), ()>::new();
        assert_eq!(to_string(&empty).unwrap(), r#"{}"#);
        assert_serde_json_serialize_eq!(&empty);

        // One element
        let mut map = HashMap::new();
        map.insert("my_age", 28);
        assert_eq!(to_string(&map).unwrap(), r#"{"my_age":28}"#);
        assert_serde_json_serialize_eq!(&map);

        #[derive(Debug, Serialize, PartialEq, Eq, Hash)]
        pub struct NewType(String);

        // New type wrappers around String types work as keys
        let mut map = HashMap::new();
        map.insert(NewType(String::from("my_age")), 44);
        assert_eq!(to_string(&map).unwrap(), r#"{"my_age":44}"#);
        assert_serde_json_serialize_eq!(&map);

        #[derive(Debug, Serialize, PartialEq, Eq, Hash)]
        #[serde(rename_all = "lowercase")]
        pub enum MyResult {
            Err,
        }

        // Unit variants are also valid keys
        let mut map = HashMap::new();
        map.insert(MyResult::Err, 404);
        assert_eq!(to_string(&map).unwrap(), r#"{"err":404}"#);
        assert_serde_json_serialize_eq!(&map);

        // HashMap does not have deterministic iteration order (except in the Wasm target).
        // So the two element map is serialized as one of two options.
        let mut two_values = HashMap::new();
        two_values.insert("my_name", "joseph");
        two_values.insert("her_name", "aline");
        let serialized = to_string(&two_values).unwrap();
        assert!(
            serialized == r#"{"her_name":"aline","my_name":"joseph"}"#
                || serialized == r#"{"my_name":"joseph","her_name":"aline"}"#
        );
        assert_serde_json_serialize_eq!(&two_values);
    }

    #[test]
    fn number_key() {
        use std::collections::HashMap;

        // i8 key
        let mut map = HashMap::new();
        map.insert(10i8, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // i16 key
        let mut map = HashMap::new();
        map.insert(10i16, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // i32 key
        let mut map = HashMap::new();
        map.insert(10i32, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // i64 key
        let mut map = HashMap::new();
        map.insert(10i64, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);

        // i128 key
        let mut map = HashMap::new();
        map.insert(10i128, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // u8 key
        let mut map = HashMap::new();
        map.insert(10u8, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // u16 key
        let mut map = HashMap::new();
        map.insert(10u16, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);

        // u32 key
        let mut map = HashMap::new();
        map.insert(10u32, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // u64 key
        let mut map = HashMap::new();
        map.insert(10u64, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);

        // u128 key
        let mut map = HashMap::new();
        map.insert(10u128, "my_age");
        assert_eq!(to_string(&map).unwrap(), r#"{"10":"my_age"}"#);
        assert_serde_json_serialize_eq!(&map);
    }

    #[test]
    fn invalid_json_key() {
        use crate::ser::map::key_must_be_a_string;
        use std::collections::HashMap;

        #[derive(Debug, Serialize, PartialEq, Eq, Hash)]
        #[serde(rename_all = "lowercase")]
        pub enum MyResult {
            Unit(()),
            Ok(Response),
        }
        #[derive(Debug, Serialize, PartialEq, Eq, Hash)]
        pub struct Response {
            pub log: Option<String>,
            pub count: i64,
            pub list: Vec<u32>,
        }

        // unit enum
        let mut map = HashMap::new();
        map.insert(MyResult::Unit(()), "my_age");
        assert_eq!(
            to_string(&map).unwrap_err().to_string(),
            key_must_be_a_string().to_string()
        );

        // struct enum
        let mut map = HashMap::new();
        map.insert(
            MyResult::Ok(Response {
                log: None,
                count: 1,
                list: vec![6],
            }),
            "my_age",
        );
        assert_eq!(
            to_string(&map).unwrap_err().to_string(),
            key_must_be_a_string().to_string()
        );

        // Struct
        let mut map = HashMap::new();
        map.insert(
            Response {
                log: None,
                count: 1,
                list: vec![6],
            },
            "my_age",
        );
        assert_eq!(
            to_string(&map).unwrap_err().to_string(),
            key_must_be_a_string().to_string()
        );
    }

    #[test]
    fn serialize_embedded_enum() {
        use serde_derive::Deserialize;

        #[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
        #[serde(rename_all = "lowercase")]
        pub enum MyResult {
            Unit(()),
            Ok(Response),
            Err(String),
        }

        #[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
        pub struct Response {
            pub log: Option<String>,
            pub count: i64,
            pub list: Vec<u32>,
        }

        let err_input = MyResult::Err("some error".to_string());
        let json = to_string(&err_input).expect("encode err enum");
        assert_eq!(json, r#"{"err":"some error"}"#.to_string());
        let loaded = crate::from_str(&json).expect("re-load err enum");
        assert_eq!(err_input, loaded);
        assert_serde_json_serialize_eq!(&err_input);

        let unit = MyResult::Unit(());
        let json = to_string(&unit).expect("encode unit enum");
        assert_eq!(json, r#"{"unit":null}"#.to_string());
        let loaded = crate::from_str(&json).expect("re-load unit enum");
        assert_eq!(unit, loaded);
        assert_serde_json_serialize_eq!(&unit);

        let empty_list = MyResult::Ok(Response {
            log: Some("log message".to_string()),
            count: 137,
            list: Vec::new(),
        });
        let json = to_string(&empty_list).expect("encode ok enum");
        assert_eq!(
            json,
            r#"{"ok":{"log":"log message","count":137,"list":[]}}"#.to_string()
        );
        let loaded = crate::from_str(&json).expect("re-load ok enum");
        assert_eq!(empty_list, loaded);
        assert_serde_json_serialize_eq!(&empty_list);

        let full_list = MyResult::Ok(Response {
            log: None,
            count: 137,
            list: vec![18u32, 34, 12],
        });
        let json = to_string(&full_list).expect("encode ok enum");
        assert_eq!(
            json,
            r#"{"ok":{"log":null,"count":137,"list":[18,34,12]}}"#.to_string()
        );
        let loaded = crate::from_str(&json).expect("re-load ok enum");
        assert_eq!(full_list, loaded);
        assert_serde_json_serialize_eq!(&full_list);
    }
}
