use std::convert::TryFrom;

use super::errors::{Error, Result};

// https://de.wikipedia.org/wiki/American_Standard_Code_for_Information_Interchange#ASCII-Tabelle
static BACKSPACE: u8 = 0x08; // BS
static FORMFEED: u8 = 0x0C; // FF
static LINEFEED: u8 = 0x0A; // LF
static CARRIAGE_RETURN: u8 = 0x0D; // CR
static HORIZONTAL_TAB: u8 = 0x09; // HT

pub(crate) fn unescape(source: &[u8]) -> Result<String> {
    let mut out: Vec<u8> = Vec::with_capacity(source.len());

    let mut encoding_tmp = [0u8; 4];
    let mut in_escape = false;
    let mut in_unicode = false;
    // Temporary storage of the four hex characters of \uACDC
    let mut unicode_tmp = [0u8; 4];
    // Position in `unicode_tmp` where the next insertion happens
    let mut unicode_tmp_pos: usize = 0;

    for byte in source {
        if in_unicode {
            match byte {
                b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' => {
                    unicode_tmp[unicode_tmp_pos] = *byte;
                    unicode_tmp_pos += 1;
                    if unicode_tmp_pos == 4 {
                        let codepoint = hex_decode(unicode_tmp);
                        let encoded = match char::try_from(codepoint as u32) {
                            Ok(c) => c.encode_utf8(&mut encoding_tmp as &mut [u8]),
                            Err(_) => return Err(Error::InvalidEscape),
                        };
                        out.extend_from_slice(encoded.as_bytes());
                        unicode_tmp_pos = 0;
                        in_unicode = false;
                        in_escape = false;
                    }
                }
                _ => return Err(Error::InvalidEscape),
            }
        } else if in_escape {
            match byte {
                b'"' | b'/' | b'\\' => {
                    out.push(*byte);
                    in_escape = false;
                }
                b'b' => {
                    out.push(BACKSPACE);
                    in_escape = false;
                }
                b'f' => {
                    out.push(FORMFEED);
                    in_escape = false;
                }
                b'n' => {
                    out.push(LINEFEED);
                    in_escape = false;
                }
                b'r' => {
                    out.push(CARRIAGE_RETURN);
                    in_escape = false;
                }
                b't' => {
                    out.push(HORIZONTAL_TAB);
                    in_escape = false;
                }
                b'u' => {
                    in_unicode = true;
                }
                _ => return Err(Error::InvalidEscape),
            }
        } else {
            // Default case, not in escape sequence

            if *byte == b'\\' {
                in_escape = true;
            } else {
                out.push(*byte);
            }
        }
    }

    if in_escape {
        return Err(Error::InvalidEscape);
    }

    String::from_utf8(out).map_err(|_| Error::InvalidUnicodeCodePoint)
}

/// Returns a 16 bit value between 0x0000 and 0xFFFF, i.e. a codepoint
/// in the Basic Multilingual Plane.
fn hex_decode(a: [u8; 4]) -> u16 {
    (hex_decode_4bit(a[0]) as u16) << 12
        | (hex_decode_4bit(a[1]) as u16) << 8
        | (hex_decode_4bit(a[2]) as u16) << 4
        | (hex_decode_4bit(a[3]) as u16)
}

/// Decodes a single hex character into its numeric value, i.e. maps
/// ASCII '0'-'9' to 0-9, 'A'-'F' to 10-15 and 'a'-'f' to 10-15.
fn hex_decode_4bit(x: u8) -> u8 {
    match x {
        b'0'..=b'9' => x - 0x30,
        b'A'..=b'F' => x - 0x41 + 10,
        b'a'..=b'f' => x - 0x61 + 10,
        _ => panic!("Non-hex ASCII character found"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A testing wrapper around unescape
    fn ue(source: &[u8]) -> String {
        unescape(source).unwrap()
    }

    #[test]
    fn unescape_works() {
        // Unchanged because no unescaping happens
        assert_eq!(ue(b""), "".to_string());
        assert_eq!(ue(b"a"), "a".to_string());
        assert_eq!(ue(b"ab"), "ab".to_string());
        assert_eq!(ue(b"abc"), "abc".to_string());
        assert_eq!(ue(b"a/c"), "a/c".to_string());
        assert_eq!(ue(b"\xF0\x9F\x91\x8F"), "👏".to_string()); // U+1F44F

        // even number of backslashes
        assert_eq!(ue(br#"\\"#), "\\".to_string());
        assert_eq!(ue(br#"\\\\"#), "\\\\".to_string());
        assert_eq!(ue(br#"\\\\\\"#), "\\\\\\".to_string());
        assert_eq!(ue(br#"\\\\\\\\"#), "\\\\\\\\".to_string());

        // The 8 short escape sequences \", \\, \/, \b, \f, \n, \r, \t (alone, start, end, middle)
        assert_eq!(ue(br#"\""#), "\"".to_string());
        assert_eq!(ue(br#"\\"#), "\\".to_string());
        assert_eq!(ue(br#"\/"#), "/".to_string());
        assert_eq!(ue(br#"\b"#), "\x08".to_string());
        assert_eq!(ue(br#"\f"#), "\x0C".to_string());
        assert_eq!(ue(br#"\n"#), "\n".to_string());
        assert_eq!(ue(br#"\r"#), "\r".to_string());
        assert_eq!(ue(br#"\t"#), "\t".to_string());
        assert_eq!(ue(br#"\"abc"#), "\"abc".to_string());
        assert_eq!(ue(br#"\\abc"#), "\\abc".to_string());
        assert_eq!(ue(br#"\/abc"#), "/abc".to_string());
        assert_eq!(ue(br#"\babc"#), "\x08abc".to_string());
        assert_eq!(ue(br#"\fabc"#), "\x0Cabc".to_string());
        assert_eq!(ue(br#"\nabc"#), "\nabc".to_string());
        assert_eq!(ue(br#"\rabc"#), "\rabc".to_string());
        assert_eq!(ue(br#"\tabc"#), "\tabc".to_string());
        assert_eq!(ue(br#"abc\""#), "abc\"".to_string());
        assert_eq!(ue(br#"abc\\"#), "abc\\".to_string());
        assert_eq!(ue(br#"abc\/"#), "abc/".to_string());
        assert_eq!(ue(br#"abc\b"#), "abc\x08".to_string());
        assert_eq!(ue(br#"abc\f"#), "abc\x0C".to_string());
        assert_eq!(ue(br#"abc\n"#), "abc\n".to_string());
        assert_eq!(ue(br#"abc\r"#), "abc\r".to_string());
        assert_eq!(ue(br#"abc\t"#), "abc\t".to_string());
        assert_eq!(ue(br#"xy\"abc"#), "xy\"abc".to_string());
        assert_eq!(ue(br#"xy\\abc"#), "xy\\abc".to_string());
        assert_eq!(ue(br#"xy\/abc"#), "xy/abc".to_string());
        assert_eq!(ue(br#"xy\babc"#), "xy\x08abc".to_string());
        assert_eq!(ue(br#"xy\fabc"#), "xy\x0Cabc".to_string());
        assert_eq!(ue(br#"xy\nabc"#), "xy\nabc".to_string());
        assert_eq!(ue(br#"xy\rabc"#), "xy\rabc".to_string());
        assert_eq!(ue(br#"xy\tabc"#), "xy\tabc".to_string());

        // Short escape sequences mixed
        assert_eq!(ue(br#" \" \" \" "#), " \" \" \" ".to_string());
        assert_eq!(ue(br#" \t \n \r "#), " \t \n \r ".to_string());
        assert_eq!(ue(br#" \"\"\" "#), " \"\"\" ".to_string());
        assert_eq!(ue(br#" \t\n\r "#), " \t\n\r ".to_string());

        // Unicode
        assert_eq!(ue(br#" \u0001 "#), " \u{0001} ".to_string());
        assert_eq!(ue(br#" \u0010 "#), " \u{0010} ".to_string());
        assert_eq!(ue(br#" \u0100 "#), " \u{0100} ".to_string());
        assert_eq!(ue(br#" \u1000 "#), " \u{1000} ".to_string());
        assert_eq!(ue(br#" \uABCD "#), " \u{abcd} ".to_string());
        assert_eq!(ue(br#" \uabcd "#), " \u{abcd} ".to_string());
        assert_eq!(ue(br#" \uAbCd "#), " \u{abcd} ".to_string());
        assert_eq!(ue(br#" \uABCDefg "#), " \u{abcd}efg ".to_string());
        assert_eq!(ue(br#" \uabcdefg "#), " \u{abcd}efg ".to_string());
        assert_eq!(ue(br#" \uAbCdefg "#), " \u{abcd}efg ".to_string());
    }

    #[test]
    fn unescape_fails_for_invalid_escape_sequence() {
        assert_eq!(unescape(br#" \ "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \a "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \N "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \- "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \' "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \x "#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \x08 "#), Err(Error::InvalidEscape)); // valid in Rust and ES6 but not JSON

        // unicode
        assert_eq!(unescape(br#" \u{7A} "#), Err(Error::InvalidEscape)); // valid in ES6 but not JSON
        assert_eq!(unescape(br#" \uAAA "#), Err(Error::InvalidEscape)); // too short
        assert_eq!(unescape(br#" \uAA "#), Err(Error::InvalidEscape)); // too short
        assert_eq!(unescape(br#" \uA "#), Err(Error::InvalidEscape)); // too short
        assert_eq!(unescape(br#" \u "#), Err(Error::InvalidEscape)); // too short
        assert_eq!(unescape(br#" \u123. "#), Err(Error::InvalidEscape)); // non-hex char
        assert_eq!(unescape(br#" \u123g "#), Err(Error::InvalidEscape)); // non-hex char
        assert_eq!(unescape(br#" \u123\9 "#), Err(Error::InvalidEscape)); // non-hex char

        // unfinished escape sequences
        assert_eq!(unescape(br#" \u123"#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \u12"#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \u1"#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \u"#), Err(Error::InvalidEscape));
        assert_eq!(unescape(br#" \"#), Err(Error::InvalidEscape));
    }

    #[test]
    fn unescape_fails_for_surrogates() {
        // TODO: implement
        assert_eq!(unescape(br#" \uDEAD "#), Err(Error::InvalidEscape)); // surrogate
    }

    #[test]
    fn hex_decode_works() {
        assert_eq!(hex_decode([b'0', b'0', b'0', b'0']), 0x0000);
        assert_eq!(hex_decode([b'0', b'0', b'0', b'1']), 0x0001);
        assert_eq!(hex_decode([b'0', b'0', b'1', b'0']), 0x0010);
        assert_eq!(hex_decode([b'0', b'1', b'0', b'0']), 0x0100);
        assert_eq!(hex_decode([b'1', b'0', b'0', b'0']), 0x1000);
        assert_eq!(hex_decode([b'1', b'1', b'1', b'1']), 0x1111);
        assert_eq!(hex_decode([b'1', b'1', b'1', b'0']), 0x1110);
        assert_eq!(hex_decode([b'1', b'1', b'0', b'1']), 0x1101);
        assert_eq!(hex_decode([b'1', b'0', b'1', b'1']), 0x1011);
        assert_eq!(hex_decode([b'0', b'1', b'1', b'1']), 0x0111);

        assert_eq!(hex_decode([b'2', b'3', b'4', b'5']), 0x2345);
        assert_eq!(hex_decode([b'6', b'7', b'8', b'9']), 0x6789);
        assert_eq!(hex_decode([b'a', b'b', b'c', b'd']), 0xabcd);
        assert_eq!(hex_decode([b'e', b'f', b'A', b'B']), 0xefab);
        assert_eq!(hex_decode([b'C', b'D', b'E', b'F']), 0xcdef);
    }
}
