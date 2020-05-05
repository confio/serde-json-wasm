use super::errors::{Error, Result};

// https://de.wikipedia.org/wiki/American_Standard_Code_for_Information_Interchange#ASCII-Tabelle
static BACKSPACE: u8 = 0x08; // BS
static FORMFEED: u8 = 0x0C; // FF
static LINEFEED: u8 = 0x0A; // LF
static CARRIAGE_RETURN: u8 = 0x0D; // CR
static HORIZONTAL_TAB: u8 = 0x09; // HT

pub(crate) fn unescape(source: &[u8]) -> Result<String> {
    let mut out: Vec<u8> = Vec::with_capacity(source.len());

    let mut open = false;
    for byte in source {
        if open {
            match byte {
                b'"' | b'/' | b'\\' => {
                    out.push(*byte);
                    open = false;
                }
                b'b' => {
                    out.push(BACKSPACE);
                    open = false;
                }
                b'f' => {
                    out.push(FORMFEED);
                    open = false;
                }
                b'n' => {
                    out.push(LINEFEED);
                    open = false;
                }
                b'r' => {
                    out.push(CARRIAGE_RETURN);
                    open = false;
                }
                b't' => {
                    out.push(HORIZONTAL_TAB);
                    open = false;
                }
                _ => panic!("unsupported escape sequence"),
            }
        } else if *byte == b'\\' {
            open = true;
        } else {
            out.push(*byte);
        }
    }

    String::from_utf8(out).map_err(|_| Error::InvalidUnicodeCodePoint)
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
    }
}
