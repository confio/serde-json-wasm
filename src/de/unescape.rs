use super::errors::{Error, Result};

pub(crate) fn unescape(source: &[u8]) -> Result<String> {
    // TODO: implement unescaping
    let string_data = source.to_vec();
    String::from_utf8(string_data).map_err(|_| Error::InvalidUnicodeCodePoint)
}
