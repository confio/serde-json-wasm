//! [`serde-json`] for `wasm` programs
//!
//! [`serde-json`]: https://crates.io/crates/serde_json
//!
//! This version of [`serde-json`] is aimed at applications that run on resource constrained
//! devices.
//!
//! # Current features
//!
//! - The error type is a simple C like enum (less overhead, smaller memory footprint)
//! - (De)serialization doesn't require memory allocations
//! - Deserialization of integers doesn't go through `u64`; instead the string is directly parsed
//!   into the requested integer type. This avoids pulling in KBs of compiler intrinsics when
//!   targeting a non 64-bit architecture.
//! - Supports deserialization of:
//!   - `bool`
//!   - Integers
//!   - Floats
//!   - `str` (This is a zero copy operation.) (\*)
//!   - `Option`
//!   - Arrays
//!   - Tuples
//!   - Structs
//!   - C like enums
//! - Supports serialization (compact format only) of:
//!   - `bool`
//!   - Integers
//!   - Floats
//!   - `str`
//!   - `Option`
//!   - Arrays
//!   - Tuples
//!   - Structs
//!   - C like enums
//!
//! (\*) Deserialization of strings ignores escaped sequences. Escaped sequences might be supported
//! in the future using a different Serializer as this operation is not zero copy.
//!
//! # Planned features
//!
//! - (De)serialization from / into IO objects once `core::io::{Read,Write}` becomes a thing.
//!
//! # Non-features
//!
//! This is explicitly out of scope
//!
//! - Anything that involves dynamic memory allocation
//!   - Like the dynamic [`Value`](https://docs.rs/serde_json/1.0.11/serde_json/enum.Value.html)
//!     type
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.62.0 and up. It *might* compile with older
//! versions but that may change in any new patch release.

#![deny(missing_docs)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]

pub mod de;
pub mod ser;

#[doc(inline)]
pub use self::de::{from_slice, from_str};
pub use self::ser::{to_string, to_vec};

#[cfg(test)]
mod test {
    use super::*;
    use serde_derive::{Deserialize, Serialize};

    #[derive(Debug, Deserialize, Serialize, PartialEq)]
    enum Model {
        Comment,
        Post { category: String, author: String },
    }

    #[derive(Debug, Deserialize, Serialize, PartialEq)]
    struct Stats {
        views: u64,
        score: i64,
    }

    #[derive(Debug, Deserialize, Serialize, PartialEq)]
    struct Item {
        model: Model,
        title: String,
        content: Option<String>,
        list: Vec<u32>,
        published: bool,
        stats: Stats,
    }

    #[test]
    fn can_serde() {
        let min = Item {
            model: Model::Comment,
            title: "".to_string(),
            content: None,
            list: vec![],
            published: false,
            stats: Stats { views: 0, score: 0 },
        };
        let max = Item {
            model: Model::Post {
                category: "fun".to_string(),
                author: "sunnyboy85".to_string(),
            },
            title: "Nice message".to_string(),
            content: Some("Happy \"blogging\" 👏\n\n\tCheers, I'm out\0\0\0".to_string()),
            list: vec![0, 1, 2, 3, 42, 154841, u32::MAX],
            published: true,
            stats: Stats {
                views: u64::MAX,
                score: i64::MIN,
            },
        };

        // binary
        assert_eq!(from_slice::<Item>(&to_vec(&min).unwrap()).unwrap(), min);
        assert_eq!(from_slice::<Item>(&to_vec(&max).unwrap()).unwrap(), max);

        // string
        assert_eq!(from_str::<Item>(&to_string(&min).unwrap()).unwrap(), min);
        assert_eq!(from_str::<Item>(&to_string(&max).unwrap()).unwrap(), max);
    }
}
