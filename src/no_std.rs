//! if somebody will need alternative implementation, for example for collection or fmt, one may patch for himself this one

#[cfg(not(feature = "no-std"))]
pub use std::vec;

#[cfg(feature = "no-std")]
pub use alloc::vec;

#[cfg(feature = "no-std")]
pub use core::mem;
#[cfg(not(feature = "no-std"))]
pub use std::mem;

#[cfg(feature = "no-std")]
pub use core::result;
#[cfg(not(feature = "no-std"))]
pub use std::result;

#[cfg(feature = "no-std")]
pub use core::cmp;
#[cfg(not(feature = "no-std"))]
pub use std::cmp;

#[cfg(feature = "no-std")]
pub use core::error;
#[cfg(not(feature = "no-std"))]
pub use std::error;

#[cfg(not(feature = "no-std"))]
pub use std::iter;

#[cfg(feature = "no-std")]
pub use core::iter;

#[cfg(not(feature = "no-std"))]
pub use std::ops;

#[cfg(feature = "no-std")]
pub use core::ops;

#[cfg(not(feature = "no-std"))]
pub use std::string;

#[cfg(feature = "no-std")]
pub use alloc::string;

pub mod array {
    #[cfg(not(feature = "no-std"))]
    pub use std::array::TryFromSliceError;

    #[cfg(feature = "no-std")]
    pub use core::array::TryFromSliceError;
}

#[cfg(not(feature = "no-std"))]
pub use std::convert;

#[cfg(feature = "no-std")]
pub use core::convert;

#[cfg(not(feature = "no-std"))]
pub use std::collections;

#[cfg(feature = "no-std")]
pub use alloc::collections;

#[cfg(not(feature = "no-std"))]
pub use std::fmt;

#[cfg(feature = "no-std")]
pub use alloc::fmt;

pub mod borrow {
    #[cfg(not(feature = "no-std"))]
    pub use std::borrow::Cow;

    #[cfg(feature = "no-std")]
    pub use alloc::borrow::Cow;
}

#[cfg(not(feature = "no-std"))]
pub use std::str;

#[cfg(feature = "no-std")]
pub use alloc::str;

#[cfg(not(feature = "no-std"))]
pub use std::marker;

#[cfg(feature = "no-std")]
pub use core::marker;

pub mod any {
    #[cfg(not(feature = "no-std"))]
    pub use std::any::type_name;

    #[cfg(feature = "no-std")]
    pub use core::any::type_name;
}

// just because it is default prelude
pub mod prelude {
    pub use super::{
        marker::{Send, Sync},
        result::Result::{Err, Ok},
        string::{String, ToString},
        vec::Vec,
    };
}
