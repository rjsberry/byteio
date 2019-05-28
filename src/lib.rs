//! # byteio
//!
//! byteio is a simple crate that exposes lightweight abstractions for
//! read/write operations on contiguous slices of memory.
//!
//! The crate is based around two core traits: [`ReadBytes`][readbytes] and
//! [`WriteBytes`][writebytes]. Two extension traits which add functionality for
//! reading and writing numbers also have blanket implementations for any types
//! that implement the core traits.
//!
//! [readbytes]: trait.ReadBytes.html
//! [writebytes]: trait.WriteBytes.html
//!
//! # Installation
//!
//! To start using `byteio` add it to your `Cargo.toml` like so:
//!
//! ```toml
//! [dependencies]
//! byteio = "0.1"
//! ```
//!
//! By default this will active the `std` feature which enables functionality in
//! the crate which is only available when compiling with the standard library.
//!
//! To use the crate in a `no_std` environment you just need to disable this
//! feature. This can be done by adjusting your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! byteio = { version = "0.1", default-features = false }
//! ```
//!
//! The crate has a final feature: `alloc`. This should be used when you are
//! building in a `no_std` environment, have an allocator, and want
//! functionality for working with `Vec<u8>`. You can activate this by adjusting
//! your `Cargo.toml` again:
//!
//! ```toml
//! [dependencies]
//! byteio = { version = "0.1", default-features = false, features = ["alloc"] }
//! ```
//!
//! # Usage
//!
//! Manual serialization and deserialization of a simple network packet:
//!
//! ```
//! use std::convert::TryInto;
//!
//! use byteio::prelude::*; // ReadBytes, ReadBytesExt, WriteBytes, WriteBytesExt
//!
//! /// A packet whose payload is encoded as `[n_msb, n_lsb, b_0, b_1, ..., b_n-1]`.
//! struct Packet<'a> {
//!    payload: &'a [u8],
//! }
//!
//! impl<'a> Packet<'a> {
//!     fn decode<R: ReadBytes<'a>>(mut reader: R) -> byteio::Result<Self> {
//!         let len: usize = reader.try_read_u16_be()?.into();
//!         let payload = reader.try_read_exact(len)?;
//!
//!         Ok(Self { payload })
//!     }
//!
//!     fn encode<W: WriteBytes>(&self, mut writer: W) -> byteio::Result<()> {
//!         let len: u16 = self.payload.len().try_into().unwrap_or_else(|_| !0);
//!
//!         writer.try_write_u16_be(len)?;
//!         writer.try_write_exact(&self.payload[..usize::from(len)])?;
//!
//!         Ok(())
//!     }
//! }
//!
//! # #[cfg(any(feature = "std", feature = "alloc"))]
//! fn main() -> byteio::Result<()> {
//!     let data = b"\x00\x0Chello, world";
//!
//!     let packet = Packet::decode(&data[..])?;
//!     assert_eq!(packet.payload, b"hello, world");
//!
//!     let mut buf = Vec::new();
//!     packet.encode(&mut buf)?;
//!     assert_eq!(&*buf, data);
//!
//!     Ok(())
//! }
//!
//! # #[cfg(all(not(feature = "std"), not(feature = "alloc")))]
//! # fn main() {}
//! ```

#![no_std]
#![allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
#![deny(missing_docs)]

use core::{fmt, marker::PhantomData, mem};

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
use std::{error, io, vec::Vec};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

pub mod prelude {
    //! The `byteio` prelude.
    //!
    //! ```
    //! use byteio::prelude::*;
    //! ```
    //!
    //! The purpose of this module is to alleviate imports by adding a glob
    //! `use` to the top of `byteio` heavy modules.

    pub use crate::{ReadBytes, ReadBytesExt, WriteBytes, WriteBytesExt};
}

/// A specialized [`Result`][core-result-result] type for `byteio` operations.
///
/// This type alias is broadly used across `byteio` for operations that may
/// produce an error, that is, overflow the underlying buffer.
///
/// As with [`std::io::Result`][std-io-result], it is not recommended to import
/// this type directly and shadow [`core::result::Result`](core-result-result),
/// but instead to use `byteio::Result` to make it easier to distinguish.
///
/// # Examples
///
/// Trying to decode a string from raw bytes:
///
/// ```
/// use core::str::{self, Utf8Error};
///
/// use byteio::WriteBytes;
///
/// fn decode_str(buf: &[u8]) -> Result<&str, Utf8Error> {
///     str::from_utf8(buf)
/// }
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = [0; 5];
///
///     (&mut buf[..]).try_write_exact(b"hello")?;
///
///     match decode_str(&buf) {
///         Ok(s) => println!("str from utf8 success!"),
///         Err(e) => println!("str from utf8 failure: {}", e),
///     }
///
///     Ok(())
/// }
/// ```
///
/// [core-result-result]: https://doc.rust-lang.org/core/result/enum.Result.html
/// [std-io-result]: https://doc.rust-lang.org/std/io/type.Result.html
pub type Result<T> = ::core::result::Result<T, Error>;

/// The errors that can occur during `byteio` operations.
///
/// When using the `std` feature of `byteio`, this type implements
/// [`Into<std::io::Error>`][core-convert-into], which allows you to yield
/// `byteio` errors with the `?` operator in functions which return
/// [`std::io::Result`][std-io-result].
///
/// # Non-exhaustive
///
/// This enum is non-exhaustive; additional variants may be added in the future.
///
/// [core-convert-into]: https://doc.rust-lang.org/core/convert/trait.Into.html
/// [std-io-result]: https://doc.rust-lang.org/std/io/type.Result.html
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Error {
    /// The error returned when a `byteio` operation would overflow the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::{Error, WriteBytes};
    ///
    /// fn main() {
    ///     let mut buf = [0; 2];
    ///
    ///     let err = (&mut buf[..]).try_write_exact(&[1, 1, 1]).unwrap_err();
    ///     assert_eq!(err, Error::EndOfStream);
    /// }
    /// ```
    EndOfStream,
    #[doc(hidden)]
    #[allow(non_camel_case_types)]
    _nonexhaustive(()),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Error::EndOfStream => f.write_str("unexpected end of stream"),
            _ => unreachable!(),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {}

#[cfg(feature = "std")]
impl From<Error> for io::Error {
    fn from(error: Error) -> Self {
        match error {
            Error::EndOfStream => io::ErrorKind::UnexpectedEof.into(),
            _ => unreachable!(),
        }
    }
}

/*
 *
 * ReadBytes
 *
 */

/// Read a slice of bytes from a buffer.
///
/// Readers can be thought of as cursors that only allow you to seek forward
/// from the current position. They can be implemented with one method;
/// [`read_exact`][read-exact]. This forcibly attempts to split the underlying
/// buffer in order to extract a sub-slice with a given length, and advance the
/// buffer forward such that the next call to [`read_exact`][read-exact] will
/// return subsequent bytes in the buffer.
///
/// The lifetime of the slices extracted are tied to the underlying buffer. This
/// allows you to compose structures borrowing from the underlying buffer.
///
/// `ReadBytes` uses [`AsRef<[u8]>`][as-ref-u8] as a supertrait. This means that
/// a generic reader can obtain its current length or peek at the underlying
/// bytes without advancing the cursor through read operations. Note that by
/// using [`as_ref`][as-ref] on a reader you discard the lifetime information of
/// the underlying buffer for the returned reference.
///
/// # Examples
///
/// Reading from a slice:
///
/// ```
/// use byteio::ReadBytes;
///
/// fn main() {
///     let mut buf = &[1, 2, 3, 4, 5][..];
///
///     let sub_slice = buf.read_exact(2);
///     assert_eq!(sub_slice, &[1, 2][..]);
///
///     let sub_slice = buf.read_exact(3);
///     assert_eq!(sub_slice, &[3, 4, 5][..]);
///
///     assert!(buf.is_empty());
/// }
/// ```
///
/// Building a structure using borrowed data:
///
/// ```
/// use core::str;
///
/// use byteio::ReadBytes;
///
/// /// A packet whose payload is encoded as `[n, b0, b1, ..., bn-1]`.
/// struct Packet<'a> {
///     payload: &'a [u8],
/// }
///
/// impl<'a> Packet<'a> {
///     pub fn new<R: ReadBytes<'a>>(mut r: R) -> byteio::Result<Self> {
///         let len: usize = r.try_read_exact(1)?[0].into();
///         let payload = r.try_read_exact(len)?;
///
///         Ok(Self { payload })
///     }
/// }
///
/// fn main() -> byteio::Result<()> {
///     let buf = b"\x05hello";
///     
///     let packet = Packet::new(&buf[..])?;
///     assert_eq!(str::from_utf8(packet.payload).unwrap(), "hello");
///
///     Ok(())
/// }
/// ```
///
/// [read-exact]: trait.ReadBytes.html#tymethod.read_exact
/// [as-ref-u8]: https://doc.rust-lang.org/core/convert/trait.AsRef.html
/// [as-ref]: https://doc.rust-lang.org/core/convert/trait.AsRef.html#tymethod.as_ref
pub trait ReadBytes<'a>: AsRef<[u8]> {
    /// Forcibly attempts to read exactly `n` bytes from the buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_exact(&mut self, n: usize) -> &'a [u8];

    /// Attempts to read exactly `n` bytes from the buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_exact(&mut self, n: usize) -> crate::Result<&'a [u8]> {
        if n > self.as_ref().len() {
            Err(Error::EndOfStream)
        } else {
            Ok(self.read_exact(n))
        }
    }
}

impl<'a> ReadBytes<'a> for &'a [u8] {
    fn read_exact(&mut self, n: usize) -> &'a [u8] {
        let (a, b) = self.split_at(n);
        *self = b;
        a
    }
}

impl<'a> ReadBytes<'a> for &'a mut [u8] {
    fn read_exact(&mut self, n: usize) -> &'a [u8] {
        let (a, b) = mem::replace(self, &mut []).split_at_mut(n);
        *self = b;
        a
    }
}

/*
 *
 * ReadBytesExt
 *
 */

macro_rules! impl_read {
    ($doc:literal, $ty:ty, $fn:ident, $from_bytes:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn(&mut self) -> $ty {
            <$ty>::$from_bytes(unsafe {
                *(self.read_exact(mem::size_of::<$ty>()).as_ptr()
                    as *const [u8; mem::size_of::<$ty>()])
            })
        }
    }
}

macro_rules! impl_try_read {
    ($doc:literal, $ty:ty, $fn:ident, $from_bytes:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn(&mut self) -> crate::Result<$ty> {
            Ok(<$ty>::$from_bytes(unsafe {
                *(self.try_read_exact(mem::size_of::<$ty>())?.as_ptr()
                    as *const [u8; mem::size_of::<$ty>()])
            }))
        }
    }
}

/// Extends `ReadBytes` with functions for reading numbers.
///
/// # Examples
///
/// Read a `u16` from a buffer using native endianness:
///
/// ```
/// use byteio::ReadBytesExt;
///
/// fn main() {
///     let mut buf: &[u8] = &[0, 1];
///
///     #[cfg(target_endian = "little")]
///     let a = buf.read_u16_le();
///     #[cfg(target_endian = "big")]
///     let a = buf.read_u16_be();
///
///     assert!(buf.is_empty());
/// }
/// ```
pub trait ReadBytesExt<'a>: ReadBytes<'a> {
    /// Reads a `u8` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_u8(&mut self) -> u8 {
        self.read_exact(1)[0]
    }

    /// Attempts to read a `u8` from the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_u8(&mut self) -> crate::Result<u8> {
        Ok(self.try_read_exact(1)?[0])
    }

    /// Reads an `i8` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_i8(&mut self) -> i8 {
        self.read_exact(1)[0] as _
    }

    /// Attempts to read an `i8` from the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_i8(&mut self) -> crate::Result<i8> {
        Ok(self.try_read_exact(1)?[0] as _)
    }

    impl_read! {
"Reads a little endian `u16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        read_u16_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `u16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        read_u16_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `u16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_read_u16_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `u16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_read_u16_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `i16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        read_i16_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `i16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        read_i16_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `i16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_read_i16_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `i16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_read_i16_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `u32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        read_u32_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `u32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        read_u32_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `u32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_read_u32_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `u32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_read_u32_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `i32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        read_i32_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `i32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        read_i32_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `i32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_read_i32_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `i32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_read_i32_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `u64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        read_u64_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `u64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        read_u64_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `u64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_read_u64_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `u64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_read_u64_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `i64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        read_i64_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `i64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        read_i64_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `i64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_read_i64_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `i64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_read_i64_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `u128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        read_u128_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `u128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        read_u128_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `u128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_read_u128_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `u128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_read_u128_be,
        from_be_bytes,
    }

    impl_read! {
"Reads a little endian `i128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        read_i128_le,
        from_le_bytes,
    }

    impl_read! {
"Reads a big endian `i128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        read_i128_be,
        from_be_bytes,
    }

    impl_try_read! {
"Attempts to read a little endian `i128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_read_i128_le,
        from_le_bytes,
    }

    impl_try_read! {
"Attempts to read a big endian `i128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_read_i128_be,
        from_be_bytes,
    }

    /// Reads a little endian IEEE754 `f32` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_f32_le(&mut self) -> f32 {
        f32::from_bits(self.read_u32_le())
    }

    /// Reads a big endian IEEE754 `f32` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_f32_be(&mut self) -> f32 {
        f32::from_bits(self.read_u32_be())
    }

    /// Attempts to read a little endian IEEE754 `f32` from the underlying
    /// buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_f32_le(&mut self) -> crate::Result<f32> {
        Ok(f32::from_bits(self.try_read_u32_le()?))
    }

    /// Attempts to read a big endian IEEE754 `f32` from the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_f32_be(&mut self) -> crate::Result<f32> {
        Ok(f32::from_bits(self.try_read_u32_be()?))
    }

    /// Reads a little endian IEEE754 `f64` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_f64_le(&mut self) -> f64 {
        f64::from_bits(self.read_u64_le())
    }

    /// Reads a big endian IEEE754 `f64` from the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn read_f64_be(&mut self) -> f64 {
        f64::from_bits(self.read_u64_be())
    }

    /// Attempts to read a little endian IEEE754 `f64` from the underlying
    /// buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_f64_le(&mut self) -> crate::Result<f64> {
        Ok(f64::from_bits(self.try_read_u64_le()?))
    }

    /// Attempts to read a big endian IEEE754 `f64` from the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_read_f64_be(&mut self) -> crate::Result<f64> {
        Ok(f64::from_bits(self.try_read_u64_be()?))
    }
}

impl<'a, R: ReadBytes<'a>> ReadBytesExt<'a> for R {}

/*
 *
 * Reader
 *
 */

/// A convenience structure used for counting the number of bytes read.
///
/// This structure wraps an implementation of [`ReadBytes`][readbytes]. It
/// forwards read operations to the inner type while also maintaining a count
/// of the number of bytes that pass through it.
///
/// When you have finished with it, you can return the original type via the
/// [`into_inner`][into-inner] method.
///
/// When compiled with the `std` feature this structure implements
/// [`Read`][std-io-read].
///
/// [std-io-read]: https://doc.rust-lang.org/std/io/trait.Read.html
///
/// # Examples
///
/// ```
/// use byteio::{ReadBytes, ReadBytesExt, Reader};
///
/// fn main() -> byteio::Result<()> {
///     let buf: &[u8] = &[1, 0, 2, 0, 0, 0, 3];
///
///     let mut reader = Reader::new(buf);
///
///     assert_eq!(reader.try_read_u8()?, 1);
///     assert_eq!(reader.try_read_u16_be()?, 2);
///     assert_eq!(reader.try_read_u32_be()?, 3);
///
///     assert_eq!(reader.num_bytes_read(), 7);
///
///     let inner = reader.into_inner();
///     assert!(inner.is_empty());
///
///     Ok(())
/// }
/// ```
///
/// [readbytes]: trait.ReadBytes.html
/// [into-inner]: struct.Reader.html#method.into_inner
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Reader<'a, R: ReadBytes<'a>>(R, usize, PhantomData<&'a ()>);

impl<'a, R: ReadBytes<'a>> Reader<'a, R> {
    /// Creates a new `Reader` by wrapping a [`ReadBytes`][readbytes]
    /// implementor.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::Reader;
    ///
    /// let buf = [0_u8; 2];
    /// let mut reader = Reader::new(&buf[..]);
    /// ```
    ///
    /// [readbytes]: trait.ReadBytes.html
    #[inline]
    pub fn new(reader: R) -> Self {
        Self(reader, 0, PhantomData)
    }

    /// Retrieves the number of bytes that have been read by this `Reader`.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::{ReadBytes, Reader};
    ///
    /// let buf = [0_u8; 2];
    /// let mut reader = Reader::new(&buf[..]);
    /// let _ = reader.read_exact(1);
    /// let _ = reader.read_exact(1);
    ///
    /// assert_eq!(reader.num_bytes_read(), 2);
    /// ```
    #[inline]
    pub fn num_bytes_read(&self) -> usize {
        self.1
    }

    /// Consumes this `Reader` and returns the original [`ReadBytes`][readbytes]
    /// implementor.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::{ReadBytes, Reader};
    ///
    /// let buf = [0_u8; 2];
    /// let mut reader = Reader::new(&buf[..]);
    /// let _ = reader.read_exact(1);
    /// let inner = reader.into_inner();
    ///
    /// assert_eq!(inner.len(), 1); // the reader consumed one byte from its view of the slice
    /// ```
    ///
    /// [readbytes]: trait.ReadBytes.html
    #[inline]
    pub fn into_inner(self) -> R {
        self.0
    }
}

impl<'a, R: ReadBytes<'a>> AsRef<[u8]> for Reader<'a, R> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<'a, R: ReadBytes<'a>> ReadBytes<'a> for Reader<'a, R> {
    fn read_exact(&mut self, n: usize) -> &'a [u8] {
        self.1 += n;
        self.0.read_exact(n)
    }

    fn try_read_exact(&mut self, n: usize) -> crate::Result<&'a [u8]> {
        match self.0.try_read_exact(n) {
            res @ Ok(_) => {
                self.1 += n;
                res
            }
            res @ Err(_) => res,
        }
    }
}

#[cfg(feature = "std")]
impl<'a, R: ReadBytes<'a>> io::Read for Reader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = ::core::cmp::min(buf.len(), self.as_ref().len());
        buf[..n].copy_from_slice(<Self as ReadBytes>::read_exact(self, n));

        Ok(n)
    }
}

/*
 *
 * WriteBytes
 *
 */

/// Write a slice of bytes into a buffer.
///
/// Writers can be thought of as mutable cursors that only allow you to seek
/// forward from the current position. They can be implemented with one method;
/// [`write_exact`][write-exact]. This forcibly attempts to writer the bytes
/// to the underlying buffer, and advance the buffer forward such that the next
/// call to [`write_exact`][write-exact] will commit the bytes directly after
/// those previously written.
///
/// `WriteBytes` uses [`AsMut<[u8]>`][as-mut-u8] as a supertrait. This means
/// that a generic writer can obtain its current length or mutably peek at the
/// underlying bytes without advancing the cursor through write operations.
///
/// # Examples
///
/// Writing into a slice:
///
/// ```
/// use byteio::WriteBytes;
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = [0; 8];
///
///     {
///         let mut buf = &mut buf[..];
///
///         buf.try_write_exact(&[1, 2])?;
///         assert_eq!(buf.len(), 6);
///
///         buf.try_write_exact(&[3, 4, 5, 6, 7])?;
///         assert_eq!(buf.len(), 1);
///
///         buf.try_write_exact(&[8])?;
///         assert!(buf.is_empty());
///     }
///
///     assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8]);
///     Ok(())
/// }
/// ```
///
/// [write-exact]: trait.WriteBytes.html#tymethod.write_exact
/// [as-mut-u8]: https://doc.rust-lang.org/core/convert/trait.AsMut.html
pub trait WriteBytes: AsMut<[u8]> {
    /// Forcibly attempts to write the exact slice into the buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn write_exact(&mut self, buf: &[u8]);

    /// Attempts to write the exact slice into the buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_write_exact(&mut self, buf: &[u8]) -> crate::Result<()> {
        if buf.len() > self.as_mut().len() {
            Err(Error::EndOfStream)
        } else {
            self.write_exact(buf);
            Ok(())
        }
    }
}

impl<'a> WriteBytes for &'a mut [u8] {
    fn write_exact(&mut self, buf: &[u8]) {
        let (a, b) = mem::replace(self, &mut []).split_at_mut(buf.len());
        a.copy_from_slice(&buf);
        *self = b;
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'a> WriteBytes for &'a mut Vec<u8> {
    fn write_exact(&mut self, buf: &[u8]) {
        self.extend_from_slice(buf);
    }

    fn try_write_exact(&mut self, buf: &[u8]) -> crate::Result<()> {
        self.write_exact(buf);
        Ok(())
    }
}

/*
 *
 * WriteBytesExt
 *
 */

macro_rules! impl_write {
    ($doc:literal, $ty:ty, $fn:ident, $to_bytes:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn(&mut self, n: $ty) {
            self.write_exact(&n.$to_bytes()[..]);
        }
    }
}

macro_rules! impl_try_write {
    ($doc:literal, $ty:ty, $fn:ident, $to_bytes:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn(&mut self, n: $ty) -> crate::Result<()> {
            self.try_write_exact(&n.$to_bytes()[..])?;
            Ok(())
        }
    }
}

/// Extends `WriteBytes` with functions for writing numbers.
///
/// # Examples
///
/// Write a `u16` into a buffer using native endianness:
///
/// ```
/// use byteio::WriteBytesExt;
///
/// fn main() {
///     let mut buf = [0; 2];
///
///     {
///         let mut buf: &mut [u8] = &mut buf;
///
///         #[cfg(target_endian = "little")]
///         buf.write_u16_le(256);
///         #[cfg(target_endian = "big")]
///         buf.write_u16_be(256);
///
///         assert!(buf.is_empty());
///     }
/// }
/// ```
pub trait WriteBytesExt: WriteBytes {
    /// Writes a `u8` into the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    #[inline]
    fn write_u8(&mut self, n: u8) {
        self.write_exact(&[n]);
    }

    /// Attempts to write a `u8` into the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    #[inline]
    fn try_write_u8(&mut self, n: u8) -> crate::Result<()> {
        self.try_write_exact(&[n])?;
        Ok(())
    }

    /// Writes an `i8` into the underlying buffer.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    #[inline]
    fn write_i8(&mut self, n: i8) {
        self.write_exact(&[n as _]);
    }

    /// Attempts to write an `i8` into the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    #[inline]
    fn try_write_i8(&mut self, n: i8) -> crate::Result<()> {
        self.try_write_exact(&[n as _])?;
        Ok(())
    }

    impl_write! {
"Writes a `u16` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        write_u16_le,
        to_le_bytes,
    }

    impl_write! {
"Writes a `u16` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        write_u16_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write a `u16` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_write_u16_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write a `u16` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_write_u16_be,
        to_be_bytes,
    }

    impl_write! {
"Writes an `i16` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        write_i16_le,
        to_le_bytes,
    }

    impl_write! {
"Writes an `i16` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        write_i16_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write an `i16` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_write_i16_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write an `i16` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_write_i16_be,
        to_be_bytes,
    }

    impl_write! {
"Writes a `u32` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        write_u32_le,
        to_le_bytes,
    }

    impl_write! {
"Writes a `u32` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        write_u32_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write a `u32` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_write_u32_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write a `u32` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_write_u32_be,
        to_be_bytes,
    }

    impl_write! {
"Writes an `i32` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        write_i32_le,
        to_le_bytes,
    }

    impl_write! {
"Writes an `i32` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        write_i32_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write an `i32` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_write_i32_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write an `i32` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_write_i32_be,
        to_be_bytes,
    }

    impl_write! {
"Writes a `u64` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        write_u64_le,
        to_le_bytes,
    }

    impl_write! {
"Writes a `u64` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        write_u64_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write a `u64` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_write_u64_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write a `u64` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_write_u64_be,
        to_be_bytes,
    }

    impl_write! {
"Writes an `i64` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        write_i64_le,
        to_le_bytes,
    }

    impl_write! {
"Writes an `i64` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        write_i64_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write an `i64` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_write_i64_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write an `i64` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_write_i64_be,
        to_be_bytes,
    }

    impl_write! {
"Writes a `u128` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        write_u128_le,
        to_le_bytes,
    }

    impl_write! {
"Writes a `u128` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        write_u128_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write a `u128` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_write_u128_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write a `u128` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_write_u128_be,
        to_be_bytes,
    }

    impl_write! {
"Writes an `i128` into the underlying buffer in little endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        write_i128_le,
        to_le_bytes,
    }

    impl_write! {
"Writes an `i128` into the underlying buffer in big endian byte order.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        write_i128_be,
        to_be_bytes,
    }

    impl_try_write! {
"Attempts to write an `i128` into the underlying buffer in little endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_write_i128_le,
        to_le_bytes,
    }

    impl_try_write! {
"Attempts to write an `i128` into the underlying buffer in big endian byte order.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_write_i128_be,
        to_be_bytes,
    }

    /// Writes an IEEE754 `f32` into the underlying buffer in little endian byte
    /// order.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn write_f32_le(&mut self, n: f32) {
        self.write_u32_le(n.to_bits());
    }

    /// Writes an IEEE754 `f32` into the underlying buffer in big endian byte
    /// order.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn write_f32_be(&mut self, n: f32) {
        self.write_u32_be(n.to_bits());
    }

    /// Attempts to write an IEEE754 `f32` into the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_write_f32_le(&mut self, n: f32) -> crate::Result<()> {
        self.try_write_u32_le(n.to_bits())
    }

    /// Attempts to write an IEEE754 `f32` into the underlying buffer in big
    /// endian byte order.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_write_f32_be(&mut self, n: f32) -> crate::Result<()> {
        self.try_write_u32_be(n.to_bits())
    }

    /// Writes an IEEE754 `f64` into the underlying buffer in little endian byte
    /// order.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn write_f64_le(&mut self, n: f64) {
        self.write_u64_le(n.to_bits());
    }

    /// Writes an IEEE754 `f64` into the underlying buffer in big endian byte
    /// order.
    ///
    /// # Panics
    ///
    /// Panics if there are not enough bytes in `self`.
    fn write_f64_be(&mut self, n: f64) {
        self.write_u64_be(n.to_bits());
    }

    /// Attempts to write an IEEE754 `f64` into the underlying buffer.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_write_f64_le(&mut self, n: f64) -> crate::Result<()> {
        self.try_write_u64_le(n.to_bits())
    }

    /// Attempts to write an IEEE754 `f64` into the underlying buffer in big
    /// endian byte order.
    ///
    /// If there are not enough bytes in `self` this function will return
    /// `Error::EndOfStream`.
    fn try_write_f64_be(&mut self, n: f64) -> crate::Result<()> {
        self.try_write_u64_be(n.to_bits())
    }
}

impl<W: WriteBytes> WriteBytesExt for W {}

/*
 *
 * Writer
 *
 */

/// A convenience structure used for counting the number of bytes written.
///
/// This structure wraps an implementation of [`WriteBytes`][writebytes]. It
/// forwards write operations to the inner type while also maintaining a count
/// of the number of bytes that pass through it.
///
/// When you have finished with it, you can return the original type via the
/// [`into_inner`][into-inner] method.
///
/// When compiled with the `std` feature this structure implements
/// [`Write`][std-io-write].
///
/// [std-io-write]: https://doc.rust-lang.org/std/io/trait.Write.html
///
/// # Examples
///
/// ```
/// use byteio::{WriteBytes, WriteBytesExt, Writer};
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = [0; 7];
///
///     {
///         let mut writer = Writer::new(&mut buf[..]);
///
///         writer.try_write_u8(1)?;
///         writer.try_write_u16_be(2)?;
///         writer.try_write_u32_be(3)?;
///
///         assert_eq!(writer.num_bytes_written(), 7);
///
///         let inner = writer.into_inner();
///         assert!(inner.is_empty());
///     }
///
///     assert_eq!(buf, [1, 0, 2, 0, 0, 0, 3]);
///
///     Ok(())
/// }
/// ```
///
/// [writebytes]: trait.WriteBytes.html
/// [into-inner]: struct.Writer.html#method.into_inner
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Writer<W: WriteBytes>(W, usize);

impl<W: WriteBytes> Writer<W> {
    /// Creates a new `Writer` by wrapping a [`WriteBytes`][writebytes]
    /// implementor.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::Writer;
    ///
    /// let mut buf = [0_u8; 2];
    /// let mut writer = Writer::new(&mut buf[..]);
    /// ```
    ///
    /// [writebytes]: trait.WriteBytes.html
    #[inline]
    pub fn new(writer: W) -> Self {
        Self(writer, 0)
    }

    /// Retrieves the number of bytes that have been written by this `Writer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use byteio::{WriteBytes, Writer};
    ///
    /// let mut buf = [0_u8; 2];
    /// let mut writer = Writer::new(&mut buf[..]);
    /// writer.write_exact(&[1]);
    /// writer.write_exact(&[1]);
    ///
    /// assert_eq!(writer.num_bytes_written(), 2);
    /// ```
    #[inline]
    pub fn num_bytes_written(&self) -> usize {
        self.1
    }

    /// Consumes this `Writer` and returns the original
    /// [`WriteBytes`][writebytes] implementor.
    ///
    /// ```
    /// use byteio::{WriteBytes, Writer};
    ///
    /// let mut buf = [0_u8; 2];
    /// let mut writer = Writer::new(&mut buf[..]);
    /// writer.write_exact(&[1]);
    /// let inner = writer.into_inner();
    ///
    /// assert_eq!(inner.len(), 1); // the writer consumed one byte from its view of the slice
    /// ```
    ///
    /// [writebytes]: trait.WriteBytes.html
    #[inline]
    pub fn into_inner(self) -> W {
        self.0
    }
}

impl<W: WriteBytes> AsMut<[u8]> for Writer<W> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut()
    }
}

impl<W: WriteBytes> WriteBytes for Writer<W> {
    fn write_exact(&mut self, buf: &[u8]) {
        self.0.write_exact(buf);
        self.1 += buf.len();
    }

    fn try_write_exact(&mut self, buf: &[u8]) -> crate::Result<()> {
        match self.0.try_write_exact(buf) {
            res @ Ok(_) => {
                self.1 += buf.len();
                res
            }
            res @ Err(_) => res,
        }
    }
}

#[cfg(feature = "std")]
impl<W: WriteBytes> io::Write for Writer<W> {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        let n = ::core::cmp::min(data.len(), self.as_mut().len());
        <Self as WriteBytes>::write_exact(self, &data[..n]);

        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/*
 *
 * Unit tests
 *
 * For the full test suite, see $CARGO_MANIFEST_DIR/tests
 *
 */

#[cfg(test)]
mod test {
    #![allow(unused_imports)]

    use super::*;

    #[cfg(feature = "std")]
    #[test]
    fn io_error_from_error_end_of_stream() {
        let err: io::Error = Error::EndOfStream.into();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic]
    fn io_error_from_error_nonexhaustive() {
        let _: io::Error = Error::_nonexhaustive(()).into();
    }

    #[cfg(feature = "std")]
    #[test]
    fn display_error_end_of_stream() {
        use std::string::ToString;

        assert_eq!(Error::EndOfStream.to_string(), "unexpected end of stream");
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic]
    fn display_error_nonexhaustive() {
        use std::string::ToString;

        let _ = Error::_nonexhaustive(()).to_string();
    }
}
