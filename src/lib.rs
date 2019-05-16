//! # byteio
//!
//! I/O operations for contiguous [`u8`] regions.
//!
//! [`u8`]: https://doc.rust-lang.org/std/primitive.u8.html

#![no_std]

use core::{fmt, mem};

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

    pub use crate::{ReadBytes, WriteBytes};
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
            Ok(self.write_exact(buf))
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
        Ok(self.write_exact(buf))
    }
}
