//! # byteio
//!
//! I/O operations for contiguous [`u8`] regions.
//!
//! [`u8`]: https://doc.rust-lang.org/std/primitive.u8.html

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

use byteorder::ByteOrder;

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
    ($doc:literal, $ty:ty, $fn:ident, $byteorder:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn<E: ByteOrder>(&mut self) -> $ty {
            E::$byteorder(self.read_exact(mem::size_of::<$ty>()))
        }
    }
}

macro_rules! impl_try_read {
    ($doc:literal, $ty:ty, $fn:ident, $byteorder:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn<E: ByteOrder>(&mut self) -> crate::Result<$ty> {
            Ok(E::$byteorder(self.try_read_exact(mem::size_of::<$ty>())?))
        }
    }
}

/// Extends `ReadBytes` with functions for reading numbers.
///
/// # Examples
///
/// Read `u16`s from a buffer using native endianness:
///
/// ```
/// use byteio::ReadBytesExt;
/// use byteorder::NativeEndian;
///
/// fn main() {
///     let mut buf = &[0_u8, 1, 1, 0][..];
///
///     let a = buf.read_u16::<NativeEndian>();
///     let b = buf.read_u16::<NativeEndian>();
///
///     assert!(buf.is_empty());
/// }
/// ```
///
/// Try to read `u16`s from a buffer using a specific endianness:
///
/// ```
/// use byteio::ReadBytesExt;
/// use byteorder::{BigEndian, LittleEndian};
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = &[0_u8, 1, 1, 0][..];
///
///     let a = buf.try_read_u16::<BigEndian>()?;
///     let b = buf.try_read_u16::<LittleEndian>()?;
///
///     assert_eq!(a, 1);
///     assert_eq!(b, 1);
///
///     assert!(buf.is_empty());
///
///     Ok(())
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
"Reads a `u16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        read_u16,
        read_u16,
    }

    impl_try_read! {
"Attempts to read a `u16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_read_u16,
        read_u16,
    }

    impl_read! {
"Reads an `i16` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        read_i16,
        read_i16,
    }

    impl_try_read! {
"Attempts to read an `i16` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_read_i16,
        read_i16,
    }

    impl_read! {
"Reads a `u32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        read_u32,
        read_u32,
    }

    impl_try_read! {
"Attempts to read a `u32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_read_u32,
        read_u32,
    }

    impl_read! {
"Reads an `i32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        read_i32,
        read_i32,
    }

    impl_try_read! {
"Attempts to read an `i32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_read_i32,
        read_i32,
    }

    impl_read! {
"Reads a `u64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        read_u64,
        read_u64,
    }

    impl_try_read! {
"Attempts to read a `u64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_read_u64,
        read_u64,
    }

    impl_read! {
"Reads an `i64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        read_i64,
        read_i64,
    }

    impl_try_read! {
"Attempts to read an `i64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_read_i64,
        read_i64,
    }

    impl_read! {
"Reads a `u128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        read_u128,
        read_u128,
    }

    impl_try_read! {
"Attempts to read a `u128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_read_u128,
        read_u128,
    }

    impl_read! {
"Reads an `i128` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        read_i128,
        read_i128,
    }

    impl_try_read! {
"Attempts to read an `i128` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_read_i128,
        read_i128,
    }

    impl_read! {
"Reads an IEEE754 `f32` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        f32,
        read_f32,
        read_f32,
    }

    impl_try_read! {
"Attempts to read an IEEE754 `f32` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        f32,
        try_read_f32,
        read_f32,
    }

    impl_read! {
"Reads an IEEE754 `f64` from the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        f64,
        read_f64,
        read_f64,
    }

    impl_try_read! {
"Attempts to read an IEEE754 `f64` from the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        f64,
        try_read_f64,
        read_f64,
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
/// # Examples
///
/// ```
/// use byteio::{ReadBytes, ReadBytesExt, Reader};
/// use byteorder::BigEndian;
///
/// fn main() -> byteio::Result<()> {
///     let buf: &[u8] = &[1, 0, 2, 0, 0, 0, 3];
///
///     let mut reader = Reader::new(buf);
///
///     assert_eq!(reader.try_read_u8()?, 1);
///     assert_eq!(reader.try_read_u16::<BigEndian>()?, 2);
///     assert_eq!(reader.try_read_u32::<BigEndian>()?, 3);
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
    ($doc:literal, $ty:ty, $fn:ident, $byteorder:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn<E: ByteOrder>(&mut self, n: $ty) {
            let mut buf = [0; mem::size_of::<$ty>()];
            E::$byteorder(&mut buf, n);
            self.write_exact(&buf);
        }
    }
}

macro_rules! impl_try_write {
    ($doc:literal, $ty:ty, $fn:ident, $byteorder:ident $( , )?) => {
        #[doc = $doc]
        #[inline]
        fn $fn<E: ByteOrder>(&mut self, n: $ty) -> crate::Result<()> {
            let mut buf = [0; mem::size_of::<$ty>()];
            E::$byteorder(&mut buf, n);
            self.try_write_exact(&buf)?;
            Ok(())
        }
    }
}

/// Extends `WriteBytes` with functions for writing numbers.
///
/// # Examples
///
/// Write `u16`s into a buffer using native endianness:
///
/// ```
/// use byteio::WriteBytesExt;
/// use byteorder::NativeEndian;
///
/// fn main() {
///     let mut buf = [0; 4];
///
///     {
///         let mut buf = &mut buf[..];
///
///         buf.write_u16::<NativeEndian>(256);
///         buf.write_u16::<NativeEndian>(1);
///
///         assert!(buf.is_empty());
///     }
/// }
/// ```
///
/// Try to write `u16`s into a buffer using a specific endianness:
///
/// ```
/// use byteio::WriteBytesExt;
/// use byteorder::{BigEndian, LittleEndian};
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = [0; 4];
///
///     {
///         let mut buf = &mut buf[..];
///
///         buf.try_write_u16::<BigEndian>(1)?;
///         buf.try_write_u16::<LittleEndian>(1)?;
///
///         assert!(buf.is_empty());
///     }
///
///     assert_eq!(buf, [0, 1, 1, 0]);
///
///     Ok(())
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
"Writes a `u16` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u16,
        write_u16,
        write_u16,
    }

    impl_try_write! {
"Attempts to write a `u16` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u16,
        try_write_u16,
        write_u16,
    }

    impl_write! {
"Writes an `i16` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i16,
        write_i16,
        write_i16,
    }

    impl_try_write! {
"Attempts to write an `i16` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i16,
        try_write_i16,
        write_i16,
    }

    impl_write! {
"Writes a `u32` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u32,
        write_u32,
        write_u32,
    }

    impl_try_write! {
"Attempts to write a `u32` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u32,
        try_write_u32,
        write_u32,
    }

    impl_write! {
"Writes an `i32` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i32,
        write_i32,
        write_i32,
    }

    impl_try_write! {
"Attempts to write an `i32` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i32,
        try_write_i32,
        write_i32,
    }

    impl_write! {
"Writes a `u64` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u64,
        write_u64,
        write_u64,
    }

    impl_try_write! {
"Attempts to write a `u64` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u64,
        try_write_u64,
        write_u64,
    }

    impl_write! {
"Writes an `i64` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i64,
        write_i64,
        write_i64,
    }

    impl_try_write! {
"Attempts to write an `i64` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i64,
        try_write_i64,
        write_i64,
    }

    impl_write! {
"Writes a `u128` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        u128,
        write_u128,
        write_u128,
    }

    impl_try_write! {
"Attempts to write a `u128` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        u128,
        try_write_u128,
        write_u128,
    }

    impl_write! {
"Writes an `i128` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        i128,
        write_i128,
        write_i128,
    }

    impl_try_write! {
"Attempts to write an `i128` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        i128,
        try_write_i128,
        write_i128,
    }

    impl_write! {
"Writes an IEEE754 `f32` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        f32,
        write_f32,
        write_f32,
    }

    impl_try_write! {
"Attempts to write an IEEE754 `f32` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        f32,
        try_write_f32,
        write_f32,
    }

    impl_write! {
"Writes an IEEE754 `f64` into the underlying buffer.

# Panics

Panics if there are not enough bytes in `self`.",
        f64,
        write_f64,
        write_f64,
    }

    impl_try_write! {
"Attempts to write an IEEE754 `f64` into the underlying buffer.

If there are not enough bytes in `self` this function will return `Error::EndOfStream`.",
        f64,
        try_write_f64,
        write_f64,
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
/// # Examples
///
/// ```
/// use byteio::{WriteBytes, WriteBytesExt, Writer};
/// use byteorder::BigEndian;
///
/// fn main() -> byteio::Result<()> {
///     let mut buf = [0; 7];
///
///     {
///         let mut writer = Writer::new(&mut buf[..]);
///
///         writer.try_write_u8(1)?;
///         writer.try_write_u16::<BigEndian>(2)?;
///         writer.try_write_u32::<BigEndian>(3)?;
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
        self.1 += buf.len();
        self.0.write_exact(buf);
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
