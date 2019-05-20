<h1 align="center">byteio</h1>
<div align="center">
  <strong>
    I/O abstractions for bytes.
  </strong>
</div>

<br />

<div align="center">
  <!-- crate version (crates.io) -->
  <a href="https://crates.io/crates/byteio">
    <img src="https://img.shields.io/crates/v/byteio.svg?style=flat-square"
      alt="crate version (crates.io)" />
  </a>

  <!-- build status (azure) -->
  <a href="https://dev.azure.com/rjsberry/byteio/_build?definitionId=2">
    <img src="https://img.shields.io/azure-devops/build/rjsberry/eefd02b5-74a7-4227-8be5-dbd037a5e6d1/2.svg?style=flat-square"
      alt="build status (azure)" />
  </a>

  <!-- docs (docs.rs) -->
  <a href="https://docs.rs/byteio">
    <img src="https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square"
      alt="docs (docs.rs)" />
  </a>

  <!-- coverage (codecov.io) -->
  <a href="https://codecov.io/gh/rjsberry/byteio">
    <img src="https://img.shields.io/codecov/c/github/rjsberry/byteio.svg?style=flat-square"
      alt="coverage (codecov.io)" />
  </a>
</div>

## About

`byteio` is a simple crate that exposes lightweight abstractions for read/write
operations on contiguous slices of memory.

At its core `byteio` is nothing new. A lot of the functionality it offers can be
found elsewhere, such as [`std::io`][std-io], [`byteorder`][byteorder], and
[`bytes`][bytes]. What it does offer is:

* First class `no_std` support.
* Reads with lifetimes tied to the underlying buffers.

The crate is based around two core traits: [`ReadBytes`][readbytes] and
[`WriteBytes`][writebytes]. Two extension traits which add functionality for
reading and writing numbers also have blanket implementations for any types that
implement the core traits.

[std-io]: https://doc.rust-lang.org/std/io/index.html
[byteorder]: https://docs.rs/byteorder/latest/byteorder/
[bytes]: https://docs.rs/bytes/latest/bytes
[readbytes]: https://docs.rs/byteio/latest/byteio/trait.ReadBytes.html
[writebytes]: https://docs.rs/byteio/latest/byteio/trait.WriteBytes.html

## Installation

To start using `byteio` add it to your `Cargo.toml` like so:

```toml
[dependencies]
byteio = "0.1"
```

By default this will active the `std` feature which enables functionality in
the crate which is only available when compiling with the standard library.

To use the crate in a `no_std` environment you just need to disable this
feature. This can be done by adjusting your `Cargo.toml`:

```toml
[dependencies]
byteio = { version = "0.1", default-features = false }
```

The crate has a final feature: `alloc`. This should be used when you are
building in a `no_std` environment, have an allocator, and want
functionality for working with `Vec<u8>`. You can activate this by adjusting
your `Cargo.toml` again:

```toml
[dependencies]
byteio = { version = "0.1", default-features = false, features = ["alloc"] }
```

## Usage

Manual serialization and deserialization of a simple network packet:

```rust
use std::convert::TryInto;

use byteio::prelude::*; // ReadBytes, ReadBytesExt, WriteBytes, WriteBytesExt
use byteorder::NetworkEndian;

/// A packet whose payload is encoded as `[n_msb, n_lsb, b_0, b_1, ..., b_n-1]`.
struct Packet<'a> {
   payload: &'a [u8],
}

impl<'a> Packet<'a> {
    fn decode<R: ReadBytes<'a>>(mut reader: R) -> byteio::Result<Self> {
        let len: usize = reader.try_read_u16::<NetworkEndian>()?.into();
        let payload = reader.try_read_exact(len)?;

        Ok(Self { payload })
    }

    fn encode<W: WriteBytes>(&self, mut writer: W) -> byteio::Result<()> {
        let len: u16 = self.payload.len().try_into().unwrap_or_else(|_| !0);

        writer.try_write_u16::<NetworkEndian>(len)?;
        writer.try_write_exact(&self.payload[..usize::from(len)])?;

        Ok(())
    }
}

fn main() -> byteio::Result<()> {
    let data = b"\x00\x0Chello, world";

    let packet = Packet::decode(&data[..])?;
    assert_eq!(packet.payload, b"hello, world");

    let mut buf = Vec::new();
    packet.encode(&mut buf)?;
    assert_eq!(&*buf, data);

    Ok(())
}
```

## License

This project is dual-licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

## Contributing

If you would like to contribute to `byteio`, experience any issues, or even have
features you would like to see implemented, [new issues][new-issue] and pull
requests are welcomed.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `byteio` by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[new-issue]: https://github.com/rjsberry/byteio/issues/new
