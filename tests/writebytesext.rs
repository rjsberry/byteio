macro_rules! _impl_write_test {
    ($ty:ty, $test:ident, $fn:ident, $to_endian:ident) => {
        #[quickcheck]
        fn $test(n: $ty) -> bool {
            let mut buf = [0_u8; mem::size_of::<$ty>()];
            {
                let mut buf = &mut buf[..];
                buf.$fn(n);
            }
            buf == n.$to_endian()
        }
    };
}

macro_rules! _impl_try_write_test {
    ($ty:ty, $test:ident, $fn:ident, $to_endian:ident) => {
        #[quickcheck]
        fn $test(n: $ty) -> bool {
            let mut buf = [0_u8; mem::size_of::<$ty>()];
            {
                let mut buf = &mut buf[..];
                buf.$fn(n).unwrap();
            }
            buf == n.$to_endian()
        }
    };
}

mod be {
    use std::mem;

    use byteio::WriteBytesExt;

    use quickcheck_macros::quickcheck;

    macro_rules! impl_write_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_write_test!($ty, $test, $fn, to_be_bytes);
        };
    }

    macro_rules! impl_try_write_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_try_write_test!($ty, $test, $fn, to_be_bytes);
        };
    }

    #[quickcheck]
    fn qc_write_u8(n: u8) -> bool {
        let mut buf = [0_u8; mem::size_of::<u8>()];
        {
            let mut buf = &mut buf[..];
            buf.write_u8(n);
        }
        buf == n.to_be_bytes()
    }

    #[quickcheck]
    fn qc_try_write_u8(n: u8) -> bool {
        let mut buf = [0_u8; mem::size_of::<u8>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_u8(n).unwrap();
        }
        buf == n.to_be_bytes()
    }

    #[quickcheck]
    fn qc_write_i8(n: i8) -> bool {
        let mut buf = [0_u8; mem::size_of::<i8>()];
        {
            let mut buf = &mut buf[..];
            buf.write_i8(n);
        }
        buf == n.to_be_bytes()
    }

    #[quickcheck]
    fn qc_try_write_i8(n: i8) -> bool {
        let mut buf = [0_u8; mem::size_of::<i8>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_i8(n).unwrap();
        }
        buf == n.to_be_bytes()
    }

    impl_write_test!(u16, qc_write_u16, write_u16_be);
    impl_try_write_test!(u16, qc_try_write_u16, try_write_u16_be);

    impl_write_test!(i16, qc_write_i16, write_i16_be);
    impl_try_write_test!(i16, qc_try_write_i16, try_write_i16_be);

    impl_write_test!(u32, qc_write_u32, write_u32_be);
    impl_try_write_test!(u32, qc_try_write_u32, try_write_u32_be);

    impl_write_test!(i32, qc_write_i32, write_i32_be);
    impl_try_write_test!(i32, qc_try_write_i32, try_write_i32_be);

    impl_write_test!(u64, qc_write_u64, write_u64_be);
    impl_try_write_test!(u64, qc_try_write_u64, try_write_u64_be);

    impl_write_test!(i64, qc_write_i64, write_i64_be);
    impl_try_write_test!(i64, qc_try_write_i64, try_write_i64_be);

    impl_write_test!(u128, qc_write_u128, write_u128_be);
    impl_try_write_test!(u128, qc_try_write_u128, try_write_u128_be);

    impl_write_test!(i128, qc_write_i128, write_i128_be);
    impl_try_write_test!(i128, qc_try_write_i128, try_write_i128_be);

    #[quickcheck]
    fn qc_write_f32(n: f32) -> bool {
        let mut buf = [0_u8; mem::size_of::<f32>()];
        {
            let mut buf = &mut buf[..];
            buf.write_f32_be(n);
        }
        buf == n.to_bits().to_be_bytes()
    }

    #[quickcheck]
    fn qc_try_write_f32(n: f32) -> bool {
        let mut buf = [0_u8; mem::size_of::<f32>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_f32_be(n).unwrap();
        }
        buf == n.to_bits().to_be_bytes()
    }

    #[quickcheck]
    fn qc_write_f64(n: f64) -> bool {
        let mut buf = [0_u8; mem::size_of::<f64>()];
        {
            let mut buf = &mut buf[..];
            buf.write_f64_be(n);
        }
        buf == n.to_bits().to_be_bytes()
    }

    #[quickcheck]
    fn qc_try_write_f64(n: f64) -> bool {
        let mut buf = [0_u8; mem::size_of::<f64>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_f64_be(n).unwrap();
        }
        buf == n.to_bits().to_be_bytes()
    }
}

mod le {
    use std::mem;

    use byteio::WriteBytesExt;

    use quickcheck_macros::quickcheck;

    macro_rules! impl_write_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_write_test!($ty, $test, $fn, to_le_bytes);
        };
    }

    macro_rules! impl_try_write_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_try_write_test!($ty, $test, $fn, to_le_bytes);
        };
    }

    #[quickcheck]
    fn qc_write_u8(n: u8) -> bool {
        let mut buf = [0_u8; mem::size_of::<u8>()];
        {
            let mut buf = &mut buf[..];
            buf.write_u8(n);
        }
        buf == n.to_le_bytes()
    }

    #[quickcheck]
    fn qc_try_write_u8(n: u8) -> bool {
        let mut buf = [0_u8; mem::size_of::<u8>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_u8(n).unwrap();
        }
        buf == n.to_le_bytes()
    }

    #[quickcheck]
    fn qc_write_i8(n: i8) -> bool {
        let mut buf = [0_u8; mem::size_of::<i8>()];
        {
            let mut buf = &mut buf[..];
            buf.write_i8(n);
        }
        buf == n.to_le_bytes()
    }

    #[quickcheck]
    fn qc_try_write_i8(n: i8) -> bool {
        let mut buf = [0_u8; mem::size_of::<i8>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_i8(n).unwrap();
        }
        buf == n.to_le_bytes()
    }

    impl_write_test!(u16, qc_write_u16, write_u16_le);
    impl_try_write_test!(u16, qc_try_write_u16, try_write_u16_le);

    impl_write_test!(i16, qc_write_i16, write_i16_le);
    impl_try_write_test!(i16, qc_try_write_i16, try_write_i16_le);

    impl_write_test!(u32, qc_write_u32, write_u32_le);
    impl_try_write_test!(u32, qc_try_write_u32, try_write_u32_le);

    impl_write_test!(i32, qc_write_i32, write_i32_le);
    impl_try_write_test!(i32, qc_try_write_i32, try_write_i32_le);

    impl_write_test!(u64, qc_write_u64, write_u64_le);
    impl_try_write_test!(u64, qc_try_write_u64, try_write_u64_le);

    impl_write_test!(i64, qc_write_i64, write_i64_le);
    impl_try_write_test!(i64, qc_try_write_i64, try_write_i64_le);

    impl_write_test!(u128, qc_write_u128, write_u128_le);
    impl_try_write_test!(u128, qc_try_write_u128, try_write_u128_le);

    impl_write_test!(i128, qc_write_i128, write_i128_le);
    impl_try_write_test!(i128, qc_try_write_i128, try_write_i128_le);

    #[quickcheck]
    fn qc_write_f32(n: f32) -> bool {
        let mut buf = [0_u8; mem::size_of::<f32>()];
        {
            let mut buf = &mut buf[..];
            buf.write_f32_le(n);
        }
        buf == n.to_bits().to_le_bytes()
    }

    #[quickcheck]
    fn qc_try_write_f32(n: f32) -> bool {
        let mut buf = [0_u8; mem::size_of::<f32>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_f32_le(n).unwrap();
        }
        buf == n.to_bits().to_le_bytes()
    }

    #[quickcheck]
    fn qc_write_f64(n: f64) -> bool {
        let mut buf = [0_u8; mem::size_of::<f64>()];
        {
            let mut buf = &mut buf[..];
            buf.write_f64_le(n);
        }
        buf == n.to_bits().to_le_bytes()
    }

    #[quickcheck]
    fn qc_try_write_f64(n: f64) -> bool {
        let mut buf = [0_u8; mem::size_of::<f64>()];
        {
            let mut buf = &mut buf[..];
            buf.try_write_f64_le(n).unwrap();
        }
        buf == n.to_bits().to_le_bytes()
    }
}
