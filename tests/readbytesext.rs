macro_rules! _impl_read_test {
    ($ty:ty, $test:ident, $fn:ident, $to_endian:ident) => {
        #[quickcheck]
        fn $test(n: $ty) -> bool {
            let mut buf: &[u8] = &n.$to_endian();
            buf.$fn() == n
        }
    };
}

macro_rules! _impl_try_read_test {
    ($ty:ty, $test:ident, $fn:ident, $to_endian:ident) => {
        #[quickcheck]
        fn $test(n: $ty) -> bool {
            let mut buf: &[u8] = &n.$to_endian();
            buf.$fn().unwrap() == n
        }
    };
}

mod be {
    use byteio::ReadBytesExt;

    use quickcheck_macros::quickcheck;

    macro_rules! impl_read_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_read_test!($ty, $test, $fn, to_be_bytes);
        };
    }

    macro_rules! impl_try_read_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_try_read_test!($ty, $test, $fn, to_be_bytes);
        };
    }

    #[quickcheck]
    fn qc_read_u8(n: u8) -> bool {
        let mut buf: &[u8] = &n.to_be_bytes();
        buf.read_u8() == n
    }

    #[quickcheck]
    fn qc_try_read_u8(n: u8) -> bool {
        let mut buf: &[u8] = &n.to_be_bytes();
        buf.try_read_u8().unwrap() == n
    }

    #[quickcheck]
    fn qc_read_i8(n: i8) -> bool {
        let mut buf: &[u8] = &n.to_be_bytes();
        buf.read_i8() == n
    }

    #[quickcheck]
    fn qc_try_read_i8(n: i8) -> bool {
        let mut buf: &[u8] = &n.to_be_bytes();
        buf.try_read_i8().unwrap() == n
    }

    impl_read_test!(u16, qc_read_u16, read_u16_be);
    impl_try_read_test!(u16, qc_try_read_u16, try_read_u16_be);

    impl_read_test!(i16, qc_read_i16, read_i16_be);
    impl_try_read_test!(i16, qc_try_read_i16, try_read_i16_be);

    impl_read_test!(u32, qc_read_u32, read_u32_be);
    impl_try_read_test!(u32, qc_try_read_u32, try_read_u32_be);

    impl_read_test!(i32, qc_read_i32, read_i32_be);
    impl_try_read_test!(i32, qc_try_read_i32, try_read_i32_be);

    impl_read_test!(u64, qc_read_u64, read_u64_be);
    impl_try_read_test!(u64, qc_try_read_u64, try_read_u64_be);

    impl_read_test!(i64, qc_read_i64, read_i64_be);
    impl_try_read_test!(i64, qc_try_read_i64, try_read_i64_be);

    impl_read_test!(u128, qc_read_u128, read_u128_be);
    impl_try_read_test!(u128, qc_try_read_u128, try_read_u128_be);

    impl_read_test!(i128, qc_read_i128, read_i128_be);
    impl_try_read_test!(i128, qc_try_read_i128, try_read_i128_be);

    #[quickcheck]
    fn qc_read_f32(n: f32) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_be_bytes();
        buf.read_f32_be() == n
    }

    #[quickcheck]
    fn qc_try_read_f32(n: f32) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_be_bytes();
        buf.read_f32_be() == n
    }

    #[quickcheck]
    fn qc_read_f64(n: f64) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_be_bytes();
        buf.read_f64_be() == n
    }

    #[quickcheck]
    fn qc_try_read_f64(n: f64) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_be_bytes();
        buf.read_f64_be() == n
    }
}

mod le {
    use byteio::ReadBytesExt;

    use quickcheck_macros::quickcheck;

    macro_rules! impl_read_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_read_test!($ty, $test, $fn, to_le_bytes);
        };
    }

    macro_rules! impl_try_read_test {
        ($ty:ty, $test:ident, $fn:ident) => {
            _impl_try_read_test!($ty, $test, $fn, to_le_bytes);
        };
    }

    #[quickcheck]
    fn qc_read_u8(n: u8) -> bool {
        let mut buf: &[u8] = &n.to_le_bytes();
        buf.read_u8() == n
    }

    #[quickcheck]
    fn qc_try_read_u8(n: u8) -> bool {
        let mut buf: &[u8] = &n.to_le_bytes();
        buf.try_read_u8().unwrap() == n
    }

    #[quickcheck]
    fn qc_read_i8(n: i8) -> bool {
        let mut buf: &[u8] = &n.to_le_bytes();
        buf.read_i8() == n
    }

    #[quickcheck]
    fn qc_try_read_i8(n: i8) -> bool {
        let mut buf: &[u8] = &n.to_le_bytes();
        buf.try_read_i8().unwrap() == n
    }

    impl_read_test!(u16, qc_read_u16, read_u16_le);
    impl_try_read_test!(u16, qc_try_read_u16, try_read_u16_le);

    impl_read_test!(i16, qc_read_i16, read_i16_le);
    impl_try_read_test!(i16, qc_try_read_i16, try_read_i16_le);

    impl_read_test!(u32, qc_read_u32, read_u32_le);
    impl_try_read_test!(u32, qc_try_read_u32, try_read_u32_le);

    impl_read_test!(i32, qc_read_i32, read_i32_le);
    impl_try_read_test!(i32, qc_try_read_i32, try_read_i32_le);

    impl_read_test!(u64, qc_read_u64, read_u64_le);
    impl_try_read_test!(u64, qc_try_read_u64, try_read_u64_le);

    impl_read_test!(i64, qc_read_i64, read_i64_le);
    impl_try_read_test!(i64, qc_try_read_i64, try_read_i64_le);

    impl_read_test!(u128, qc_read_u128, read_u128_le);
    impl_try_read_test!(u128, qc_try_read_u128, try_read_u128_le);

    impl_read_test!(i128, qc_read_i128, read_i128_le);
    impl_try_read_test!(i128, qc_try_read_i128, try_read_i128_le);

    #[quickcheck]
    fn qc_read_f32(n: f32) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_le_bytes();
        buf.read_f32_le() == n
    }

    #[quickcheck]
    fn qc_try_read_f32(n: f32) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_le_bytes();
        buf.read_f32_le() == n
    }

    #[quickcheck]
    fn qc_read_f64(n: f64) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_le_bytes();
        buf.read_f64_le() == n
    }

    #[quickcheck]
    fn qc_try_read_f64(n: f64) -> bool {
        let mut buf: &[u8] = &n.to_bits().to_le_bytes();
        buf.read_f64_le() == n
    }
}
