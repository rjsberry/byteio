mod slice {
    use byteio::ReadBytes;

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let len = src.len();
        let mut src: &[u8] = &*src;

        let _ = src.read_exact(len + 1);

        true
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let len = src.len();
        let mut src: &[u8] = &*src;

        src.try_read_exact(len + 1).is_err()
    }

    #[quickcheck]
    fn qc_read_exact(src: Vec<u8>) -> bool {
        let len = src.len();
        let mut reader: &[u8] = &*src;

        let bytes = reader.read_exact(len);

        reader.is_empty() && bytes.to_vec() == src
    }

    #[quickcheck]
    fn qc_try_read_exact(src: Vec<u8>) -> bool {
        let len = src.len();
        let mut reader: &[u8] = &*src;

        let bytes = reader.try_read_exact(len).unwrap();

        reader.is_empty() && bytes.to_vec() == src
    }

    #[quickcheck]
    fn qc_read_exact_chunks(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let len = src.len();
        let mut reader: &[u8] = &*src;
        let mut sink = Vec::with_capacity(len);

        for n in chunks.iter().map(|n| usize::from(*n)) {
            sink.extend_from_slice(reader.read_exact(n));
        }

        TestResult::from_bool(reader.is_empty() && sink == src)
    }

    #[quickcheck]
    fn qc_try_read_exact_chunks(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let len = src.len();
        let mut reader: &[u8] = &*src;
        let mut sink = Vec::with_capacity(len);

        for n in chunks.iter().map(|n| usize::from(*n)) {
            sink.extend_from_slice(reader.try_read_exact(n).unwrap());
        }

        TestResult::from_bool(reader.is_empty() && sink == src)
    }
}

mod mut_slice {
    use byteio::ReadBytes;

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(mut src: Vec<u8>) -> bool {
        let len = src.len();
        let mut src: &mut [u8] = &mut *src;

        let _ = src.read_exact(len + 1);

        true
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(mut src: Vec<u8>) -> bool {
        let len = src.len();
        let mut src: &mut [u8] = &mut *src;

        src.try_read_exact(len + 1).is_err()
    }

    #[quickcheck]
    fn qc_read_exact(mut src: Vec<u8>) -> bool {
        let len = src.len();
        let mut reader: &mut [u8] = &mut *src;

        let bytes = reader.read_exact(len);

        reader.is_empty() && bytes.to_vec() == src
    }

    #[quickcheck]
    fn qc_try_read_exact(mut src: Vec<u8>) -> bool {
        let len = src.len();
        let mut reader: &mut [u8] = &mut *src;

        let bytes = reader.try_read_exact(len).unwrap();

        reader.is_empty() && bytes.to_vec() == src
    }

    #[quickcheck]
    fn qc_read_exact_chunks(mut src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let len = src.len();
        let mut reader: &mut [u8] = &mut *src;
        let mut sink = Vec::with_capacity(len);

        for n in chunks.iter().map(|n| usize::from(*n)) {
            sink.extend_from_slice(reader.read_exact(n));
        }

        TestResult::from_bool(reader.is_empty() && sink == src)
    }

    #[quickcheck]
    fn qc_try_read_exact_chunks(mut src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let len = src.len();
        let mut reader: &mut [u8] = &mut *src;
        let mut sink = Vec::with_capacity(len);

        for n in chunks.iter().map(|n| usize::from(*n)) {
            sink.extend_from_slice(reader.try_read_exact(n).unwrap());
        }

        TestResult::from_bool(reader.is_empty() && sink == src)
    }
}
