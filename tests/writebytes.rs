mod mut_slice {
    use byteio::WriteBytes;

    use itertools::Itertools;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_write_exact_not_enough_bytes(src: Vec<u8>) -> TestResult {
        if src.is_empty() {
            return TestResult::discard();
        }

        let mut dst = vec![0; src.len() - 1];
        let src: &[u8] = &*src;
        let mut dst: &mut [u8] = &mut *dst;

        dst.write_exact(src);

        TestResult::from_bool(true)
    }

    #[quickcheck]
    fn qc_try_write_exact_not_enough_bytes(src: Vec<u8>) -> TestResult {
        if src.is_empty() {
            return TestResult::discard();
        }

        let mut dst = vec![0; src.len() - 1];
        let src: &[u8] = &*src;
        let mut dst: &mut [u8] = &mut *dst;

        TestResult::from_bool(dst.try_write_exact(src).unwrap_err() == byteio::Error::EndOfStream)
    }

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let src: &[u8] = &*src;
        let mut writer: &mut [u8] = &mut *dst;

        writer.write_exact(src);

        writer.is_empty() && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let src: &[u8] = &*src;
        let mut writer: &mut [u8] = &mut *dst;

        writer.try_write_exact(src).unwrap();

        writer.is_empty() && dst == src
    }

    #[quickcheck]
    fn qc_write_exact_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let mut dst = vec![0; src.len()];
        let src: &[u8] = &*src;
        let mut writer: &mut [u8] = &mut *dst;

        for chunk in src.into_iter().batching(|it| {
            chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
        }) {
            writer.write_exact(&*chunk);
        }

        TestResult::from_bool(writer.is_empty() && dst == src)
    }

    #[quickcheck]
    fn qc_try_write_exact_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let mut dst = vec![0; src.len()];
        let src: &[u8] = &*src;
        let mut writer: &mut [u8] = &mut *dst;

        for chunk in src.into_iter().batching(|it| {
            chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
        }) {
            writer.try_write_exact(&*chunk).unwrap();
        }

        TestResult::from_bool(writer.is_empty() && dst == src)
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
mod mut_vec_ref {
    use byteio::WriteBytes;

    use itertools::Itertools;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let src: &[u8] = &*src;

        (&mut dst).write_exact(src);

        dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let src: &[u8] = &*src;

        (&mut dst).try_write_exact(src).unwrap();

        dst == src
    }

    #[quickcheck]
    fn qc_write_exact_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let mut dst = Vec::with_capacity(src.len());
        let src: &[u8] = &*src;

        for chunk in src.into_iter().batching(|it| {
            chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
        }) {
            (&mut dst).write_exact(&*chunk);
        }

        TestResult::from_bool(dst == src)
    }

    #[quickcheck]
    fn qc_try_write_exact_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            return TestResult::discard();
        }

        let mut dst = Vec::with_capacity(src.len());
        let src: &[u8] = &*src;

        for chunk in src.into_iter().batching(|it| {
            chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
        }) {
            (&mut dst).try_write_exact(&*chunk).unwrap();
        }

        TestResult::from_bool(dst == src)
    }
}
