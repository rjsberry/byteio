macro_rules! _impl_qc_writer {
    ($ty:ty, $src:expr, $chunks:expr, $dst:expr, $chunker:tt, $inner_validator:expr $( , )?) => {
        if $src.len() != $chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            TestResult::discard()
        } else {
            let len = $src.len();
            let mut dst = $dst;
            let src: &[u8] = &*$src;
            let mut writer: Writer<$ty> = Writer::new(&mut dst);

            for chunk in src.into_iter().batching(|it| {
                $chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
            }) {
                // hack: macro avoids multiple mutable borrows
                $chunker!(writer, chunk);
            }

            let written = writer.num_bytes_written();
            let inner = writer.into_inner();

            TestResult::from_bool($inner_validator(inner) && written == len && dst == src)
        }
    };
}

macro_rules! _write_exact {
    ($writer:expr, $chunk:expr) => {
        $writer.write_exact(&*$chunk);
    };
}

macro_rules! _try_write_exact {
    ($writer:expr, $chunk:expr) => {
        $writer.try_write_exact(&*$chunk).unwrap();
    };
}

mod mut_slice {
    #[cfg(feature = "std")]
    use std::{cmp, io};

    use byteio::{WriteBytes, Writer};

    use itertools::Itertools;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_writer(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        _impl_qc_writer!(
            &mut [u8],
            src,
            chunks,
            vec![0; src.len()],
            _write_exact,
            |inner: &mut [u8]| inner.is_empty(),
        )
    }

    #[quickcheck]
    fn qc_writer_try(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        _impl_qc_writer!(
            &mut [u8],
            src,
            chunks,
            vec![0; src.len()],
            _try_write_exact,
            |inner: &mut [u8]| inner.is_empty(),
        )
    }

    #[cfg(feature = "std")]
    #[quickcheck]
    fn qc_writer_io_write(mut src: Vec<u8>, dst: Vec<u8>) -> bool {
        let mut writer = Writer::new(&mut *src);
        <Writer<_> as io::Write>::write(&mut writer, &*dst).expect("io write");
        let n = cmp::min(src.len(), dst.len());

        &src[..n] == &dst[..n]
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
mod mut_vec_ref {
    #[cfg(feature = "std")]
    use std::{cmp, io};

    use byteio::{WriteBytes, Writer};

    use itertools::Itertools;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_writer(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        _impl_qc_writer!(&mut Vec<u8>, src, chunks, vec![], _write_exact, |inner: &mut [u8]| inner
            .to_vec()
            == src,)
    }

    #[quickcheck]
    fn qc_writer_try(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
        _impl_qc_writer!(
            &mut Vec<u8>,
            src,
            chunks,
            vec![],
            _try_write_exact,
            |inner: &mut [u8]| inner.to_vec() == src,
        )
    }

    #[cfg(feature = "std")]
    #[quickcheck]
    fn qc_writer_io_write(dst: Vec<u8>) -> bool {
        let mut src = Vec::with_capacity(dst.len());

        let mut writer = Writer::new(&mut src);
        <Writer<_> as io::Write>::write(&mut writer, &*dst).expect("io write");
        let n = cmp::min(src.len(), dst.len());

        &src[..n] == &dst[..n]
    }
}
