macro_rules! _impl_qc_reader {
    (& $( $mut:ident )? [u8], $src:expr, $chunks:expr, $reader:tt) => {
        if $src.len() != $chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
            TestResult::discard()
        } else {
            let len = $src.len();
            let mut reader: Reader<& $( $mut )? [u8]> = Reader::new(& $( $mut )? *$src);
            let mut sink = Vec::with_capacity(len);

            for n in $chunks.iter().map(|n| usize::from(*n)) {
                // hack: macro avoids multiple mutable borrows
                sink.extend_from_slice($reader!(reader, n));
            }

            let read = reader.num_bytes_read();
            let inner = reader.into_inner();

            TestResult::from_bool(inner.is_empty() && read == len && sink == $src)
        }
    };
}

macro_rules! _read_exact {
    ($reader:expr, $n:expr) => {
        $reader.read_exact($n)
    };
}

macro_rules! _try_read_exact {
    ($reader:expr, $n:expr) => {
        $reader.try_read_exact($n).unwrap()
    };
}

mod slice {
    use byteio::{ReadBytes, Reader};

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_reader(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        _impl_qc_reader!(&[u8], src, chunks, _read_exact)
    }

    #[quickcheck]
    fn qc_reader_try(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        _impl_qc_reader!(&[u8], src, chunks, _try_read_exact)
    }
}

mod mut_slice {
    use byteio::{ReadBytes, Reader};

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_reader(mut src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        _impl_qc_reader!(&mut [u8], src, chunks, _read_exact)
    }

    #[quickcheck]
    fn qc_reader_try(mut src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
        _impl_qc_reader!(&mut [u8], src, chunks, _try_read_exact)
    }
}
