use byteio::ReadBytes;

fn check_read_exact_not_enough_bytes<'a, R: ReadBytes<'a>>(src: &[u8], mut reader: R) {
    let len = src.len();
    let _ = reader.read_exact(len + 1);
}

fn check_try_read_exact_not_enough_bytes<'a, R: ReadBytes<'a>>(src: &[u8], mut reader: R) -> bool {
    let len = src.len();
    reader.try_read_exact(len + 1).unwrap_err() == ::byteio::Error::EndOfStream
}

fn check_read_exact<'a, R: ReadBytes<'a>>(src: &[u8], mut reader: R) -> bool {
    let len = src.len();
    let bytes = reader.read_exact(len);

    reader.as_ref().is_empty() && bytes.to_vec() == src
}

fn check_try_read_exact<'a, R: ReadBytes<'a>>(src: &[u8], mut reader: R) -> bool {
    let len = src.len();
    let bytes = reader.try_read_exact(len).unwrap();

    reader.as_ref().is_empty() && bytes.to_vec() == src
}

mod slice {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(src: Vec<u8>) {
        let reader: &[u8] = &*src;
        check_read_exact_not_enough_bytes(&src, reader);
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let reader: &[u8] = &*src;
        check_try_read_exact_not_enough_bytes(&src, reader)
    }

    #[quickcheck]
    fn qc_read_exact(src: Vec<u8>) -> bool {
        let reader: &[u8] = &*src;
        check_read_exact(&src, reader)
    }

    #[quickcheck]
    fn qc_try_read_exact(src: Vec<u8>) -> bool {
        let reader: &[u8] = &*src;
        check_try_read_exact(&src, reader)
    }
}

mod slice_mut_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(src: Vec<u8>) {
        let reader: &mut &[u8] = &mut &*src;
        check_read_exact_not_enough_bytes(&src, reader);
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let reader: &mut &[u8] = &mut &*src;
        check_try_read_exact_not_enough_bytes(&src, reader)
    }

    #[quickcheck]
    fn qc_read_exact(src: Vec<u8>) -> bool {
        let reader: &mut &[u8] = &mut &*src;
        check_read_exact(&src, reader)
    }

    #[quickcheck]
    fn qc_try_read_exact(src: Vec<u8>) -> bool {
        let reader: &mut &[u8] = &mut &*src;
        check_try_read_exact(&src, reader)
    }
}

mod mut_slice {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(src: Vec<u8>) {
        let mut src2 = src.clone();
        let reader: &mut [u8] = &mut *src2;

        check_read_exact_not_enough_bytes(&src, reader);
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut [u8] = &mut *src2;

        check_try_read_exact_not_enough_bytes(&src, reader)
    }

    #[quickcheck]
    fn qc_read_exact(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut [u8] = &mut *src2;

        check_read_exact(&src, reader)
    }

    #[quickcheck]
    fn qc_try_read_exact(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut [u8] = &mut *src2;

        check_try_read_exact(&src, reader)
    }
}

mod mut_slice_mut_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_read_exact_not_enough_bytes(src: Vec<u8>) {
        let mut src2 = src.clone();
        let reader: &mut &mut [u8] = &mut &mut *src2;

        check_read_exact_not_enough_bytes(&src, reader);
    }

    #[quickcheck]
    fn qc_try_read_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut &mut [u8] = &mut &mut *src2;

        check_try_read_exact_not_enough_bytes(&src, reader)
    }

    #[quickcheck]
    fn qc_read_exact(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut &mut [u8] = &mut &mut *src2;

        check_read_exact(&src, reader)
    }

    #[quickcheck]
    fn qc_try_read_exact(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let reader: &mut &mut [u8] = &mut &mut *src2;

        check_try_read_exact(&src, reader)
    }
}
