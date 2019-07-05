use byteio::WriteBytes;

fn check_write_exact_not_enough_bytes<W: WriteBytes>(mut src: Vec<u8>, mut writer: W) {
    src.push(0);
    writer.write_exact(&src);
}

fn check_try_write_exact_not_enough_bytes<W: WriteBytes>(mut src: Vec<u8>, mut writer: W) -> bool {
    src.push(0);
    writer.try_write_exact(&src).unwrap_err() == ::byteio::Error::EndOfStream
}

fn check_write_exact<W: WriteBytes, F: Fn(W) -> bool>(src: &[u8], mut writer: W, test: F) -> bool {
    writer.write_exact(src);
    test(writer)
}

fn check_try_write_exact<W: WriteBytes, F: Fn(W) -> bool>(
    src: &[u8],
    mut writer: W,
    test: F,
) -> bool {
    writer.try_write_exact(src).unwrap();
    test(writer)
}

mod mut_slice {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_write_exact_not_enough_bytes(src: Vec<u8>) {
        let mut src2 = src.clone();
        let writer: &mut [u8] = &mut src2;

        check_write_exact_not_enough_bytes(src, writer)
    }

    #[quickcheck]
    fn qc_try_write_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let writer: &mut [u8] = &mut src2;

        check_try_write_exact_not_enough_bytes(src, writer)
    }

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut [u8] = &mut dst;

        check_write_exact(&src, writer, |w| w.as_mut().is_empty()) && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut [u8] = &mut dst;

        check_try_write_exact(&src, writer, |w| w.as_mut().is_empty()) && dst == src
    }
}

mod mut_slice_mut_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_write_exact_not_enough_bytes(src: Vec<u8>) {
        let mut src2 = src.clone();
        let writer: &mut &mut [u8] = &mut &mut *src2;

        check_write_exact_not_enough_bytes(src, writer)
    }

    #[quickcheck]
    fn qc_try_write_exact_not_enough_bytes(src: Vec<u8>) -> bool {
        let mut src2 = src.clone();
        let writer: &mut &mut [u8] = &mut &mut *src2;

        check_try_write_exact_not_enough_bytes(src, writer)
    }

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut &mut [u8] = &mut &mut *dst;

        check_write_exact(&src, writer, |w| w.as_mut().is_empty()) && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut &mut [u8] = &mut &mut *dst;

        check_try_write_exact(&src, writer, |w| w.as_mut().is_empty()) && dst == src
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
mod mut_vec_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let writer: &mut Vec<u8> = &mut dst;

        check_write_exact(&src, writer, |w| AsMut::<[u8]>::as_mut(w).len() == src.len())
            && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let writer: &mut Vec<u8> = &mut dst;

        check_try_write_exact(&src, writer, |w| AsMut::<[u8]>::as_mut(w).len() == src.len())
            && dst == src
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
mod mut_vec_ref_mut_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let writer: &mut &mut Vec<u8> = &mut &mut dst;

        check_write_exact(&src, writer, |w| AsMut::<[u8]>::as_mut(w).len() == src.len())
            && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let writer: &mut &mut Vec<u8> = &mut &mut dst;

        check_try_write_exact(&src, writer, |w| AsMut::<[u8]>::as_mut(w).len() == src.len())
            && dst == src
    }
}
