use byteio::WriteBytes;

mod mut_slice {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_write_exact_not_enough_bytes(mut src: Vec<u8>) {
        let mut dst = vec![0; src.len()];
        src.push(0);
        let mut writer: &mut [u8] = &mut dst;
        writer.write_exact(&src);
    }

    #[quickcheck]
    fn qc_try_write_exact_not_enough_bytes(mut src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        src.push(0);
        let mut writer: &mut [u8] = &mut dst;
        writer.try_write_exact(&src).is_err()
    }

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let mut writer: &mut [u8] = &mut dst;
        writer.write_exact(&src);
        writer.as_ref().is_empty() && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let mut writer: &mut [u8] = &mut dst;
        writer.try_write_exact(&src).unwrap();
        writer.as_ref().is_empty() && dst == src
    }
}

mod mut_slice_mut_ref {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[should_panic]
    fn qc_write_exact_not_enough_bytes(mut src: Vec<u8>) {
        let mut dst = vec![0; src.len()];
        src.push(0);
        let writer: &mut &mut [u8] = &mut &mut *dst;
        writer.write_exact(&src);
    }

    #[quickcheck]
    fn qc_try_write_exact_not_enough_bytes(mut src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        src.push(0);
        let writer: &mut &mut [u8] = &mut &mut *dst;
        writer.try_write_exact(&src).is_err()
    }

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut &mut [u8] = &mut &mut *dst;
        writer.write_exact(&src);
        writer.as_ref().is_empty() && dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = vec![0; src.len()];
        let writer: &mut &mut [u8] = &mut &mut *dst;
        writer.try_write_exact(&src).unwrap();
        writer.as_ref().is_empty() && dst == src
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
mod vec {
    use super::*;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn qc_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        dst.write_exact(&*src);
        dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        dst.try_write_exact(&*src).unwrap();
        dst == src
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
        writer.write_exact(&src);
        dst == src
    }

    #[quickcheck]
    fn qc_try_write_exact(src: Vec<u8>) -> bool {
        let mut dst = Vec::with_capacity(src.len());
        let writer: &mut Vec<u8> = &mut dst;
        writer.try_write_exact(&src).unwrap();
        dst == src
    }
}
