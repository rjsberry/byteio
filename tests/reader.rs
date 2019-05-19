use byteio::{ReadBytes, Reader};

use quickcheck::TestResult;
use quickcheck_macros::quickcheck;

#[quickcheck]
fn reader_read_chunks(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
    if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
        return TestResult::discard();
    }

    let len = src.len();
    let mut reader = Reader::new(&*src);
    let mut sink = Vec::with_capacity(len);

    for n in chunks.iter().map(|n| usize::from(*n)) {
        sink.extend_from_slice(reader.read_exact(n));
    }

    let read = reader.num_bytes_read();
    let inner = reader.into_inner();

    TestResult::from_bool(inner.is_empty() && read == len && sink == src)
}

#[quickcheck]
fn reader_try_read_chunks(src: Vec<u8>, chunks: Vec<u8>) -> TestResult {
    if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
        return TestResult::discard();
    }

    let len = src.len();
    let mut reader = Reader::new(&*src);
    let mut sink = Vec::with_capacity(len);

    for n in chunks.iter().map(|n| usize::from(*n)) {
        sink.extend_from_slice(reader.try_read_exact(n).unwrap());
    }

    let read = reader.num_bytes_read();
    let inner = reader.into_inner();

    TestResult::from_bool(inner.is_empty() && read == len && sink == src)
}
