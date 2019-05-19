use byteio::{WriteBytes, Writer};

use itertools::Itertools;
use quickcheck::TestResult;
use quickcheck_macros::quickcheck;

#[quickcheck]
fn writer_write_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
    if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
        return TestResult::discard();
    }

    let len = src.len();
    let mut dst = vec![0; len];
    let src: &[u8] = &*src;
    let mut writer = Writer::new(&mut *dst);

    for chunk in src.into_iter().batching(|it| {
        chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
    }) {
        writer.write_exact(&*chunk);
    }

    let written = writer.num_bytes_written();
    let inner = writer.into_inner();

    TestResult::from_bool(inner.is_empty() && written == len && dst == src)
}

#[quickcheck]
fn writer_try_write_chunks(src: Vec<u8>, mut chunks: Vec<u8>) -> TestResult {
    if src.len() != chunks.iter().fold(0_usize, |acc, n| acc + usize::from(*n)) {
        return TestResult::discard();
    }

    let len = src.len();
    let mut dst = vec![0; len];
    let src: &[u8] = &*src;
    let mut writer = Writer::new(&mut *dst);

    for chunk in src.into_iter().batching(|it| {
        chunks.pop().map(|c| it.take(usize::from(c)).map(|n| *n).collect::<Vec<_>>())
    }) {
        writer.try_write_exact(&*chunk).unwrap();
    }

    let written = writer.num_bytes_written();
    let inner = writer.into_inner();

    TestResult::from_bool(inner.is_empty() && written == len && dst == src)
}
