#![no_main]

use arbitrary::{unstructured::Int, Arbitrary, Result, Unstructured};
use libfuzzer_sys::fuzz_target;
use std::{fmt::Display, ops::RangeInclusive};

fuzz_target!(|data: &[u8]| {
    fuzz(data).expect("`int_in_range` should never return an error");
});

fn fuzz(data: &[u8]) -> Result<()> {
    let mut u = Unstructured::new(data);

    let choices = [
        assert_in_range::<u8, 1>,
        assert_in_range::<i8, 1>,
        assert_in_range::<u16, 2>,
        assert_in_range::<i16, 2>,
        assert_in_range::<u32, 4>,
        assert_in_range::<i32, 4>,
        assert_in_range::<u64, 8>,
        assert_in_range::<i64, 8>,
        assert_in_range::<u64, 8>,
        assert_in_range::<i64, 8>,
        assert_in_range::<u128, 16>,
        assert_in_range::<i128, 16>,
    ];

    let f = u.choose(&choices[..])?;
    f(&mut u)
}

fn assert_in_range<'a, 'b, T, const BYTES: usize>(u: &'a mut Unstructured<'b>) -> Result<()>
where
    T: Arbitrary<'b> + Int<BYTES> + Display,
{
    let range = RangeInclusive::<T>::arbitrary(u)?;
    let start = *range.start();
    let end = *range.end();

    let x = u.int_in_range(range)?;

    if start <= x && x <= end {
        return Ok(());
    }

    let ty = std::any::type_name::<T>();
    panic!("{ty}: {x} is not within {start}..={end}",);
}
