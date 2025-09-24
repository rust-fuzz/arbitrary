#![no_main]

use arbitrary::{unstructured::Int, Arbitrary, Result, Unstructured};
use core::{fmt::Display, ops::RangeInclusive};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    fuzz(data).expect("`int_in_range` should never return an error");
});

fn fuzz(data: &[u8]) -> Result<()> {
    let mut u = Unstructured::new(data);

    let choices = [
        assert_in_range::<u8>,
        assert_in_range::<i8>,
        assert_in_range::<u16>,
        assert_in_range::<i16>,
        assert_in_range::<u32>,
        assert_in_range::<i32>,
        assert_in_range::<u64>,
        assert_in_range::<i64>,
        assert_in_range::<u64>,
        assert_in_range::<i64>,
        assert_in_range::<u128>,
        assert_in_range::<i128>,
    ];

    let f = u.choose(&choices[..])?;
    f(&mut u)
}

fn assert_in_range<'a, 'b, T>(u: &'a mut Unstructured<'b>) -> Result<()>
where
    T: Arbitrary<'b> + Int + Display,
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
