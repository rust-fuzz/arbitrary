use {
    crate::{size_hint, Arbitrary, ArbitraryInRange, Result, Unstructured},
    core::{
        ops::{Bound, RangeBounds},
        time::Duration,
    },
};

const MAX_NANOS: u32 = 999_999_999;

fn split_duration(duration: &Duration) -> (u64, u32) {
    (
        duration.as_secs(),
        // We can assume, that this is always in the range 0–MAX_NANOS
        duration.subsec_nanos(),
    )
}

fn split_bound_duration(duration: Bound<&Duration>) -> (Bound<u64>, Bound<u32>) {
    match duration {
        Bound::Included(duration) => {
            let (secs, nanos) = split_duration(duration);
            (Bound::Included(secs), Bound::Included(nanos))
        }
        Bound::Excluded(duration) => {
            let (secs, nanos) = split_duration(duration);
            (Bound::Excluded(secs), Bound::Excluded(nanos))
        }
        Bound::Unbounded => (Bound::Unbounded, Bound::Unbounded),
    }
}

impl<'a> ArbitraryInRange<'a> for Duration {
    type Bound = Self;

    fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
    where
        R: RangeBounds<Self::Bound>,
    {
        let (start_secs, start_nanos) = split_bound_duration(range.start_bound());
        let (end_secs, end_nanos) = split_bound_duration(range.end_bound());
        let secs = u64::arbitrary_in_range(u, &(start_secs, end_secs))?;

        // If secs is not the minimum, nanos can start at 0.
        let start_nanos = match start_secs {
            Bound::Included(start_secs) => (secs == start_secs).then_some(start_nanos),
            Bound::Excluded(start_secs) => (secs == start_secs + 1).then_some(start_nanos),
            // If start_secs is unbounded, start_nanos is too
            Bound::Unbounded => None,
        };
        let start_nanos = start_nanos.unwrap_or(Bound::Unbounded);

        // If secs is not the maximum, nanos can end at 999_999_999.
        let end_nanos = match end_secs {
            Bound::Included(end_secs) => (end_secs == secs).then_some(end_nanos),
            Bound::Excluded(end_secs) => (end_secs == secs + 1).then_some(end_nanos),
            // If end_secs is unbounded, end_nanos is too
            Bound::Unbounded => None,
        };
        let end_nanos = end_nanos.unwrap_or(Bound::Included(MAX_NANOS));

        let nanos = u32::arbitrary_in_range(u, &(start_nanos, end_nanos))?;

        Ok(Self::new(secs, nanos))
    }
}
impl<'a> Arbitrary<'a> for Duration {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self::new(
            <u64 as Arbitrary>::arbitrary(u)?,
            u.int_in_range(0..=MAX_NANOS)?,
        ))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(
            <u64 as Arbitrary>::size_hint(depth),
            <u32 as Arbitrary>::size_hint(depth),
        )
    }
}
