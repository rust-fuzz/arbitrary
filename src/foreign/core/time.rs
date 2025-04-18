use {
    crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured},
    core::time::Duration,
};

/// Returns zero, not an error, if this `Unstructured` [is empty][Unstructured::is_empty].
impl<'a> Arbitrary<'a> for Duration {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self::new(
            <u64 as Arbitrary>::arbitrary(u)?,
            u.int_in_range(0..=999_999_999)?,
        ))
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(<u64 as Arbitrary>::size_hint(depth)? + <u32 as Arbitrary>::size_hint(depth)?)
    }
}
