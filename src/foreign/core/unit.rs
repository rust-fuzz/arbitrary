use crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured};

impl<'a> Arbitrary<'a> for () {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(())
    }

    #[inline]
    fn size_hint(_depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(SizeHint::exactly(0))
    }
}
