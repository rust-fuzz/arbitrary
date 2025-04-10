use crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured};

impl<'a> Arbitrary<'a> for bool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(<u8 as Arbitrary<'a>>::arbitrary(u)? & 1 == 1)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        <u8 as Arbitrary<'a>>::size_hint(depth)
    }
}
