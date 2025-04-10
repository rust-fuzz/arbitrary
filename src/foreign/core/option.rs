use crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured};

impl<'a, A> Arbitrary<'a> for Option<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(if <bool as Arbitrary<'a>>::arbitrary(u)? {
            Some(Arbitrary::arbitrary(u)?)
        } else {
            None
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(<bool as Arbitrary>::size_hint(depth)?
            + (SizeHint::exactly(0) | <A as Arbitrary>::size_hint(depth)?))
    }
}
