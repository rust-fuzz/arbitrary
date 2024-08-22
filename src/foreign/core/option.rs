use crate::{size_hint, Arbitrary, Result, Unstructured};

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
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(
            <bool as Arbitrary>::size_hint(depth),
            size_hint::or((0, Some(0)), <A as Arbitrary>::size_hint(depth)),
        )
    }
}
