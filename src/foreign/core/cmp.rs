use {
    crate::{Arbitrary, Result, SizeHint, Unstructured},
    core::cmp::Reverse,
};

impl<'a, A> Arbitrary<'a> for Reverse<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, crate::MaxRecursionReached> {
        SizeHint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}
