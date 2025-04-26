use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
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
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<A>()
    }
}
