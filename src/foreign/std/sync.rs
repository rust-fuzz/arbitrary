use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::sync::Mutex,
};

impl<'a, A> Arbitrary<'a> for Mutex<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<A>()
    }
}
