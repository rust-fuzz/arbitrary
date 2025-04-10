use {
    crate::{size_hint, Arbitrary, Result, SizeHint, Unstructured},
    core::iter::{empty, Empty},
};

impl<'a, A> Arbitrary<'a> for Empty<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(empty())
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(0)
    }
}
