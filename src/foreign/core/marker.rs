use {
    crate::{size_hint, Arbitrary, Result, SizeHint, Unstructured},
    core::marker::{PhantomData, PhantomPinned},
};

impl<'a, A> Arbitrary<'a> for PhantomData<A>
where
    A: ?Sized,
{
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(PhantomData)
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(0)
    }
}

impl<'a> Arbitrary<'a> for PhantomPinned {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(PhantomPinned)
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(0)
    }
}
