use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    core::cell::{Cell, RefCell, UnsafeCell},
};

impl<'a, A> Arbitrary<'a> for Cell<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <A as Arbitrary<'a>>::size_hint(context)
    }
}

impl<'a, A> Arbitrary<'a> for RefCell<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <A as Arbitrary<'a>>::size_hint(context)
    }
}

impl<'a, A> Arbitrary<'a> for UnsafeCell<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <A as Arbitrary<'a>>::size_hint(context)
    }
}
