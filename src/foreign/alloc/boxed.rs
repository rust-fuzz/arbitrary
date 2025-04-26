use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::boxed::Box,
};

impl<'a, A> Arbitrary<'a> for Box<A>
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

impl<'a, A> Arbitrary<'a> for Box<[A]>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        size_hint::SizeHint::at_least(0)
    }
}

impl<'a> Arbitrary<'a> for Box<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        // known non-recursive
        <String as Arbitrary>::size_hint(context)
    }
}
