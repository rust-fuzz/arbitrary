use {
    crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured},
    std::rc::Rc,
};

impl<'a, A> Arbitrary<'a> for Rc<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, crate::MaxRecursionReached> {
        SizeHint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A> Arbitrary<'a> for Rc<[A]>
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
    fn size_hint(_depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(SizeHint::at_least(0))
    }
}

impl<'a> Arbitrary<'a> for Rc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        <&str as Arbitrary>::size_hint(depth)
    }
}
