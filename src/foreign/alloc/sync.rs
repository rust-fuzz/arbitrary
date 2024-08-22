use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::sync::Arc,
};

impl<'a, A> Arbitrary<'a> for Arc<A>
where
    A: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A> Arbitrary<'a> for Arc<[A]>
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
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for Arc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}
