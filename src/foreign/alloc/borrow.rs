use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::borrow::{Cow, ToOwned},
};

impl<'a, A> Arbitrary<'a> for Cow<'a, A>
where
    A: ToOwned + ?Sized,
    <A as ToOwned>::Owned: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::recursion_guard(depth, |depth| {
            <<A as ToOwned>::Owned as Arbitrary>::size_hint(depth)
        })
    }
}
