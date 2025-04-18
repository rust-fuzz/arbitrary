use {
    crate::{Arbitrary, Result, SizeHint, Unstructured},
    std::borrow::{Cow, ToOwned},
};

impl<'a, A> Arbitrary<'a> for Cow<'a, A>
where
    A: ToOwned + ?Sized + 'a,
    <A as ToOwned>::Owned: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, crate::MaxRecursionReached> {
        SizeHint::recursion_guard(depth, |depth| {
            <<A as ToOwned>::Owned as Arbitrary>::size_hint(depth)
        })
    }
}
