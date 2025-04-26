use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
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
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <<A as ToOwned>::Owned as Arbitrary>::size_hint(context)
    }
}
