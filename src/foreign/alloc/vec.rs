use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::vec::Vec,
};

impl<'a, A> Arbitrary<'a> for Vec<A>
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
