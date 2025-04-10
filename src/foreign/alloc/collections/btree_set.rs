use {
    crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured},
    std::collections::btree_set::BTreeSet,
};

impl<'a, A> Arbitrary<'a> for BTreeSet<A>
where
    A: Arbitrary<'a> + Ord,
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
