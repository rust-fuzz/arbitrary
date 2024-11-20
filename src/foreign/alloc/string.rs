use {
    crate::{Arbitrary, ArbitraryInRange, Result, Unstructured},
    std::{ops::RangeBounds, string::String},
};

impl<'a> ArbitraryInRange<'a> for String {
    type Bound = char;

    fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
    where
        R: RangeBounds<Self::Bound>,
    {
        u.arbitrary_in_range_iter::<Self::Bound, _>(range)?
            .collect()
    }
}

impl<'a> Arbitrary<'a> for String {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary_take_rest(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}
