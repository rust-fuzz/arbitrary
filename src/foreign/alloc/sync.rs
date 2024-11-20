use {
    crate::{Arbitrary, Result, Unstructured},
    std::sync::Arc,
};

implement_wrapped_new! { Arc! }
implement_from_iter! { Arc<[A]> }

impl<'a> Arbitrary<'a> for Arc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}
