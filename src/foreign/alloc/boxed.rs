use {
    crate::{Arbitrary, Result, Unstructured},
    std::boxed::Box,
};

implement_wrapped_new! { Box! }
implement_from_iter! { Box<[A]> }

impl<'a> Arbitrary<'a> for Box<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <String as Arbitrary>::size_hint(depth)
    }
}
