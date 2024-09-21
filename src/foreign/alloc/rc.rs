use {
    crate::{Arbitrary, Result, Unstructured},
    std::rc::Rc,
};

implement_wrapped_new! { Rc! }
implement_from_iter! { Rc<[A]> }

impl<'a> Arbitrary<'a> for Rc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}
