use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::string::String,
};

impl<'a> Arbitrary<'a> for String {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary_take_rest(u).map(Into::into)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <&str as Arbitrary>::size_hint(context)
    }
}
