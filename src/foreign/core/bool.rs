use crate::{size_hint, Arbitrary, Result, Unstructured};

/// Returns false, not an error, if this `Unstructured` [is empty][Unstructured::is_empty].
impl<'a> Arbitrary<'a> for bool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(<u8 as Arbitrary<'a>>::arbitrary(u)? & 1 == 1)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <u8 as Arbitrary<'a>>::size_hint(context)
    }
}
