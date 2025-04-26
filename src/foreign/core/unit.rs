use crate::{size_hint, Arbitrary, Result, SizeHint, Unstructured};

impl<'a> Arbitrary<'a> for () {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(())
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(0)
    }
}
