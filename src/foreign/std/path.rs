use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::{ffi::OsString, path::PathBuf},
};

impl<'a> Arbitrary<'a> for PathBuf {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <OsString as Arbitrary>::arbitrary(u).map(From::from)
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        <OsString as Arbitrary>::size_hint(context)
    }
}
