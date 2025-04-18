use {
    crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured},
    std::{ffi::OsString, path::PathBuf},
};

impl<'a> Arbitrary<'a> for PathBuf {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <OsString as Arbitrary>::arbitrary(u).map(From::from)
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        <OsString as Arbitrary>::size_hint(depth)
    }
}
