use {
    crate::{size_hint, Arbitrary, Result, Unstructured},
    std::ffi::CString,
};

impl<'a> Arbitrary<'a> for CString {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <Vec<u8> as Arbitrary>::arbitrary(u).map(|mut x| {
            x.retain(|&c| c != 0);
            // SAFETY: all zero bytes have been removed
            unsafe { Self::from_vec_unchecked(x) }
        })
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        // known non-recursive
        <Vec<u8> as Arbitrary>::size_hint(context)
    }
}
