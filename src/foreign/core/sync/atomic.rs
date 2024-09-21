use {
    crate::{Arbitrary, ArbitraryInRange, Result, Unstructured},
    core::sync::atomic::{
        AtomicBool, AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicU16, AtomicU32,
        AtomicU64, AtomicU8, AtomicUsize,
    },
};

impl<'a> Arbitrary<'a> for AtomicBool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <bool as Arbitrary<'a>>::size_hint(depth)
    }
}

implement_new! { AtomicI8: i8 }
implement_new! { AtomicI16: i16 }
implement_new! { AtomicI32: i32 }
implement_new! { AtomicI64: i64 }
implement_new! { AtomicIsize: isize }
implement_new! { AtomicU8: u8 }
implement_new! { AtomicU16: u16 }
implement_new! { AtomicU32: u32 }
implement_new! { AtomicU64: u64 }
implement_new! { AtomicUsize: usize }
