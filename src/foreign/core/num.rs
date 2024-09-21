use {
    crate::{Arbitrary, ArbitraryInRange, Error, MaxRecursionReached, Result, Unstructured},
    core::{
        mem,
        num::{
            NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
            NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, Saturating, Wrapping,
        },
        ops::{Bound, RangeBounds},
    },
};

#[inline]
fn map_bound<T, U, F>(bound: Bound<T>, f: F) -> Bound<U>
where
    F: FnOnce(T) -> U,
{
    match bound {
        Bound::Included(bound) => Bound::Included(f(bound)),
        Bound::Excluded(bound) => Bound::Excluded(f(bound)),
        Bound::Unbounded => Bound::Unbounded,
    }
}

macro_rules! impl_arbitrary_for_integers {
    ( $( $ty:ty: $actual:ty; )* ) => {
        $(
            impl<'a> ArbitraryInRange<'a> for $ty {
                type Bound = Self;

                fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
                where
                    R: RangeBounds<Self::Bound>
                {
                    let minimum = map_bound(range.start_bound(), |x| *x as Self);
                    let maximum = map_bound(range.start_bound(), |x| *x as Self);
                    u.int_in_range((minimum, maximum))
                }
            }

            impl<'a> Arbitrary<'a> for $ty {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    Self::arbitrary_in_range(u, &..)
                }

                #[inline]
                fn size_hint(_depth: usize) -> (usize, Option<usize>) {
                    // The implementation of `arbitrary` uses `int_in_range`,
                    //   which is actually able to generate integers even from 0 bytes,
                    // thus the actual minimum is `0`.
                    // However, to meaningful generate integers, more bytes are required.
                    (mem::size_of::<$actual>(), Some(mem::size_of::<$actual>()))
                }

            }
        )*
    }
}

// Note: We forward Arbitrary for i/usize to i/u64 in order to simplify corpus
// compatibility between 32-bit and 64-bit builds. This introduces dead space in
// 32-bit builds but keeps the input layout independent of the build platform.
impl_arbitrary_for_integers! {
    u8: u8;
    u16: u16;
    u32: u32;
    u64: u64;
    u128: u128;
    usize: u64;
    i8: i8;
    i16: i16;
    i32: i32;
    i64: i64;
    i128: i128;
    isize: i64;
}

macro_rules! impl_arbitrary_for_floats {
    ( $( $ty:ident : $unsigned:ty; )* ) => {
        $(
            impl<'a> Arbitrary<'a> for $ty {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    Ok(Self::from_bits(<$unsigned as Arbitrary<'a>>::arbitrary(u)?))
                }

                #[inline]
                fn size_hint(depth: usize) -> (usize, Option<usize>) {
                    <$unsigned as Arbitrary<'a>>::size_hint(depth)
                }
            }
        )*
    }
}

impl_arbitrary_for_floats! {
    f32: u32;
    f64: u64;
}

macro_rules! implement_nonzero_int {
    ($nonzero:ty, $int:ty) => {
        impl<'a> ArbitraryInRange<'a> for $nonzero {
            type Bound = $int;

            fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
            where
                R: RangeBounds<Self::Bound>,
            {
                Self::new(<$int as ArbitraryInRange<'a>>::arbitrary_in_range(
                    u, range,
                )?)
                .ok_or(Error::InvalidRange)
            }
        }

        impl<'a> Arbitrary<'a> for $nonzero {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                Self::new(<$int as Arbitrary<'a>>::arbitrary(u)?).ok_or(Error::IncorrectFormat)
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                <$int as Arbitrary<'a>>::size_hint(depth)
            }
        }
    };
}

implement_nonzero_int! { NonZeroI8, i8 }
implement_nonzero_int! { NonZeroI16, i16 }
implement_nonzero_int! { NonZeroI32, i32 }
implement_nonzero_int! { NonZeroI64, i64 }
implement_nonzero_int! { NonZeroI128, i128 }
implement_nonzero_int! { NonZeroIsize, isize }
implement_nonzero_int! { NonZeroU8, u8 }
implement_nonzero_int! { NonZeroU16, u16 }
implement_nonzero_int! { NonZeroU32, u32 }
implement_nonzero_int! { NonZeroU64, u64 }
implement_nonzero_int! { NonZeroU128, u128 }
implement_nonzero_int! { NonZeroUsize, usize }

macro_rules! implement_wrapped {
    ($outer:ident) => {
        impl<'a, A> ArbitraryInRange<'a> for $outer<A>
        where
            A: ArbitraryInRange<'a>,
        {
            type Bound = A::Bound;

            fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
            where
                R: RangeBounds<Self::Bound>,
            {
                A::arbitrary_in_range(u, range).map($outer)
            }

            fn arbitrary_in_range_take_rest<R>(u: Unstructured<'a>, range: &R) -> Result<Self>
            where
                R: RangeBounds<Self::Bound>,
            {
                A::arbitrary_in_range_take_rest(u, range).map($outer)
            }
        }

        impl<'a, A> Arbitrary<'a> for $outer<A>
        where
            A: Arbitrary<'a>,
        {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                A::arbitrary(u).map($outer)
            }

            fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
                A::arbitrary_take_rest(u).map($outer)
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                Self::try_size_hint(depth).unwrap_or_default()
            }

            #[inline]
            fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {
                <A as Arbitrary<'a>>::try_size_hint(depth)
            }
        }
    };
}

implement_wrapped! { Saturating }
implement_wrapped! { Wrapping }
