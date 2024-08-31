// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The `Arbitrary` trait crate.
//!
//! This trait provides an [`Arbitrary`](./trait.Arbitrary.html) trait to
//! produce well-typed, structured values, from raw, byte buffers. It is
//! generally intended to be used with fuzzers like AFL or libFuzzer. See the
//! [`Arbitrary`](./trait.Arbitrary.html) trait's documentation for details on
//! automatically deriving, implementing, and/or using the trait.

#![deny(bad_style)]
#![deny(missing_docs)]
#![deny(future_incompatible)]
#![deny(nonstandard_style)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(unused)]

#[cfg(feature = "derive_arbitrary")]
pub use derive_arbitrary::*;

mod error;
pub use error::*;

pub mod unstructured;
#[doc(inline)]
pub use unstructured::Unstructured;

pub mod size_hint;

use core::array;
use core::cell::{Cell, RefCell, UnsafeCell};
use core::iter;
use std::{mem, ops};
use core::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use core::ops::{Range, RangeBounds, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};
use core::str;
use core::time::Duration;
use std::borrow::{Cow, ToOwned};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::ffi::{CString, OsString};
use std::hash::BuildHasher;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
use std::ops::Bound;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize};
use std::sync::{Arc, Mutex};

/// Generate arbitrary structured values from raw, unstructured data.
///
/// The `Arbitrary` trait allows you to generate valid structured values, like
/// `HashMap`s, or ASTs, or `MyTomlConfig`, or any other data structure from
/// raw, unstructured bytes provided by a fuzzer.
///
/// # Deriving `Arbitrary`
///
/// Automatically deriving the `Arbitrary` trait is the recommended way to
/// implement `Arbitrary` for your types.
///
/// Using the custom derive requires that you enable the `"derive"` cargo
/// feature in your `Cargo.toml`:
///
/// ```toml
/// [dependencies]
/// arbitrary = { version = "1", features = ["derive"] }
/// ```
///
/// Then, you add the `#[derive(Arbitrary)]` annotation to your `struct` or
/// `enum` type definition:
///
/// ```
/// # #[cfg(feature = "derive")] mod foo {
/// use arbitrary::Arbitrary;
/// use std::collections::HashSet;
///
/// #[derive(Arbitrary)]
/// pub struct AddressBook {
///     friends: HashSet<Friend>,
/// }
///
/// #[derive(Arbitrary, Hash, Eq, PartialEq)]
/// pub enum Friend {
///     Buddy { name: String },
///     Pal { age: usize },
/// }
/// # }
/// ```
///
/// Every member of the `struct` or `enum` must also implement `Arbitrary`.
///
/// It is also possible to change the default bounds added by the derive:
///
/// ```
/// # #[cfg(feature = "derive")] mod foo {
/// use arbitrary::Arbitrary;
///
/// trait Trait {
///     type Assoc: for<'a> Arbitrary<'a>;
/// }
///
/// #[derive(Arbitrary)]
/// // The bounds are used verbatim, so any existing trait bounds will need to be repeated.
/// #[arbitrary(bound = "T: Trait")]
/// struct Point<T: Trait> {
///     x: T::Assoc,
/// }
/// # }
/// ```
///
/// # Implementing `Arbitrary` By Hand
///
/// Implementing `Arbitrary` mostly involves nested calls to other `Arbitrary`
/// arbitrary implementations for each of your `struct` or `enum`'s members. But
/// sometimes you need some amount of raw data, or you need to generate a
/// variably-sized collection type, or something of that sort. The
/// [`Unstructured`][crate::Unstructured] type helps you with these tasks.
///
/// ```
/// # #[cfg(feature = "derive")] mod foo {
/// # pub struct MyCollection<T> { _t: std::marker::PhantomData<T> }
/// # impl<T> MyCollection<T> {
/// #     pub fn new() -> Self { MyCollection { _t: std::marker::PhantomData } }
/// #     pub fn insert(&mut self, element: T) {}
/// # }
/// use arbitrary::{Arbitrary, Result, Unstructured};
///
/// impl<'a, T> Arbitrary<'a> for MyCollection<T>
/// where
///     T: Arbitrary<'a>,
/// {
///     fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
///         // Get an iterator of arbitrary `T`s.
///         let iter = u.arbitrary_iter::<T>()?;
///
///         // And then create a collection!
///         let mut my_collection = MyCollection::new();
///         for elem_result in iter {
///             let elem = elem_result?;
///             my_collection.insert(elem);
///         }
///
///         Ok(my_collection)
///     }
/// }
/// # }
/// ```
///
/// # A Note On Output Distributions
///
/// There is no requirement for a particular distribution of the values. For
/// example, it is not required that every value appears with the same
/// probability. That being said, the main use for `Arbitrary` is for fuzzing,
/// so in many cases a uniform distribution will make the most sense in order to
/// provide the best coverage of the domain. In other cases this is not
/// desirable or even possible, for example when sampling from a uniform
/// distribution is computationally expensive or in the case of collections that
/// may grow indefinitely.
pub trait Arbitrary<'a>: Sized {
    /// Generate an arbitrary value of `Self` from the given unstructured data.
    ///
    /// Calling `Arbitrary::arbitrary` requires that you have some raw data,
    /// perhaps given to you by a fuzzer like AFL or libFuzzer. You wrap this
    /// raw data in an `Unstructured`, and then you can call `<MyType as
    /// Arbitrary>::arbitrary` to construct an arbitrary instance of `MyType`
    /// from that unstructured data.
    ///
    /// Implementations may return an error if there is not enough data to
    /// construct a full instance of `Self`, or they may fill out the rest of
    /// `Self` with dummy values. Using dummy values when the underlying data is
    /// exhausted can help avoid accidentally "defeating" some of the fuzzer's
    /// mutations to the underlying byte stream that might otherwise lead to
    /// interesting runtime behavior or new code coverage if only we had just a
    /// few more bytes. However, it also requires that implementations for
    /// recursive types (e.g. `struct Foo(Option<Box<Foo>>)`) avoid infinite
    /// recursion when the underlying data is exhausted.
    ///
    /// ```
    /// # #[cfg(feature = "derive")] fn foo() {
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// #[derive(Arbitrary)]
    /// pub struct MyType {
    ///     // ...
    /// }
    ///
    /// // Get the raw data from the fuzzer or wherever else.
    /// # let get_raw_data_from_fuzzer = || &[];
    /// let raw_data: &[u8] = get_raw_data_from_fuzzer();
    ///
    /// // Wrap that raw data in an `Unstructured`.
    /// let mut unstructured = Unstructured::new(raw_data);
    ///
    /// // Generate an arbitrary instance of `MyType` and do stuff with it.
    /// if let Ok(value) = MyType::arbitrary(&mut unstructured) {
    /// #   let do_stuff = |_| {};
    ///     do_stuff(value);
    /// }
    /// # }
    /// ```
    ///
    /// See also the documentation for [`Unstructured`][crate::Unstructured].
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self>;

    /// Generate an arbitrary value of `Self` for a given range from unstructured data.
    fn arbitrary_in_range<T>(u: &mut Unstructured<'a>, range: ops::RangeInclusive<T>) -> Result<Self>
    where
        T: crate::unstructured::Int,
    {
        let _r = range;
        Self::arbitrary(u)
    }

    /// Generate an arbitrary value of `Self` from the entirety of the given
    /// unstructured data.
    ///
    /// This is similar to Arbitrary::arbitrary, however it assumes that it is
    /// the last consumer of the given data, and is thus able to consume it all
    /// if it needs.  See also the documentation for
    /// [`Unstructured`][crate::Unstructured].
    fn arbitrary_take_rest(mut u: Unstructured<'a>) -> Result<Self> {
        Self::arbitrary(&mut u)
    }

    /// Get a size hint for how many bytes out of an `Unstructured` this type
    /// needs to construct itself.
    ///
    /// This is useful for determining how many elements we should insert when
    /// creating an arbitrary collection.
    ///
    /// The return value is similar to
    /// [`Iterator::size_hint`][iterator-size-hint]: it returns a tuple where
    /// the first element is a lower bound on the number of bytes required, and
    /// the second element is an optional upper bound.
    ///
    /// The default implementation return `(0, None)` which is correct for any
    /// type, but not ultimately that useful. Using `#[derive(Arbitrary)]` will
    /// create a better implementation. If you are writing an `Arbitrary`
    /// implementation by hand, and your type can be part of a dynamically sized
    /// collection (such as `Vec`), you are strongly encouraged to override this
    /// default with a better implementation. The
    /// [`size_hint`][crate::size_hint] module will help with this task.
    ///
    /// ## Invariant
    ///
    /// It must be possible to construct every possible output using only inputs
    /// of lengths bounded by these parameters. This applies to both
    /// [`Arbitrary::arbitrary`] and [`Arbitrary::arbitrary_take_rest`].
    ///
    /// This is trivially true for `(0, None)`. To restrict this further, it
    /// must be proven that all inputs that are now excluded produced redundant
    /// outputs which are still possible to produce using the reduced input
    /// space.
    ///
    /// ## The `depth` Parameter
    ///
    /// If you 100% know that the type you are implementing `Arbitrary` for is
    /// not a recursive type, or your implementation is not transitively calling
    /// any other `size_hint` methods, you can ignore the `depth` parameter.
    /// Note that if you are implementing `Arbitrary` for a generic type, you
    /// cannot guarantee the lack of type recursion!
    ///
    /// Otherwise, you need to use
    /// [`arbitrary::size_hint::recursion_guard(depth)`][crate::size_hint::recursion_guard]
    /// to prevent potential infinite recursion when calculating size hints for
    /// potentially recursive types:
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Unstructured, size_hint};
    ///
    /// // This can potentially be a recursive type if `L` or `R` contain
    /// // something like `Box<Option<MyEither<L, R>>>`!
    /// enum MyEither<L, R> {
    ///     Left(L),
    ///     Right(R),
    /// }
    ///
    /// impl<'a, L, R> Arbitrary<'a> for MyEither<L, R>
    /// where
    ///     L: Arbitrary<'a>,
    ///     R: Arbitrary<'a>,
    /// {
    ///     fn arbitrary(u: &mut Unstructured) -> arbitrary::Result<Self> {
    ///         // ...
    /// #       unimplemented!()
    ///     }
    ///
    ///     fn size_hint(depth: usize) -> (usize, Option<usize>) {
    ///         // Protect against potential infinite recursion with
    ///         // `recursion_guard`.
    ///         size_hint::recursion_guard(depth, |depth| {
    ///             // If we aren't too deep, then `recursion_guard` calls
    ///             // this closure, which implements the natural size hint.
    ///             // Don't forget to use the new `depth` in all nested
    ///             // `size_hint` calls! We recommend shadowing the
    ///             // parameter, like what is done here, so that you can't
    ///             // accidentally use the wrong depth.
    ///             size_hint::or(
    ///                 <L as Arbitrary>::size_hint(depth),
    ///                 <R as Arbitrary>::size_hint(depth),
    ///             )
    ///         })
    ///     }
    /// }
    /// ```
    ///
    /// [iterator-size-hint]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html#method.size_hint
    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        let _ = depth;
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for () {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(())
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<'a> Arbitrary<'a> for bool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(<u8 as Arbitrary<'a>>::arbitrary(u)? & 1 == 1)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <u8 as Arbitrary<'a>>::size_hint(depth)
    }
}

macro_rules! impl_arbitrary_for_integers {
    ( $( $ty:ty; )* ) => {
        $(
            impl<'a> Arbitrary<'a> for $ty {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    let mut buf = [0; mem::size_of::<$ty>()];
                    u.fill_buffer(&mut buf)?;
                    Ok(Self::from_le_bytes(buf))
                }

                #[inline]
                fn size_hint(_depth: usize) -> (usize, Option<usize>) {
                    let n = mem::size_of::<$ty>();
                    (n, Some(n))
                }

            }
        )*
    }
}

impl_arbitrary_for_integers! {
    u8;
    u16;
    u32;
    u64;
    u128;
    i8;
    i16;
    i32;
    i64;
    i128;
}

// Note: We forward Arbitrary for i/usize to i/u64 in order to simplify corpus
// compatibility between 32-bit and 64-bit builds. This introduces dead space in
// 32-bit builds but keeps the input layout independent of the build platform.
impl<'a> Arbitrary<'a> for usize {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary::<u64>().map(|x| x as usize)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <u64 as Arbitrary>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for isize {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary::<i64>().map(|x| x as isize)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <i64 as Arbitrary>::size_hint(depth)
    }
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

impl<'a> Arbitrary<'a> for char {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        use std::char;
        // The highest unicode code point is 0x11_FFFF
        const CHAR_END: u32 = 0x11_0000;
        // The size of the surrogate blocks
        const SURROGATES_START: u32 = 0xD800;
        let mut c = <u32 as Arbitrary<'a>>::arbitrary(u)? % CHAR_END;
        if let Some(c) = char::from_u32(c) {
            Ok(c)
        } else {
            // We found a surrogate, wrap and try again
            c -= SURROGATES_START;
            Ok(char::from_u32(c)
                .expect("Generated character should be valid! This is a bug in arbitrary-rs"))
        }
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <u32 as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for AtomicBool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <bool as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for AtomicIsize {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <isize as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for AtomicUsize {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <usize as Arbitrary<'a>>::size_hint(depth)
    }
}

macro_rules! impl_range {
    (
        $range:ty,
        $value_closure:expr,
        $value_ty:ty,
        $fun:ident($fun_closure:expr),
        $size_hint_closure:expr
    ) => {
        impl<'a, A> Arbitrary<'a> for $range
        where
            A: Arbitrary<'a> + Clone + PartialOrd,
        {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                let value: $value_ty = Arbitrary::arbitrary(u)?;
                Ok($fun(value, $fun_closure))
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                #[allow(clippy::redundant_closure_call)]
                $size_hint_closure(depth)
            }
        }
    };
}

impl_range!(
    Range<A>,
    |r: &Range<A>| (r.start.clone(), r.end.clone()),
    (A, A),
    bounded_range(|(a, b)| a..b),
    |depth| crate::size_hint::and(
        <A as Arbitrary>::size_hint(depth),
        <A as Arbitrary>::size_hint(depth)
    )
);
impl_range!(
    RangeFrom<A>,
    |r: &RangeFrom<A>| r.start.clone(),
    A,
    unbounded_range(|a| a..),
    |depth| <A as Arbitrary>::size_hint(depth)
);
impl_range!(
    RangeInclusive<A>,
    |r: &RangeInclusive<A>| (r.start().clone(), r.end().clone()),
    (A, A),
    bounded_range(|(a, b)| a..=b),
    |depth| crate::size_hint::and(
        <A as Arbitrary>::size_hint(depth),
        <A as Arbitrary>::size_hint(depth)
    )
);
impl_range!(
    RangeTo<A>,
    |r: &RangeTo<A>| r.end.clone(),
    A,
    unbounded_range(|b| ..b),
    |depth| <A as Arbitrary>::size_hint(depth)
);
impl_range!(
    RangeToInclusive<A>,
    |r: &RangeToInclusive<A>| r.end.clone(),
    A,
    unbounded_range(|b| ..=b),
    |depth| <A as Arbitrary>::size_hint(depth)
);

pub(crate) fn bounded_range<CB, I, R>(bounds: (I, I), cb: CB) -> R
where
    CB: Fn((I, I)) -> R,
    I: PartialOrd,
    R: RangeBounds<I>,
{
    let (mut start, mut end) = bounds;
    if start > end {
        mem::swap(&mut start, &mut end);
    }
    cb((start, end))
}

pub(crate) fn unbounded_range<CB, I, R>(bound: I, cb: CB) -> R
where
    CB: Fn(I) -> R,
    R: RangeBounds<I>,
{
    cb(bound)
}

impl<'a> Arbitrary<'a> for Duration {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self::new(
            <u64 as Arbitrary>::arbitrary(u)?,
            u.int_in_range(0..=999_999_999)?,
        ))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::and(
            <u64 as Arbitrary>::size_hint(depth),
            <u32 as Arbitrary>::size_hint(depth),
        )
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Option<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(if <bool as Arbitrary<'a>>::arbitrary(u)? {
            Some(Arbitrary::arbitrary(u)?)
        } else {
            None
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::and(
            <bool as Arbitrary>::size_hint(depth),
            crate::size_hint::or((0, Some(0)), <A as Arbitrary>::size_hint(depth)),
        )
    }
}

impl<'a, A: Arbitrary<'a>, B: Arbitrary<'a>> Arbitrary<'a> for std::result::Result<A, B> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(if <bool as Arbitrary<'a>>::arbitrary(u)? {
            Ok(<A as Arbitrary>::arbitrary(u)?)
        } else {
            Err(<B as Arbitrary>::arbitrary(u)?)
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::and(
            <bool as Arbitrary>::size_hint(depth),
            crate::size_hint::or(
                <A as Arbitrary>::size_hint(depth),
                <B as Arbitrary>::size_hint(depth),
            ),
        )
    }
}

macro_rules! arbitrary_tuple {
    () => {};
    ($last: ident $($xs: ident)*) => {
        arbitrary_tuple!($($xs)*);

        impl<'a, $($xs: Arbitrary<'a>,)* $last: Arbitrary<'a>> Arbitrary<'a> for ($($xs,)* $last,) {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                Ok(($($xs::arbitrary(u)?,)* Arbitrary::arbitrary(u)?,))
            }

            #[allow(unused_mut, non_snake_case)]
            fn arbitrary_take_rest(mut u: Unstructured<'a>) -> Result<Self> {
                $(let $xs = $xs::arbitrary(&mut u)?;)*
                let $last = $last::arbitrary_take_rest(u)?;
                Ok(($($xs,)* $last,))
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                crate::size_hint::and_all(&[
                    <$last as Arbitrary>::size_hint(depth),
                    $( <$xs as Arbitrary>::size_hint(depth) ),*
                ])
            }
        }
    };
}
arbitrary_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);

// Helper to safely create arrays since the standard library doesn't
// provide one yet. Shouldn't be necessary in the future.
struct ArrayGuard<T, const N: usize> {
    dst: *mut T,
    initialized: usize,
}

impl<T, const N: usize> Drop for ArrayGuard<T, N> {
    fn drop(&mut self) {
        debug_assert!(self.initialized <= N);
        let initialized_part = core::ptr::slice_from_raw_parts_mut(self.dst, self.initialized);
        unsafe {
            core::ptr::drop_in_place(initialized_part);
        }
    }
}

fn try_create_array<F, T, const N: usize>(mut cb: F) -> Result<[T; N]>
where
    F: FnMut(usize) -> Result<T>,
{
    let mut array: mem::MaybeUninit<[T; N]> = mem::MaybeUninit::uninit();
    let array_ptr = array.as_mut_ptr();
    let dst = array_ptr as _;
    let mut guard: ArrayGuard<T, N> = ArrayGuard {
        dst,
        initialized: 0,
    };
    unsafe {
        for (idx, value_ptr) in (*array.as_mut_ptr()).iter_mut().enumerate() {
            core::ptr::write(value_ptr, cb(idx)?);
            guard.initialized += 1;
        }
        mem::forget(guard);
        Ok(array.assume_init())
    }
}

impl<'a, T, const N: usize> Arbitrary<'a> for [T; N]
where
    T: Arbitrary<'a>,
{
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        try_create_array(|_| <T as Arbitrary<'a>>::arbitrary(u))
    }

    #[inline]
    fn arbitrary_take_rest(mut u: Unstructured<'a>) -> Result<Self> {
        let mut array = Self::arbitrary(&mut u)?;
        if let Some(last) = array.last_mut() {
            *last = Arbitrary::arbitrary_take_rest(u)?;
        }
        Ok(array)
    }

    #[inline]
    fn size_hint(d: usize) -> (usize, Option<usize>) {
        crate::size_hint::and_all(&array::from_fn::<_, N, _>(|_| {
            <T as Arbitrary>::size_hint(d)
        }))
    }
}

impl<'a> Arbitrary<'a> for &'a [u8] {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let len = u.arbitrary_len::<u8>()?;
        u.bytes(len)
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        Ok(u.take_rest())
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Vec<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, K: Arbitrary<'a> + Ord, V: Arbitrary<'a>> Arbitrary<'a> for BTreeMap<K, V> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a> + Ord> Arbitrary<'a> for BTreeSet<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Bound<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        match u.int_in_range::<u8>(0..=2)? {
            0 => Ok(Bound::Included(A::arbitrary(u)?)),
            1 => Ok(Bound::Excluded(A::arbitrary(u)?)),
            2 => Ok(Bound::Unbounded),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::or(
            size_hint::and((1, Some(1)), A::size_hint(depth)),
            (1, Some(1)),
        )
    }
}

impl<'a, A: Arbitrary<'a> + Ord> Arbitrary<'a> for BinaryHeap<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, K: Arbitrary<'a> + Eq + ::std::hash::Hash, V: Arbitrary<'a>, S: BuildHasher + Default>
    Arbitrary<'a> for HashMap<K, V, S>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a> + Eq + ::std::hash::Hash, S: BuildHasher + Default> Arbitrary<'a>
    for HashSet<A, S>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for LinkedList<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for VecDeque<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A> Arbitrary<'a> for Cow<'a, A>
where
    A: ToOwned + ?Sized,
    <A as ToOwned>::Owned: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, |depth| {
            <<A as ToOwned>::Owned as Arbitrary>::size_hint(depth)
        })
    }
}

fn arbitrary_str<'a>(u: &mut Unstructured<'a>, size: usize) -> Result<&'a str> {
    match str::from_utf8(u.peek_bytes(size).unwrap()) {
        Ok(s) => {
            u.bytes(size).unwrap();
            Ok(s)
        }
        Err(e) => {
            let i = e.valid_up_to();
            let valid = u.bytes(i).unwrap();
            let s = unsafe {
                debug_assert!(str::from_utf8(valid).is_ok());
                str::from_utf8_unchecked(valid)
            };
            Ok(s)
        }
    }
}

impl<'a> Arbitrary<'a> for &'a str {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let size = u.arbitrary_len::<u8>()?;
        arbitrary_str(u, size)
    }

    fn arbitrary_take_rest(mut u: Unstructured<'a>) -> Result<Self> {
        let size = u.len();
        arbitrary_str(&mut u, size)
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for String {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary_take_rest(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for CString {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <Vec<u8> as Arbitrary>::arbitrary(u).map(|mut x| {
            x.retain(|&c| c != 0);
            // SAFETY: all zero bytes have been removed
            unsafe { Self::from_vec_unchecked(x) }
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <Vec<u8> as Arbitrary>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for OsString {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(From::from)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <String as Arbitrary>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for PathBuf {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <OsString as Arbitrary>::arbitrary(u).map(From::from)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <OsString as Arbitrary>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Box<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Box<[A]> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for Box<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <String as Arbitrary>::size_hint(depth)
    }
}

// impl Arbitrary for Box<CStr> {
//     fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
//         <CString as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_c_str())
//     }
// }

// impl Arbitrary for Box<OsStr> {
//     fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
//         <OsString as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_osstr())
//
//     }
// }

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Arc<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Arc<[A]> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for Arc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Rc<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Rc<[A]> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a> Arbitrary<'a> for Rc<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <&str as Arbitrary>::arbitrary(u).map(Into::into)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <&str as Arbitrary>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Cell<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <A as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for RefCell<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <A as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for UnsafeCell<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <A as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Mutex<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <A as Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for iter::Empty<A> {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(iter::empty())
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<'a, A: ?Sized> Arbitrary<'a> for ::std::marker::PhantomData<A> {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(::std::marker::PhantomData)
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<'a> Arbitrary<'a> for ::std::marker::PhantomPinned {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(::std::marker::PhantomPinned)
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for ::std::num::Wrapping<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(::std::num::Wrapping)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <A as Arbitrary<'a>>::size_hint(depth)
    }
}

macro_rules! implement_nonzero_int {
    ($nonzero:ty, $int:ty) => {
        impl<'a> Arbitrary<'a> for $nonzero {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                match Self::new(<$int as Arbitrary<'a>>::arbitrary(u)?) {
                    Some(n) => Ok(n),
                    None => Err(Error::IncorrectFormat),
                }
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

impl<'a> Arbitrary<'a> for Ipv4Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv4Addr::from(u32::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (4, Some(4))
    }
}

impl<'a> Arbitrary<'a> for Ipv6Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv6Addr::from(u128::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (16, Some(16))
    }
}

impl<'a> Arbitrary<'a> for IpAddr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.arbitrary()? {
            Ok(IpAddr::V4(u.arbitrary()?))
        } else {
            Ok(IpAddr::V6(u.arbitrary()?))
        }
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(
            bool::size_hint(depth),
            size_hint::or(Ipv4Addr::size_hint(depth), Ipv6Addr::size_hint(depth)),
        )
    }
}

impl<'a> Arbitrary<'a> for SocketAddrV4 {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(SocketAddrV4::new(u.arbitrary()?, u.arbitrary()?))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(Ipv4Addr::size_hint(depth), u16::size_hint(depth))
    }
}

impl<'a> Arbitrary<'a> for SocketAddrV6 {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(SocketAddrV6::new(
            u.arbitrary()?,
            u.arbitrary()?,
            u.arbitrary()?,
            u.arbitrary()?,
        ))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(
            Ipv6Addr::size_hint(depth),
            size_hint::and(
                u16::size_hint(depth),
                size_hint::and(u32::size_hint(depth), u32::size_hint(depth)),
            ),
        )
    }
}

impl<'a> Arbitrary<'a> for SocketAddr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.arbitrary()? {
            Ok(SocketAddr::V4(u.arbitrary()?))
        } else {
            Ok(SocketAddr::V6(u.arbitrary()?))
        }
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        size_hint::and(
            bool::size_hint(depth),
            size_hint::or(
                SocketAddrV4::size_hint(depth),
                SocketAddrV6::size_hint(depth),
            ),
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// Assert that the given expected values are all generated.
    ///
    /// Exhaustively enumerates all buffers up to length 10 containing the
    /// following bytes: `0x00`, `0x01`, `0x61` (aka ASCII 'a'), and `0xff`
    fn assert_generates<T>(expected_values: impl IntoIterator<Item = T>)
    where
        T: Clone + std::fmt::Debug + std::hash::Hash + Eq + for<'a> Arbitrary<'a>,
    {
        let expected_values: HashSet<_> = expected_values.into_iter().collect();
        let mut arbitrary_expected = expected_values.clone();
        let mut arbitrary_take_rest_expected = expected_values;

        let bytes = [0, 1, b'a', 0xff];
        let max_len = 10;

        let mut buf = Vec::with_capacity(max_len);

        let mut g = exhaustigen::Gen::new();
        while !g.done() {
            let len = g.gen(max_len);

            buf.clear();
            buf.extend(
                std::iter::repeat_with(|| {
                    let index = g.gen(bytes.len() - 1);
                    bytes[index]
                })
                .take(len),
            );

            let mut u = Unstructured::new(&buf);
            let val = T::arbitrary(&mut u).unwrap();
            arbitrary_expected.remove(&val);

            let u = Unstructured::new(&buf);
            let val = T::arbitrary_take_rest(u).unwrap();
            arbitrary_take_rest_expected.remove(&val);

            if arbitrary_expected.is_empty() && arbitrary_take_rest_expected.is_empty() {
                return;
            }
        }

        panic!(
            "failed to generate all expected values!\n\n\
             T::arbitrary did not generate: {arbitrary_expected:#?}\n\n\
             T::arbitrary_take_rest did not generate {arbitrary_take_rest_expected:#?}"
        )
    }

    /// Generates an arbitrary `T`, and checks that the result is consistent with the
    /// `size_hint()` reported by `T`.
    fn checked_arbitrary<'a, T: Arbitrary<'a>>(u: &mut Unstructured<'a>) -> Result<T> {
        let (min, max) = T::size_hint(0);

        let len_before = u.len();
        let result = T::arbitrary(u);

        let consumed = len_before - u.len();

        if let Some(max) = max {
            assert!(
                consumed <= max,
                "incorrect maximum size: indicated {}, actually consumed {}",
                max,
                consumed
            );
        }

        if result.is_ok() {
            assert!(
                consumed >= min,
                "incorrect minimum size: indicated {}, actually consumed {}",
                min,
                consumed
            );
        }

        result
    }

    /// Like `checked_arbitrary()`, but calls `arbitrary_take_rest()` instead of `arbitrary()`.
    fn checked_arbitrary_take_rest<'a, T: Arbitrary<'a>>(u: Unstructured<'a>) -> Result<T> {
        let (min, _) = T::size_hint(0);

        let len_before = u.len();
        let result = T::arbitrary_take_rest(u);

        if result.is_ok() {
            assert!(
                len_before >= min,
                "incorrect minimum size: indicated {}, worked with {}",
                min,
                len_before
            );
        }

        result
    }

    #[test]
    fn finite_buffer_fill_buffer() {
        let x = [1, 2, 3, 4];
        let mut rb = Unstructured::new(&x);
        let mut z = [0; 2];
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [1, 2]);
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [3, 4]);
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [0, 0]);
    }

    #[test]
    fn arbitrary_for_integers() {
        let x = [1, 2, 3, 4];
        let mut buf = Unstructured::new(&x);
        let expected = 1 | (2 << 8) | (3 << 16) | (4 << 24);
        let actual = checked_arbitrary::<i32>(&mut buf).unwrap();
        assert_eq!(expected, actual);

        assert_generates([
            i32::from_ne_bytes([0, 0, 0, 0]),
            i32::from_ne_bytes([0, 0, 0, 1]),
            i32::from_ne_bytes([0, 0, 1, 0]),
            i32::from_ne_bytes([0, 1, 0, 0]),
            i32::from_ne_bytes([1, 0, 0, 0]),
            i32::from_ne_bytes([1, 1, 1, 1]),
            i32::from_ne_bytes([0xff, 0xff, 0xff, 0xff]),
        ]);
    }

    #[test]
    fn arbitrary_for_bytes() {
        let x = [1, 2, 3, 4, 4];
        let mut buf = Unstructured::new(&x);
        let expected = &[1, 2, 3, 4];
        let actual = checked_arbitrary::<&[u8]>(&mut buf).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn arbitrary_take_rest_for_bytes() {
        let x = [1, 2, 3, 4];
        let buf = Unstructured::new(&x);
        let expected = &[1, 2, 3, 4];
        let actual = checked_arbitrary_take_rest::<&[u8]>(buf).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn arbitrary_for_vec_u8() {
        assert_generates::<Vec<u8>>([
            vec![],
            vec![0],
            vec![1],
            vec![0, 0],
            vec![0, 1],
            vec![1, 0],
            vec![1, 1],
            vec![0, 0, 0],
            vec![0, 0, 1],
            vec![0, 1, 0],
            vec![0, 1, 1],
            vec![1, 0, 0],
            vec![1, 0, 1],
            vec![1, 1, 0],
            vec![1, 1, 1],
        ]);
    }

    #[test]
    fn arbitrary_for_vec_vec_u8() {
        assert_generates::<Vec<Vec<u8>>>([
            vec![],
            vec![vec![]],
            vec![vec![0]],
            vec![vec![1]],
            vec![vec![0, 1]],
            vec![vec![], vec![]],
            vec![vec![0], vec![]],
            vec![vec![], vec![1]],
            vec![vec![0], vec![1]],
            vec![vec![0, 1], vec![]],
            vec![vec![], vec![1, 0]],
            vec![vec![], vec![], vec![]],
        ]);
    }

    #[test]
    fn arbitrary_for_vec_vec_vec_u8() {
        assert_generates::<Vec<Vec<Vec<u8>>>>([
            vec![],
            vec![vec![]],
            vec![vec![vec![0]]],
            vec![vec![vec![1]]],
            vec![vec![vec![0, 1]]],
            vec![vec![], vec![]],
            vec![vec![], vec![vec![]]],
            vec![vec![vec![]], vec![]],
            vec![vec![vec![]], vec![vec![]]],
            vec![vec![vec![0]], vec![]],
            vec![vec![], vec![vec![1]]],
            vec![vec![vec![0]], vec![vec![1]]],
            vec![vec![vec![0, 1]], vec![]],
            vec![vec![], vec![vec![0, 1]]],
            vec![vec![], vec![], vec![]],
            vec![vec![vec![]], vec![], vec![]],
            vec![vec![], vec![vec![]], vec![]],
            vec![vec![], vec![], vec![vec![]]],
        ]);
    }

    #[test]
    fn arbitrary_for_string() {
        assert_generates::<String>(["".into(), "a".into(), "aa".into(), "aaa".into()]);
    }

    #[test]
    fn arbitrary_collection() {
        let x = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 12,
        ];
        assert_eq!(
            checked_arbitrary::<&[u8]>(&mut Unstructured::new(&x)).unwrap(),
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3]
        );
        assert_eq!(
            checked_arbitrary::<Vec<u8>>(&mut Unstructured::new(&x)).unwrap(),
            &[2, 4, 6, 8, 1]
        );
        assert_eq!(
            &*checked_arbitrary::<Box<[u8]>>(&mut Unstructured::new(&x)).unwrap(),
            &[2, 4, 6, 8, 1]
        );
        assert_eq!(
            &*checked_arbitrary::<Arc<[u8]>>(&mut Unstructured::new(&x)).unwrap(),
            &[2, 4, 6, 8, 1]
        );
        assert_eq!(
            &*checked_arbitrary::<Rc<[u8]>>(&mut Unstructured::new(&x)).unwrap(),
            &[2, 4, 6, 8, 1]
        );
        assert_eq!(
            checked_arbitrary::<Vec<u32>>(&mut Unstructured::new(&x)).unwrap(),
            &[84148994]
        );
        assert_eq!(
            checked_arbitrary::<String>(&mut Unstructured::new(&x)).unwrap(),
            "\x01\x02\x03\x04\x05\x06\x07\x08\x09\x01\x02\x03"
        );
    }

    #[test]
    fn arbitrary_take_rest() {
        // Basic examples
        let x = [1, 2, 3, 4];
        assert_eq!(
            checked_arbitrary_take_rest::<&[u8]>(Unstructured::new(&x)).unwrap(),
            &[1, 2, 3, 4]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u8>>(Unstructured::new(&x)).unwrap(),
            &[2, 4]
        );
        assert_eq!(
            &*checked_arbitrary_take_rest::<Box<[u8]>>(Unstructured::new(&x)).unwrap(),
            &[2, 4]
        );
        assert_eq!(
            &*checked_arbitrary_take_rest::<Arc<[u8]>>(Unstructured::new(&x)).unwrap(),
            &[2, 4]
        );
        assert_eq!(
            &*checked_arbitrary_take_rest::<Rc<[u8]>>(Unstructured::new(&x)).unwrap(),
            &[2, 4]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u32>>(Unstructured::new(&x)).unwrap(),
            &[0x040302]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<String>(Unstructured::new(&x)).unwrap(),
            "\x01\x02\x03\x04"
        );

        // Empty remainder
        assert_eq!(
            checked_arbitrary_take_rest::<&[u8]>(Unstructured::new(&[])).unwrap(),
            &[]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u8>>(Unstructured::new(&[])).unwrap(),
            &[]
        );

        // Cannot consume all but can consume part of the input
        assert_eq!(
            checked_arbitrary_take_rest::<String>(Unstructured::new(&[1, 0xFF, 2])).unwrap(),
            "\x01"
        );
    }

    #[test]
    fn size_hint_for_tuples() {
        assert_eq!(
            (7, Some(7)),
            <(bool, u16, i32) as Arbitrary<'_>>::size_hint(0)
        );
        assert_eq!((1, None), <(u8, Vec<u8>) as Arbitrary>::size_hint(0));
    }
}

/// Multiple conflicting arbitrary attributes are used on the same field:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// struct Point {
///     #[arbitrary(value = 2)]
///     #[arbitrary(value = 2)]
///     x: i32,
/// }
/// ```
///
/// An unknown attribute:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// struct Point {
///     #[arbitrary(unknown_attr)]
///     x: i32,
/// }
/// ```
///
/// An unknown attribute with a value:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// struct Point {
///     #[arbitrary(unknown_attr = 13)]
///     x: i32,
/// }
/// ```
///
/// `value` without RHS:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// struct Point {
///     #[arbitrary(value)]
///     x: i32,
/// }
/// ```
///
/// `with` without RHS:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// struct Point {
///     #[arbitrary(with)]
///     x: i32,
/// }
/// ```
///
/// Multiple conflicting bounds at the container-level:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// #[arbitrary(bound = "T: Default")]
/// #[arbitrary(bound = "T: Default")]
/// struct Point<T: Default> {
///     #[arbitrary(default)]
///     x: T,
/// }
/// ```
///
/// Multiple conflicting bounds in a single bound attribute:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// #[arbitrary(bound = "T: Default, T: Default")]
/// struct Point<T: Default> {
///     #[arbitrary(default)]
///     x: T,
/// }
/// ```
///
/// Multiple conflicting bounds in multiple bound attributes:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// #[arbitrary(bound = "T: Default", bound = "T: Default")]
/// struct Point<T: Default> {
///     #[arbitrary(default)]
///     x: T,
/// }
/// ```
///
/// Too many bounds supplied:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// #[arbitrary(bound = "T: Default")]
/// struct Point {
///     x: i32,
/// }
/// ```
///
/// Too many bounds supplied across multiple attributes:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// #[arbitrary(bound = "T: Default")]
/// #[arbitrary(bound = "U: Default")]
/// struct Point<T: Default> {
///     #[arbitrary(default)]
///     x: T,
/// }
/// ```
///
/// Attempt to use the derive attribute on an enum variant:
/// ```compile_fail
/// #[derive(::arbitrary::Arbitrary)]
/// enum Enum<T: Default> {
///     #[arbitrary(default)]
///     Variant(T),
/// }
/// ```
#[cfg(all(doctest, feature = "derive"))]
pub struct CompileFailTests;
