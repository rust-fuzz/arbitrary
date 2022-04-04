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

use core::cell::{Cell, RefCell, UnsafeCell};
use core::iter;
use core::mem;
use core::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use core::ops::{Range, RangeBounds, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};
use core::str;
use core::time::Duration;
use std::borrow::{Cow, ToOwned};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::ffi::{CString, OsString};
use std::hash::BuildHasher;
use std::net::{Ipv4Addr, Ipv6Addr};
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
/// 
///     fn dearbitrary(&self) -> Vec<u8> {
///         unimplemented!()
///     }
/// }
/// # }
/// ```
pub trait Arbitrary<'a>: Sized {
    /// Generate an arbitrary value of `Self` from the given unstructured data.
    ///
    /// Calling `Arbitrary::arbitrary` requires that you have some raw data,
    /// perhaps given to you by a fuzzer like AFL or libFuzzer. You wrap this
    /// raw data in an `Unstructured`, and then you can call `<MyType as
    /// Arbitrary>::arbitrary` to construct an arbitrary instance of `MyType`
    /// from that unstuctured data.
    ///
    /// Implementation may return an error if there is not enough data to
    /// construct a full instance of `Self`. This is generally OK: it is better
    /// to exit early and get the fuzzer to provide more input data, than it is
    /// to generate default values in place of the missing data, which would
    /// bias the distribution of generated values, and ultimately make fuzzing
    /// less efficient.
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

    
    /// Inverse operation of `arbitrary` aka creating the byte stream, which can be used
    /// together with an `arbitrary` call to recreate `Self`.
    /// 
    fn dearbitrary(&self) -> Vec<u8>;

    /// Generate an arbitrary value of `Self` from the entirety of the given unstructured data.
    ///
    /// This is similar to Arbitrary::arbitrary, however it assumes that it is the
    /// last consumer of the given data, and is thus able to consume it all if it needs.
    /// See also the documentation for [`Unstructured`][crate::Unstructured].
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
    /// This is trivially true for `(0, None)`. To restrict this further, it must be proven
    /// that all inputs that are now excluded produced redundant outputs which are still
    /// possible to produce using the reduced input space.
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
    ///     fn dearbitrary(&self) -> Vec<u8> {
    ///         unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        Vec::new()
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

    fn dearbitrary(&self) -> Vec<u8> {
        if *self {
            u8::dearbitrary(&1)
        } else {
            u8::dearbitrary(&0)
        }
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <u8 as Arbitrary<'a>>::size_hint(depth)
    }
}

macro_rules! impl_arbitrary_for_integers {
    ( $( $ty:ty: $unsigned:ty; )* ) => {
        $(
            impl<'a> Arbitrary<'a> for $ty {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    let mut buf = [0; mem::size_of::<$ty>()];
                    u.fill_buffer(&mut buf)?;
                    let mut x: $unsigned = 0;
                    for i in 0..mem::size_of::<$ty>() {
                        x |= buf[i] as $unsigned << (i * 8);
                    }
                    Ok(x as $ty)
                }

                fn dearbitrary(&self) -> Vec<u8> {
                    let mut buf = [0; mem::size_of::<$ty>()];
                    for i in 0..mem::size_of::<$ty>() {
                        buf[i] = ((*self as $unsigned >> (i * 8)) & 0xFF ) as u8;
                    }
                    buf.to_vec()
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
    u8: u8;
    u16: u16;
    u32: u32;
    u64: u64;
    u128: u128;
    usize: usize;
    i8: u8;
    i16: u16;
    i32: u32;
    i64: u64;
    i128: u128;
    isize: usize;
}

macro_rules! impl_arbitrary_for_floats {
    ( $( $ty:ident : $unsigned:ty; )* ) => {
        $(
            impl<'a> Arbitrary<'a> for $ty {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    Ok(Self::from_bits(<$unsigned as Arbitrary<'a>>::arbitrary(u)?))
                }

                fn dearbitrary(&self) -> Vec<u8> {
                    <$unsigned>::dearbitrary(&Self::to_bits(*self))
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

    fn dearbitrary(&self) -> Vec<u8> {
        u32::dearbitrary(&(*self as u32))
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

            fn dearbitrary(&self) -> Vec<u8> {
                unimplemented!()
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

macro_rules! expr { ($x:expr) => ($x) }
macro_rules! tuple_index {
    ($tuple:expr, $idx:tt) => { expr!($tuple.$idx) }
}


macro_rules! arbitrary_tuple {
    () => {};
    ($last: ident -> ($ln: tt) $($xs: ident -> ($n: tt))*) => {
        arbitrary_tuple!($($xs -> ($n))*);

        impl<'a, $($xs: Arbitrary<'a>,)* $last: Arbitrary<'a>> Arbitrary<'a> for ($($xs,)* $last,) {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                Ok(($($xs::arbitrary(u)?,)* Arbitrary::arbitrary(u)?,))
            }

            fn dearbitrary(&self) -> Vec<u8> {
                let mut vv: Vec<Vec<u8>> = Vec::new();
                vv.push(Arbitrary::dearbitrary(&tuple_index!(*self, $ln)));
                $(vv.push(Arbitrary::dearbitrary(&tuple_index!(*self, $n)));)*
                vv.reverse();
                vv.into_iter().flatten().collect()
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
arbitrary_tuple!(
    A -> (25)
    B -> (24)
    C -> (23)
    D -> (22)
    E -> (21)
    F -> (20)
    G -> (19)
    H -> (18)
    I -> (17)
    J -> (16)
    K -> (15)
    L -> (14)
    M -> (13)
    N -> (12)
    O -> (11)
    P -> (10)
    Q -> (9)
    R -> (8)
    S -> (7)
    T -> (6)
    U -> (5)
    V -> (4)
    W -> (3)
    X -> (2)
    Y -> (1)
    Z -> (0));

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

fn create_array<F, T, const N: usize>(mut cb: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    let mut array: mem::MaybeUninit<[T; N]> = mem::MaybeUninit::uninit();
    let array_ptr = array.as_mut_ptr();
    let dst = array_ptr as _;
    let mut guard: ArrayGuard<T, N> = ArrayGuard {
        dst,
        initialized: 0,
    };
    unsafe {
        for (idx, value_ptr) in (&mut *array.as_mut_ptr()).iter_mut().enumerate() {
            core::ptr::write(value_ptr, cb(idx));
            guard.initialized += 1;
        }
        mem::forget(guard);
        array.assume_init()
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
        for (idx, value_ptr) in (&mut *array.as_mut_ptr()).iter_mut().enumerate() {
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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
        crate::size_hint::and_all(&create_array::<_, (usize, Option<usize>), N>(|_| {
            <T as Arbitrary>::size_hint(d)
        }))
    }
}

impl<'a> Arbitrary<'a> for &'a [u8] {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let len = u.arbitrary_len::<u8>()?;
        u.bytes(len)
    }

    fn dearbitrary(&self) -> Vec<u8> {
        let mut len_bytes = if self.len() <= core::u8::MAX as usize + 1 {
            let l = self.len() as u8;
            vec![l]
        } else if self.len() <= core::u16::MAX as usize + 1 {
            let l = self.len() as u16;
            l.to_le_bytes().to_vec()
        } else if self.len() <= core::u32::MAX as usize + 1 {
            let l = self.len() as u32;
            l.to_le_bytes().to_vec()
        } else {
            let l = self.len() as u64;
            l.to_le_bytes().to_vec()
        };

        let mut v = Vec::new();
        v.append(&mut self.to_vec());
        v.append(&mut len_bytes);
        v
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

    fn dearbitrary(&self) -> Vec<u8> {
        let mut v = Vec::new();
        for a in self {
            v.append(&mut bool::dearbitrary(&true));
            v.append(&mut A::dearbitrary(a));
        }
        v.append(&mut bool::dearbitrary(&false));
        v
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        u.arbitrary_take_rest_iter()?.collect()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, A: Arbitrary<'a> + Ord> Arbitrary<'a> for BinaryHeap<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, |depth| {
            <<A as ToOwned>::Owned as Arbitrary>::size_hint(depth)
        })
    }
}

impl<'a> Arbitrary<'a> for &'a str {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let size = u.arbitrary_len::<u8>()?;
        match str::from_utf8(&u.peek_bytes(size).unwrap()) {
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn arbitrary_take_rest(u: Unstructured<'a>) -> Result<Self> {
        let bytes = u.take_rest();
        str::from_utf8(bytes)
            .map_err(|_| Error::IncorrectFormat)
            .map(Into::into)
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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
            Self::new(x).unwrap()
        })
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <OsString as Arbitrary>::size_hint(depth)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Box<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let a = Arbitrary::arbitrary(u);
        a.map(Self::new)
    }

    fn dearbitrary(&self) -> Vec<u8> {
        A::dearbitrary(&*self)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a> + Clone> Arbitrary<'a> for Box<[A]> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <Vec<A> as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_slice())
    }

    fn dearbitrary(&self) -> Vec<u8> {
        <Vec<A> as Arbitrary>::dearbitrary(&self.to_vec())
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <Vec<A> as Arbitrary>::size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for Box<str> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Rc<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        crate::size_hint::recursion_guard(depth, <A as Arbitrary>::size_hint)
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for Cell<A> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<'a, A: Arbitrary<'a>> Arbitrary<'a> for ::std::marker::PhantomData<A> {
    fn arbitrary(_: &mut Unstructured<'a>) -> Result<Self> {
        Ok(::std::marker::PhantomData)
    }

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

            fn dearbitrary(&self) -> Vec<u8> {
                unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
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

    fn dearbitrary(&self) -> Vec<u8> {
        unimplemented!()
    }

    #[inline]
    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (16, Some(16))
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
    }

    #[test]
    fn dearbitrary_for_integers() {
        let x = 1 | (2 << 8) | (3 << 16) | (4 << 24);
        let expected = vec![1, 2, 3, 4];
        let actual = i32::dearbitrary(&x);
        assert_eq!(expected, actual);

        let x = 1 | (2 << 8) | (3 << 16) | (4 << 24) | (5 << 32) | (6 << 40) | (7 << 48) | (8 << 56);
        let expected = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let actual = i64::dearbitrary(&x);
        assert_eq!(expected, actual);

        let expected = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let mut buf = Unstructured::new(&expected);
        let x = i64::arbitrary(&mut buf).unwrap();
        let actual = i64::dearbitrary(&x);
        assert_eq!(expected, actual);

        let expected = vec![1, 2, 3, 4];
        let mut buf = Unstructured::new(&expected);
        let x = u32::arbitrary(&mut buf).unwrap();
        let actual = u32::dearbitrary(&x);
        assert_eq!(expected, actual);
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
    fn dearbitrary_for_bytes() {
        let x = &[1u8, 2u8, 3u8, 4u8];
        let expected = [1, 2, 3, 4, 4];
        let actual = <&[u8] as Arbitrary>::dearbitrary(&x.as_slice());
        assert_eq!(expected.as_slice(), actual);
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
            checked_arbitrary::<Vec<u32>>(&mut Unstructured::new(&x)).unwrap(),
            &[84148994]
        );
        assert_eq!(
            checked_arbitrary::<String>(&mut Unstructured::new(&x)).unwrap(),
            "\x01\x02\x03\x04\x05\x06\x07\x08\x09\x01\x02\x03"
        );
    }

    #[test]
    fn dearbitrary_collection() {
        let x = vec![2, 4, 6, 8, 1];
        let expected = [1, 2, 1, 4, 1, 6, 1, 8, 1, 1, 0];
        let actual = Vec::<u8>::dearbitrary(&x);
        assert_eq!(expected.as_slice(), actual);
    }

    #[test]
    fn arbitrary_take_rest() {
        let x = [1, 2, 3, 4];
        assert_eq!(
            checked_arbitrary_take_rest::<&[u8]>(Unstructured::new(&x)).unwrap(),
            &[1, 2, 3, 4]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u8>>(Unstructured::new(&x)).unwrap(),
            &[1, 2, 3, 4]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u32>>(Unstructured::new(&x)).unwrap(),
            &[0x4030201]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<String>(Unstructured::new(&x)).unwrap(),
            "\x01\x02\x03\x04"
        );

        assert_eq!(
            checked_arbitrary_take_rest::<&[u8]>(Unstructured::new(&[])).unwrap(),
            &[]
        );
        assert_eq!(
            checked_arbitrary_take_rest::<Vec<u8>>(Unstructured::new(&[])).unwrap(),
            &[]
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

    #[test]
    fn dearbitrary_tuples() {
        let x = [9, 0, 1, 2, 3, 4, 5, 6, 7, 8];
        let mut buf = Unstructured::new(&x);
        let t = <(u16,u32,u8,u8,u8,u8)>::arbitrary(&mut buf).unwrap();
        let actual = Arbitrary::dearbitrary(&t);

        assert_eq!(x.to_vec(), actual);

        let x = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut buf = Unstructured::new(&x);
        let t = <(bool, bool, u32,u8,u8,u8,u8)>::arbitrary(&mut buf).unwrap();
        let actual = Arbitrary::dearbitrary(&t);

        assert_eq!(x.to_vec(), actual);


        let x = [1, 0, 3, 4, 5, 0, 7, 8, 9, 0];
        let mut buf = Unstructured::new(&x);
        let t = <(u32, u8, bool,u8,u8,u8,u8)>::arbitrary(&mut buf).unwrap();
        let actual = Arbitrary::dearbitrary(&t);

        assert_eq!(x.to_vec(), actual);

        let x = (true, 2);
        let data = [1, 2, 0, 0, 0, 0, 0, 0, 0];
        let actual = <(bool, u64)>::dearbitrary(&x);
        assert_eq!(data.to_vec(), actual);
        let mut buf = Unstructured::new(&data);
        let expected = <(bool, u64)>::arbitrary(&mut buf).unwrap();
        assert_eq!(expected, x);
    }
}
