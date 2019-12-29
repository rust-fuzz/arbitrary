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

use std::borrow::{Cow, ToOwned};
use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::ffi::{CString, OsString};
use std::iter;
use std::mem;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

fn empty<T: 'static>() -> Box<dyn Iterator<Item = T>> {
    Box::new(iter::empty())
}

fn once<T: 'static>(val: T) -> Box<dyn Iterator<Item = T>> {
    Box::new(iter::once(val))
}

/// Generate arbitrary structured values from raw, unstructured data.
///
/// The `Arbitrary` trait allows you to generate valid structured values, like
/// `HashMap`s, or ASTs, or `MyTomlConfig`, or any other data structure from
/// raw, unstructured bytes provided by a fuzzer. It also features built-in
/// shrinking, so that if you find a test case that triggers a bug, you can find
/// the smallest, most easiest-to-understand test case that still triggers that
/// bug.
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
/// arbitrary = { version = "0.2.0", features = ["derive"] }
/// ```
///
/// Then, you add the `#[derive(Arbitrary)]` annotation to your `struct` or
/// `enum` type definition:
///
/// ```
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
/// ```
///
/// Every member of the `struct` or `enum` must also implement `Arbitrary`.
///
/// # Implementing `Arbitrary` By Hand
///
/// Implementing `Arbitrary` mostly involves nested calls to other `Arbitrary`
/// arbitrary implementations for each of your `struct` or `enum`'s members. But
/// sometimes you need some amount of raw data, or you need to generate a
/// variably-sized collection type, or you something of that sort. The
/// [`Unstructured`][crate::Unstructured] type helps you with these tasks.
///
/// ```
/// use arbitrary::{Arbitrary, Result, Unstructured};
/// # pub struct MyCollection<T> { _t: std::marker::PhantomData<T> }
/// # impl<T> MyCollection<T> {
/// #     pub fn with_capacity(capacity: usize) -> Self { MyCollection { _t: std::marker::PhantomData } }
/// #     pub fn insert(&mut self, element: T) {}
/// # }
///
/// impl<T> Arbitrary for MyCollection<T>
/// where
///     T: Arbitrary,
/// {
///     fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
///         // Get the number of `T`s we should insert into our collection.
///         let len = u.arbitrary_len::<T>()?;
///
///         // And then create a collection of that length!
///         let mut my_collection = MyCollection::with_capacity(len);
///         for _ in 0..len {
///             let element = T::arbitrary(u)?;
///             my_collection.insert(element);
///         }
///
///         Ok(my_collection)
///     }
/// }
/// ```
pub trait Arbitrary: Sized + 'static {
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
    /// ```
    ///
    /// See also the documentation for [`Unstructured`][crate::Unstructured].
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self>;

    /// Generate an arbitrary value of `Self` from the entirety of the given unstructured data.
    ///
    /// This is similar to Arbitrary::arbitrary, however it assumes that it is the
    /// last consumer of the given data, and is thus able to consume it all if it needs.
    /// See also the documentation for [`Unstructured`][crate::Unstructured].
    fn arbitrary_take_rest(mut u: Unstructured<'_>) -> Result<Self> {
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
    /// [iterator-size-hint]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html#method.size_hint
    fn size_hint() -> (usize, Option<usize>) {
        (0, None)
    }

    /// Generate an iterator of derived values which are "smaller" than the
    /// original `self` instance.
    ///
    /// You can use this to help find the smallest test case that reproduces a
    /// bug.
    ///
    /// Using `#[derive(Arbitrary)]` will automatically implement shrinking for
    /// your type.
    ///
    /// However, if you are implementing `Arbirary` by hand and you want support
    /// for shrinking your type, you must override the default provided
    /// implementation of `shrink`, which just returns an empty iterator. You
    /// should try pretty hard to have your `shrink` implementation return a
    /// *lazy* iterator: one that computes the next value as it is needed,
    /// rather than computing them up front when `shrink` is first called.
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        empty()
    }
}

impl Arbitrary for () {
    fn arbitrary(_: &mut Unstructured<'_>) -> Result<Self> {
        Ok(())
    }

    fn size_hint() -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl Arbitrary for bool {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Ok(<u8 as Arbitrary>::arbitrary(u)? & 1 == 1)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <u8 as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(if *self { once(false) } else { empty() })
    }
}

macro_rules! impl_arbitrary_for_integers {
    ( $( $ty:ty: $unsigned:ty; )* ) => {
        $(
            impl Arbitrary for $ty {
                fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
                    let mut buf = [0; mem::size_of::<$ty>()];
                    u.fill_buffer(&mut buf)?;
                    let mut x: $unsigned = 0;
                    for i in 0..mem::size_of::<$ty>() {
                        x |= buf[i] as $unsigned << (i * 8);
                    }
                    Ok(x as $ty)
                }

                fn size_hint() -> (usize, Option<usize>) {
                    let n = mem::size_of::<$ty>();
                    (n, Some(n))
                }

                fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                    let mut x = *self;
                    if x == 0 {
                        return empty();
                    }
                    Box::new(iter::once(0).chain(std::iter::from_fn(move || {
                        x = x / 2;
                        if x == 0 {
                            None
                        } else {
                            Some(x)
                        }
                    })))
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
            impl Arbitrary for $ty {
                fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
                    Ok(Self::from_bits(<$unsigned as Arbitrary>::arbitrary(u)?))
                }

                fn size_hint() -> (usize, Option<usize>) {
                    <$unsigned as Arbitrary>::size_hint()
                }

                fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                    if *self == 0.0 {
                        empty()
                    } else if !self.is_finite() {
                        once(0.0)
                    } else {
                        let mut x = *self;
                        Box::new(iter::once(0.0).chain(iter::from_fn(move || {
                            // NB: do not test for zero like we do for integers
                            // because dividing by two until we reach a fixed
                            // point is NOT guaranteed to end at zero in
                            // non-default rounding modes of IEEE-754!
                            //
                            // For example, with 64-bit floats and the
                            // round-to-positive-infinity mode:
                            //
                            //     5e-324 / 2.0 == 5e-324
                            //
                            // (5e-234 is the smallest postive number that can
                            // be precisely represented in a 64-bit float.)
                            let y = x;
                            x = x / 2.0;
                            if x == y {
                                None
                            } else {
                                Some(x)
                            }
                        })))
                    }
                }
            }
        )*
    }
}

impl_arbitrary_for_floats! {
    f32: u32;
    f64: u64;
}

impl Arbitrary for char {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        use std::char;
        const CHAR_END: u32 = 0x0011_000;
        // The size of the surrogate blocks
        const SURROGATES_START: u32 = 0xD800;
        let mut c = <u32 as Arbitrary>::arbitrary(u)? % CHAR_END;
        if let Some(c) = char::from_u32(c) {
            return Ok(c);
        } else {
            // We found a surrogate, wrap and try again
            c -= SURROGATES_START;
            Ok(char::from_u32(c)
                .expect("Generated character should be valid! This is a bug in arbitrary-rs"))
        }
    }

    fn size_hint() -> (usize, Option<usize>) {
        <u32 as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = *self as u32;
        Box::new(x.shrink().filter_map(|x| {
            use std::convert::TryFrom;
            char::try_from(x).ok()
        }))
    }
}

impl Arbitrary for AtomicBool {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <bool as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        if self.load(Ordering::SeqCst) {
            once(AtomicBool::new(false))
        } else {
            empty()
        }
    }
}

impl Arbitrary for AtomicIsize {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <isize as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = self.load(Ordering::SeqCst);
        Box::new(x.shrink().map(Self::new))
    }
}

impl Arbitrary for AtomicUsize {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <usize as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = self.load(Ordering::SeqCst);
        Box::new(x.shrink().map(Self::new))
    }
}

impl Arbitrary for Duration {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Ok(Self::new(
            <u64 as Arbitrary>::arbitrary(u)?,
            <u32 as Arbitrary>::arbitrary(u)? % 1_000_000_000,
        ))
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(
            <u64 as Arbitrary>::size_hint(),
            <u32 as Arbitrary>::size_hint(),
        )
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            (self.as_secs(), self.subsec_nanos())
                .shrink()
                .map(|(secs, nanos)| Duration::new(secs, nanos % 1_000_000_000)),
        )
    }
}

impl<A: Arbitrary> Arbitrary for Option<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Ok(if <bool as Arbitrary>::arbitrary(u)? {
            Some(Arbitrary::arbitrary(u)?)
        } else {
            None
        })
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(
            <bool as Arbitrary>::size_hint(),
            <A as Arbitrary>::size_hint(),
        )
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        if let Some(ref a) = *self {
            Box::new(iter::once(None).chain(a.shrink().map(Some)))
        } else {
            empty()
        }
    }
}

impl<A: Arbitrary, B: Arbitrary> Arbitrary for std::result::Result<A, B> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Ok(if <bool as Arbitrary>::arbitrary(u)? {
            Ok(<A as Arbitrary>::arbitrary(u)?)
        } else {
            Err(<B as Arbitrary>::arbitrary(u)?)
        })
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(
            <bool as Arbitrary>::size_hint(),
            crate::size_hint::or(<A as Arbitrary>::size_hint(), <B as Arbitrary>::size_hint()),
        )
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match *self {
            Ok(ref a) => Box::new(a.shrink().map(Ok)),
            Err(ref b) => Box::new(b.shrink().map(Err)),
        }
    }
}

macro_rules! arbitrary_tuple {
    () => {};
    ($x: ident $($xs: ident)*) => {
        arbitrary_tuple!($($xs)*);

        impl<$x: Arbitrary, $($xs: Arbitrary),*> Arbitrary for ($x, $($xs),*) {
            fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
                Ok((Arbitrary::arbitrary(u)?, $($xs::arbitrary(u)?),*))
            }

            fn size_hint() -> (usize, Option<usize>) {
                crate::size_hint::and_all(&[
                    <$x as Arbitrary>::size_hint(),
                    $( <$xs as Arbitrary>::size_hint() ),*
                ])
            }

            #[allow(non_snake_case)]
            fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                let ( $x, $( $xs ),* ) = self;
                let ( mut $x, $( mut $xs ),* ) = ( $x.shrink(), $( $xs.shrink() ),* );
                Box::new(iter::from_fn(move || {
                    Some(( $x.next()?, $( $xs.next()? ),* ))
                }))
            }
        }
    };
}
arbitrary_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);

macro_rules! arbitrary_array {
    {$n:expr, $t:ident $($ts:ident)*} => {
        arbitrary_array!{($n - 1), $($ts)*}

        impl<T: Arbitrary> Arbitrary for [T; $n] {
            fn arbitrary(u: &mut Unstructured<'_>) -> Result<[T; $n]> {
                Ok([
                    Arbitrary::arbitrary(u)?,
                    $(<$ts as Arbitrary>::arbitrary(u)?),*
                ])
            }

            fn size_hint() -> (usize, Option<usize>) {
                crate::size_hint::and_all(&[
                    <$t as Arbitrary>::size_hint(),
                    $( <$ts as Arbitrary>::size_hint() ),*
                ])
            }

            #[allow(unused_mut)] // For the `[T; 1]` case.
            fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                let mut i = 0;
                let mut shrinkers = [
                    self[i].shrink(),
                    $({
                        i += 1;
                        let t: &$ts = &self[i];
                        t.shrink()
                    }),*
                ];
                Box::new(iter::from_fn(move || {
                    let mut i = 0;
                    Some([
                        shrinkers[i].next()?,
                        $({
                            i += 1;
                            let t: $ts = shrinkers[i].next()?;
                            t
                        }),*
                    ])
                }))
            }
        }
    };
    ($n: expr,) => {};
}

arbitrary_array! { 32, T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T }

fn shrink_collection<'a, T, A: Arbitrary>(
    entries: impl Iterator<Item = T>,
    f: impl Fn(&T) -> Box<dyn Iterator<Item = A>>,
) -> Box<dyn Iterator<Item = Vec<A>>> {
    let entries: Vec<_> = entries.collect();
    if entries.is_empty() {
        return empty();
    }

    let mut shrinkers: Vec<Vec<_>> = vec![];
    let mut i = entries.len();
    loop {
        shrinkers.push(entries.iter().take(i).map(&f).collect());
        i = i / 2;
        if i == 0 {
            break;
        }
    }
    Box::new(iter::once(vec![]).chain(iter::from_fn(move || loop {
        let mut shrinker = shrinkers.pop()?;
        let x: Option<Vec<A>> = shrinker.iter_mut().map(|s| s.next()).collect();
        if x.is_none() {
            continue;
        }
        shrinkers.push(shrinker);
        return x;
    })))
}

impl<A: Arbitrary> Arbitrary for Vec<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        shrink_collection(self.iter(), |x| x.shrink())
    }
}

impl<K: Arbitrary + Ord, V: Arbitrary> Arbitrary for BTreeMap<K, V> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections =
            shrink_collection(self.iter(), |(k, v)| Box::new(k.shrink().zip(v.shrink())));
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BTreeSet<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BinaryHeap<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<K: Arbitrary + Eq + ::std::hash::Hash, V: Arbitrary> Arbitrary for HashMap<K, V> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections =
            shrink_collection(self.iter(), |(k, v)| Box::new(k.shrink().zip(v.shrink())));
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Eq + ::std::hash::Hash> Arbitrary for HashSet<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary> Arbitrary for LinkedList<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary> Arbitrary for VecDeque<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        u.arbitrary_iter()?.collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A> Arbitrary for Cow<'static, A>
where
    A: ToOwned + ?Sized,
    <A as ToOwned>::Owned: Arbitrary,
{
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <<A as ToOwned>::Owned as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match *self {
            Cow::Owned(ref o) => Box::new(o.shrink().map(Cow::Owned)),
            Cow::Borrowed(b) => Box::new(b.to_owned().shrink().map(Cow::Owned)),
        }
    }
}

impl Arbitrary for String {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        let size = u.arbitrary_len::<char>()?;
        (0..size)
            .map(|_| <char as Arbitrary>::arbitrary(u))
            .collect()
    }

    fn size_hint() -> (usize, Option<usize>) {
        crate::size_hint::and(<usize as Arbitrary>::size_hint(), (0, None))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.chars(), |ch| ch.shrink());
        Box::new(collections.map(|chars| chars.into_iter().collect()))
    }
}

impl Arbitrary for CString {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        <Vec<u8> as Arbitrary>::arbitrary(u).map(|mut x| {
            x.retain(|&c| c != 0);
            Self::new(x).unwrap()
        })
    }

    fn size_hint() -> (usize, Option<usize>) {
        <Vec<u8> as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.as_bytes().iter(), |b| {
            Box::new(b.shrink().filter(|&b| b != 0))
        });
        Box::new(collections.map(|bytes| Self::new(bytes).unwrap()))
    }
}

impl Arbitrary for OsString {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(From::from)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <String as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match self.clone().into_string() {
            Err(_) if self.is_empty() => empty(),
            Err(_) => once(OsString::from("".to_string())),
            Ok(s) => Box::new(s.shrink().map(From::from)),
        }
    }
}

impl Arbitrary for PathBuf {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        <OsString as Arbitrary>::arbitrary(u).map(From::from)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <OsString as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let s = self.clone().into_os_string();
        Box::new(s.shrink().map(From::from))
    }
}

impl<A: Arbitrary> Arbitrary for Box<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((&**self).shrink().map(Self::new))
    }
}

impl<A: Arbitrary> Arbitrary for Box<[A]> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        <Vec<A> as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_slice())
    }

    fn size_hint() -> (usize, Option<usize>) {
        <Vec<A> as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(shrink_collection(self.iter(), |x| x.shrink()).map(|v| v.into_boxed_slice()))
    }
}

impl Arbitrary for Box<str> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }

    fn size_hint() -> (usize, Option<usize>) {
        <String as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.chars(), |ch| ch.shrink());
        Box::new(collections.map(|chars| chars.into_iter().collect::<String>().into_boxed_str()))
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

impl<A: Arbitrary> Arbitrary for Arc<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((&**self).shrink().map(Self::new))
    }
}

impl<A: Arbitrary> Arbitrary for Rc<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((&**self).shrink().map(Self::new))
    }
}

impl<A: Arbitrary> Arbitrary for Cell<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    // Note: can't implement `shrink` without either more trait bounds on `A`
    // (copy or default) or `Cell::update`:
    // https://github.com/rust-lang/rust/issues/50186
}

impl<A: Arbitrary> Arbitrary for RefCell<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = self.borrow();
        Box::new(x.shrink().map(Self::new))
    }
}

impl<A: Arbitrary> Arbitrary for UnsafeCell<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    // We can't non-trivially (i.e. not an empty iterator) implement `shrink` in
    // a safe way, since we don't have a safe way to get the inner value.
}

impl<A: Arbitrary> Arbitrary for Mutex<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match self.lock() {
            Err(_) => empty(),
            Ok(g) => Box::new(g.shrink().map(Self::new)),
        }
    }
}

impl<A: Arbitrary> Arbitrary for iter::Empty<A> {
    fn arbitrary(_: &mut Unstructured<'_>) -> Result<Self> {
        Ok(iter::empty())
    }

    fn size_hint() -> (usize, Option<usize>) {
        (0, Some(0))
    }

    // Nothing to shrink here.
}

impl<A: Arbitrary> Arbitrary for ::std::marker::PhantomData<A> {
    fn arbitrary(_: &mut Unstructured<'_>) -> Result<Self> {
        Ok(::std::marker::PhantomData)
    }

    fn size_hint() -> (usize, Option<usize>) {
        (0, Some(0))
    }

    // Nothing to shrink here.
}

impl<A: Arbitrary> Arbitrary for ::std::num::Wrapping<A> {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Arbitrary::arbitrary(u).map(::std::num::Wrapping)
    }

    fn size_hint() -> (usize, Option<usize>) {
        <A as Arbitrary>::size_hint()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let ref x = self.0;
        Box::new(x.shrink().map(::std::num::Wrapping))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn finite_buffer_fill_buffer() {
        let x = [1, 2, 3, 4];
        let mut rb = Unstructured::new(&x);
        let mut z = [0; 2];
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [1, 2]);
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [3, 4]);
        assert!(rb.fill_buffer(&mut z).is_err());
    }

    #[test]
    fn arbitrary_for_integers() {
        let x = [1, 2, 3, 4];
        let mut buf = Unstructured::new(&x);
        let expected = 1 | (2 << 8) | (3 << 16) | (4 << 24);
        let actual = i32::arbitrary(&mut buf).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn shrink_tuple() {
        let tup = (10, 20, 30);
        assert_eq!(
            tup.shrink().collect::<Vec<_>>(),
            [(0, 0, 0), (5, 10, 15), (2, 5, 7), (1, 2, 3)]
        );
    }

    #[test]
    fn shrink_array() {
        let tup = [10, 20, 30];
        assert_eq!(
            tup.shrink().collect::<Vec<_>>(),
            [[0, 0, 0], [5, 10, 15], [2, 5, 7], [1, 2, 3]]
        );
    }

    #[test]
    fn shrink_vec() {
        let v = vec![4, 4, 4, 4];
        assert_eq!(
            v.shrink().collect::<Vec<_>>(),
            [
                vec![],
                vec![0],
                vec![2],
                vec![1],
                vec![0, 0],
                vec![2, 2],
                vec![1, 1],
                vec![0, 0, 0, 0],
                vec![2, 2, 2, 2],
                vec![1, 1, 1, 1]
            ]
        );
    }

    #[test]
    fn shrink_string() {
        let s = "aaaa".to_string();
        assert_eq!(
            s.shrink().collect::<Vec<_>>(),
            [
                "",
                "\u{0}",
                "0",
                "\u{18}",
                "\u{c}",
                "\u{6}",
                "\u{3}",
                "\u{1}",
                "\u{0}\u{0}",
                "00",
                "\u{18}\u{18}",
                "\u{c}\u{c}",
                "\u{6}\u{6}",
                "\u{3}\u{3}",
                "\u{1}\u{1}",
                "\u{0}\u{0}\u{0}\u{0}",
                "0000",
                "\u{18}\u{18}\u{18}\u{18}",
                "\u{c}\u{c}\u{c}\u{c}",
                "\u{6}\u{6}\u{6}\u{6}",
                "\u{3}\u{3}\u{3}\u{3}",
                "\u{1}\u{1}\u{1}\u{1}"
            ]
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn shrink_cstring() {
        let s = CString::new(b"aaaa".to_vec()).unwrap();
        assert_eq!(
            s.shrink().collect::<Vec<_>>(),
            [
                &[][..],
                &[b'0'][..],
                &[0x18][..],
                &[0x0c][..],
                &[0x06][..],
                &[0x03][..],
                &[0x01][..],
                &[b'0', b'0'][..],
                &[0x18, 0x18][..],
                &[0x0c, 0x0c][..],
                &[0x06, 0x06][..],
                &[0x03, 0x03][..],
                &[0x01, 0x01][..],
                &[b'0', b'0', b'0', b'0'][..],
                &[0x18, 0x18, 0x18, 0x18][..],
                &[0x0c, 0x0c, 0x0c, 0x0c][..],
                &[0x06, 0x06, 0x06, 0x06][..],
                &[0x03, 0x03, 0x03, 0x03][..],
                &[0x01, 0x01, 0x01, 0x01][..],
            ]
            .iter()
            .map(|s| CString::new(s.to_vec()).unwrap())
            .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn size_hint_for_tuples() {
        assert_eq!((7, Some(7)), <(bool, u16, i32) as Arbitrary>::size_hint());
        assert_eq!(
            (1 + mem::size_of::<usize>(), None),
            <(u8, Vec<u8>) as Arbitrary>::size_hint()
        );
    }
}
