// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Arbitrary trait crate
//!
//! This trait provides an `Arbitrary` trait to produce well-typed data from
//! byte buffers. The crate additionally provides different flavors of byte
//! buffers with useful semantics.
#![deny(bad_style)]
#![deny(missing_docs)]
#![deny(future_incompatible)]
#![deny(nonstandard_style)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(unused)]

#[cfg(feature = "derive")]
pub use derive_arbitrary::*;

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

/// Unstructured data from which structured `Arbitrary` data shall be generated.
///
/// This could be a random number generator, a static ring buffer of bytes or some such.
pub trait Unstructured {
    /// The error type for [`Unstructured`], see implementations for details
    type Error;
    /// Fill a `buffer` with bytes, forming the unstructured data from which
    /// `Arbitrary` structured data shall be generated.
    ///
    /// This operation is fallible to allow implementations based on e.g. I/O.
    fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<(), Self::Error>;

    /// Generate a size for container.
    ///
    /// e.g. number of elements in a vector
    fn container_size(&mut self) -> Result<usize, Self::Error> {
        <u8 as Arbitrary>::arbitrary(self).map(|x| x as usize)
    }
}

fn empty<T: 'static>() -> Box<dyn Iterator<Item = T>> {
    Box::new(iter::empty())
}

fn once<T: 'static>(val: T) -> Box<dyn Iterator<Item = T>> {
    Box::new(iter::once(val))
}

/// A trait to generate and shrink arbitrary types from an [`Unstructured`] pool
/// of bytes.
pub trait Arbitrary: Sized + 'static {
    /// Generate arbitrary structured data from unstructured data.
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error>;

    /// Generate derived values which are “smaller” than the original one.
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        empty()
    }
}

impl Arbitrary for () {
    fn arbitrary<U: Unstructured + ?Sized>(_: &mut U) -> Result<Self, U::Error> {
        Ok(())
    }
}

impl Arbitrary for bool {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<u8 as Arbitrary>::arbitrary(u)? & 1 == 1)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(if *self { once(false) } else { empty() })
    }
}

macro_rules! impl_arbitrary_for_integers {
    ( $( $ty:ty: $unsigned:ty; )* ) => {
        $(
            impl Arbitrary for $ty {
                fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
                    let mut buf = [0; mem::size_of::<$ty>()];
                    u.fill_buffer(&mut buf)?;
                    let mut x: $unsigned = 0;
                    for i in 0..mem::size_of::<$ty>() {
                        x |= buf[i] as $unsigned << (i * 8);
                    }
                    Ok(x as $ty)
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
                fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
                    Ok(Self::from_bits(<$unsigned as Arbitrary>::arbitrary(u)?))
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        const CHAR_MASK: u32 = 0x001f_ffff;
        let mut c = <u32 as Arbitrary>::arbitrary(u)? & CHAR_MASK;
        loop {
            // Cannot do rejection sampling which the rand crate does, because it may result in
            // infinite loop with unstructured data provided by a ring buffer. Instead we just pick
            // closest valid character which comes before the current one.
            //
            // Note, of course this does not result in unbiased data, but it is not really
            // necessary for either quickcheck or fuzzing.
            if let Some(c) = ::std::char::from_u32(c) {
                return Ok(c);
            } else {
                c -= 1;
            }
        }
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = self.load(Ordering::SeqCst);
        Box::new(x.shrink().map(Self::new))
    }
}

impl Arbitrary for AtomicUsize {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let x = self.load(Ordering::SeqCst);
        Box::new(x.shrink().map(Self::new))
    }
}

impl Arbitrary for Duration {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(Self::new(
            Arbitrary::arbitrary(u)?,
            <u32 as Arbitrary>::arbitrary(u)? % 1_000_000_000,
        ))
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(if Arbitrary::arbitrary(u)? {
            Some(Arbitrary::arbitrary(u)?)
        } else {
            None
        })
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        if let Some(ref a) = *self {
            Box::new(iter::once(None).chain(a.shrink().map(Some)))
        } else {
            empty()
        }
    }
}

impl<A: Arbitrary, B: Arbitrary> Arbitrary for Result<A, B> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(if Arbitrary::arbitrary(u)? {
            Ok(Arbitrary::arbitrary(u)?)
        } else {
            Err(Arbitrary::arbitrary(u)?)
        })
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match *self {
            Ok(ref a) => Box::new(a.shrink().map(Ok)),
            Err(ref a) => Box::new(a.shrink().map(Err)),
        }
    }
}

macro_rules! arbitrary_tuple {
    () => {};
    ($x: ident $($xs: ident)*) => {
        arbitrary_tuple!($($xs)*);

        impl<$x: Arbitrary, $($xs: Arbitrary),*> Arbitrary for ($x, $($xs),*) {
            fn arbitrary<_U: Unstructured + ?Sized>(u: &mut _U) -> Result<Self, _U::Error> {
                Ok((Arbitrary::arbitrary(u)?, $($xs::arbitrary(u)?),*))
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
            fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<[T; $n], U::Error> {
                Ok([
                    Arbitrary::arbitrary(u)?,
                    $(<$ts as Arbitrary>::arbitrary(u)?),*
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        shrink_collection(self.iter(), |x| x.shrink())
    }
}

impl<K: Arbitrary + Ord, V: Arbitrary> Arbitrary for BTreeMap<K, V> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections =
            shrink_collection(self.iter(), |(k, v)| Box::new(k.shrink().zip(v.shrink())));
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BTreeSet<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BinaryHeap<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<K: Arbitrary + Eq + ::std::hash::Hash, V: Arbitrary> Arbitrary for HashMap<K, V> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections =
            shrink_collection(self.iter(), |(k, v)| Box::new(k.shrink().zip(v.shrink())));
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary + Eq + ::std::hash::Hash> Arbitrary for HashSet<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary> Arbitrary for LinkedList<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.iter(), |v| v.shrink());
        Box::new(collections.map(|entries| entries.into_iter().collect()))
    }
}

impl<A: Arbitrary> Arbitrary for VecDeque<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
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
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match *self {
            Cow::Owned(ref o) => Box::new(o.shrink().map(Cow::Owned)),
            Cow::Borrowed(b) => Box::new(b.to_owned().shrink().map(Cow::Owned)),
        }
    }
}

impl Arbitrary for String {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size)
            .map(|_| <char as Arbitrary>::arbitrary(u))
            .collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.chars(), |ch| ch.shrink());
        Box::new(collections.map(|chars| chars.into_iter().collect()))
    }
}

impl Arbitrary for CString {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <Vec<u8> as Arbitrary>::arbitrary(u).map(|mut x| {
            x.retain(|&c| c != 0);
            Self::new(x).unwrap()
        })
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let collections = shrink_collection(self.as_bytes().iter(), |b| {
            Box::new(b.shrink().filter(|&b| b != 0))
        });
        Box::new(collections.map(|bytes| Self::new(bytes).unwrap()))
    }
}

impl Arbitrary for OsString {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <String as Arbitrary>::arbitrary(u).map(From::from)
    }
}

impl Arbitrary for PathBuf {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <OsString as Arbitrary>::arbitrary(u).map(From::from)
    }
}

impl<A: Arbitrary> Arbitrary for Box<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for Box<[A]> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <Vec<A> as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_slice())
    }
}

impl Arbitrary for Box<str> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <String as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_str())
    }
}

// impl Arbitrary for Box<CStr> {
//     fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
//         <CString as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_c_str())
//     }
// }

// impl Arbitrary for Box<OsStr> {
//     fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
//         <OsString as Arbitrary>::arbitrary(u).map(|x| x.into_boxed_osstr())
//
//     }
// }

impl<A: Arbitrary> Arbitrary for Arc<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for Rc<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for Cell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for RefCell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for UnsafeCell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for Mutex<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Self::new)
    }
}

impl<A: Arbitrary> Arbitrary for iter::Empty<A> {
    fn arbitrary<U: Unstructured + ?Sized>(_: &mut U) -> Result<Self, U::Error> {
        Ok(iter::empty())
    }
}

impl<A: Arbitrary> Arbitrary for ::std::marker::PhantomData<A> {
    fn arbitrary<U: Unstructured + ?Sized>(_: &mut U) -> Result<Self, U::Error> {
        Ok(::std::marker::PhantomData)
    }
}

impl<A: Arbitrary> Arbitrary for ::std::num::Wrapping<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(::std::num::Wrapping)
    }
}

/// An enumeration of buffer creation errors
#[derive(Debug, Clone, Copy)]
pub enum BufferError {
    /// The input buffer is empty, causing construction of some buffer types to
    /// fail
    EmptyInput,
}

/// A source of unstructured data with a finite size
///
/// This buffer is a finite source of unstructured data. Once the data is
/// exhausted it stays exhausted.
pub struct FiniteBuffer<'a> {
    buffer: &'a [u8],
    offset: usize,
    max_len: usize,
}

impl<'a> FiniteBuffer<'a> {
    /// Create a new FiniteBuffer
    ///
    /// If the passed `buffer` is shorter than max_len the total number of bytes
    /// will be the bytes available in `buffer`. If `buffer` is longer than
    /// `max_len` the buffer will be trimmed.
    pub fn new(buffer: &'a [u8], max_len: usize) -> Result<Self, BufferError> {
        let buf: &'a [u8] = if buffer.len() > max_len {
            &buffer[..max_len]
        } else {
            // This branch is hit if buffer is shorter than max_len. We might
            // choose to make this an error condition instead of, potentially,
            // surprising folks with less bytes.
            buffer
        };

        Ok(FiniteBuffer {
            buffer: buf,
            offset: 0,
            max_len: buf.len(),
        })
    }
}

impl<'a> Unstructured for FiniteBuffer<'a> {
    type Error = ();

    fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<(), Self::Error> {
        if (self.max_len - self.offset) >= buffer.len() {
            let max = self.offset + buffer.len();
            for (i, idx) in (self.offset..max).enumerate() {
                buffer[i] = self.buffer[idx];
            }
            self.offset = max;
            Ok(())
        } else {
            Err(())
        }
    }

    // NOTE(blt) I'm not sure if this is the right definition. I don't
    // understand the purpose of container_size.
    fn container_size(&mut self) -> Result<usize, Self::Error> {
        <usize as Arbitrary>::arbitrary(self).map(|x| x % self.max_len)
    }
}

/// A source of unstructured data which returns the same data over and over again
///
/// This buffer acts as a ring buffer over the source of unstructured data,
/// allowing for an infinite amount of not-very-random data.
pub struct RingBuffer<'a> {
    buffer: &'a [u8],
    offset: usize,
    max_len: usize,
}

impl<'a> RingBuffer<'a> {
    /// Create a new RingBuffer
    pub fn new(buffer: &'a [u8], max_len: usize) -> Result<Self, BufferError> {
        if buffer.is_empty() {
            return Err(BufferError::EmptyInput);
        }
        Ok(RingBuffer {
            buffer,
            offset: 0,
            max_len,
        })
    }
}

impl<'a> Unstructured for RingBuffer<'a> {
    type Error = ();
    fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<(), Self::Error> {
        let b = [&self.buffer[self.offset..], &self.buffer[..self.offset]];
        let it = ::std::iter::repeat(&b[..]).flat_map(|x| x).flat_map(|&x| x);
        self.offset = (self.offset + buffer.len()) % self.buffer.len();
        for (d, f) in buffer.iter_mut().zip(it) {
            *d = *f;
        }
        Ok(())
    }

    fn container_size(&mut self) -> Result<usize, Self::Error> {
        <usize as Arbitrary>::arbitrary(self).map(|x| x % self.max_len)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn finite_buffer_fill_buffer() {
        let x = [1, 2, 3, 4];
        let mut rb = FiniteBuffer::new(&x, 10).unwrap();
        let mut z = [0; 2];
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [1, 2]);
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [3, 4]);
        assert!(rb.fill_buffer(&mut z).is_err());
    }

    #[test]
    fn ring_buffer_fill_buffer() {
        let x = [1, 2, 3, 4];
        let mut rb = RingBuffer::new(&x, 2).unwrap();
        let mut z = [0; 10];
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [1, 2, 3, 4, 1, 2, 3, 4, 1, 2]);
        rb.fill_buffer(&mut z).unwrap();
        assert_eq!(z, [3, 4, 1, 2, 3, 4, 1, 2, 3, 4]);
    }

    #[test]
    fn ring_buffer_container_size() {
        let x = [1, 2, 3, 4, 5];
        let mut rb = RingBuffer::new(&x, 11).unwrap();
        assert_eq!(rb.container_size().unwrap(), 9);
        assert_eq!(rb.container_size().unwrap(), 1);
        assert_eq!(rb.container_size().unwrap(), 2);
        assert_eq!(rb.container_size().unwrap(), 6);
        assert_eq!(rb.container_size().unwrap(), 1);
    }

    #[test]
    fn arbitrary_for_integers() {
        let x = [1, 2, 3, 4];
        let mut buf = FiniteBuffer::new(&x, x.len()).unwrap();
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
}
