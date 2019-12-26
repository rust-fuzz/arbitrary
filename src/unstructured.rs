// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Wrappers around raw, unstructured bytes.

use crate::{Arbitrary, Error, Result};
use std::{iter, mem, ops, slice};

/// A source of unstructured data with a finite size
///
/// This buffer is a finite source of unstructured data. Once the data is
/// exhausted it stays exhausted.
pub struct Unstructured<'a> {
    data: &'a [u8],
}

impl<'a> Unstructured<'a> {
    /// Create a new `Unstructured`.
    pub fn new(data: &'a [u8]) -> Self {
        Unstructured { data }
    }

    /// Fill a `buffer` with bytes, forming the unstructured data from which
    /// `Arbitrary` structured data shall be generated.
    ///
    /// If this `Unstructured` cannot fill the whole `buffer`, an error is
    /// returned.
    pub fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<()> {
        if self.data.len() < buffer.len() {
            return Err(Error::NotEnoughData);
        }

        let (for_buf, rest) = self.data.split_at(buffer.len());
        self.data = rest;
        buffer.copy_from_slice(for_buf);
        Ok(())
    }

    /// Generate a size for container or collection, e.g. the number of elements
    /// in a vector.
    pub fn container_size(&mut self) -> Result<usize> {
        let n = usize::arbitrary(self)?;
        if self.data.is_empty() {
            Err(Error::NotEnoughData)
        } else {
            Ok(n % self.data.len())
        }
    }

    /// Get the number of bytes of underlying data that is still available.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3]);
    ///
    /// // Initially have three bytes of data.
    /// assert_eq!(u.len(), 3);
    ///
    /// // Generating a `bool` consumes one byte from the underlying data, so
    /// // we are left with two bytes afterwards.
    /// let _ = bool::arbitrary(&mut u);
    /// assert_eq!(u.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Is the underlying unstructured data exhausted?
    ///
    /// `unstructured.is_empty()` is the same as `unstructured.len() == 0`.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4]);
    ///
    /// // Initially, we are not empty.
    /// assert!(!u.is_empty());
    ///
    /// // Generating a `u32` consumes all four bytes of the underlying data, so
    /// // we become empty afterwards.
    /// let _ = u32::arbitrary(&mut u);
    /// assert!(u.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Generate an integer within the given range.
    ///
    /// Do not use this to generate the size of a collection. Use
    /// `container_size` instead.
    ///
    /// # Panics
    ///
    /// Panics if `range.start >= range.end`. That is, the given range must be
    /// non-empty.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4]);
    ///
    /// let x: i32 = u.int_in_range(-5_000..=-1_000)
    ///     .expect("constructed `u` with enough bytes to generate an `i32`");
    ///
    /// assert!(-5_000 <= x);
    /// assert!(x <= -1_000);
    /// ```
    pub fn int_in_range<T>(&mut self, range: ops::RangeInclusive<T>) -> Result<T>
    where
        T: Int,
    {
        let (result, bytes_consumed) = Self::int_in_range_impl(range, self.data.iter().cloned())?;
        self.data = &self.data[bytes_consumed..];
        Ok(result)
    }

    fn int_in_range_impl<T>(
        range: ops::RangeInclusive<T>,
        mut bytes: impl Iterator<Item = u8>,
    ) -> Result<(T, usize)>
    where
        T: Int,
    {
        let start = range.start();
        let end = range.end();
        assert!(
            start < end,
            "`arbitrary::Unstructured::int_in_range` requires a non-empty range"
        );

        let range: T::Widest = end.as_widest() - start.as_widest();
        let mut result = T::Widest::ZERO;
        let mut offset: usize = 0;

        while offset < mem::size_of::<T>()
            && (range >> T::Widest::from_usize(offset)) > T::Widest::ZERO
        {
            let byte = bytes.next().ok_or(Error::NotEnoughData)?;
            result = (result << 8) | T::Widest::from_u8(byte);
            offset += 1;
        }

        // Avoid division by zero.
        if let Some(range) = range.checked_add(T::Widest::ONE) {
            result = result % range;
        }

        Ok((
            T::from_widest(start.as_widest().wrapping_add(result)),
            offset,
        ))
    }

    /// Consume all of the rest of the remaining underlying bytes.
    ///
    /// Returns a non-empty iterator of all the remaining bytes.
    ///
    /// If the underlying data is already exhausted, returns an error.
    ///
    /// Any future requests for bytes will fail afterwards, since the underlying
    /// data has already been exhausted.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3]);
    ///
    /// let mut rem = u.take_rest()
    ///     .expect("we know that `u` is non-empty, so `take_rest` cannot fail");
    ///
    /// assert_eq!(rem.next(), Some(1));
    /// assert_eq!(rem.next(), Some(2));
    /// assert_eq!(rem.next(), Some(3));
    /// assert_eq!(rem.next(), None);
    /// ```
    pub fn take_rest(&mut self) -> Result<TakeRest<'a>> {
        if self.data.is_empty() {
            Err(Error::NotEnoughData)
        } else {
            let inner = self.data.iter().cloned();
            self.data = &[];
            Ok(TakeRest { inner })
        }
    }
}

/// An iterator of the remaining bytes returned by
/// `Unstructured::take_rest`.
pub struct TakeRest<'a> {
    inner: iter::Cloned<slice::Iter<'a, u8>>,
}

impl Iterator for TakeRest<'_> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.inner.next()
    }
}

/// A trait that is implemented for all of the primitive integers:
///
/// * `u8`
/// * `u16`
/// * `u32`
/// * `u64`
/// * `u128`
/// * `usize`
/// * `i8`
/// * `i16`
/// * `i32`
/// * `i64`
/// * `i128`
/// * `isize`
///
/// Don't implement this trait yourself.
pub trait Int:
    Copy
    + PartialOrd
    + Ord
    + ops::Sub<Self, Output = Self>
    + ops::Rem<Self, Output = Self>
    + ops::Shr<Self, Output = Self>
    + ops::Shl<usize, Output = Self>
    + ops::BitOr<Self, Output = Self>
{
    #[doc(hidden)]
    type Widest: Int;

    #[doc(hidden)]
    const ZERO: Self;

    #[doc(hidden)]
    const ONE: Self;

    #[doc(hidden)]
    fn as_widest(self) -> Self::Widest;

    #[doc(hidden)]
    fn from_widest(w: Self::Widest) -> Self;

    #[doc(hidden)]
    fn from_u8(b: u8) -> Self;

    #[doc(hidden)]
    fn from_usize(u: usize) -> Self;

    #[doc(hidden)]
    fn checked_add(self, rhs: Self) -> Option<Self>;

    #[doc(hidden)]
    fn wrapping_add(self, rhs: Self) -> Self;
}

macro_rules! impl_int {
    ( $( $ty:ty : $widest:ty ; )* ) => {
        $(
            impl Int for $ty {
                type Widest = $widest;

                const ZERO: Self = 0;

                const ONE: Self = 1;

                fn as_widest(self) -> Self::Widest {
                    self as $widest
                }

                fn from_widest(w: Self::Widest) -> Self {
                    let x = <$ty>::max_value().as_widest();
                    (w % x) as Self
                }

                fn from_u8(b: u8) -> Self {
                    b as Self
                }

                fn from_usize(u: usize) -> Self {
                    u as Self
                }

                fn checked_add(self, rhs: Self) -> Option<Self> {
                    <$ty>::checked_add(self, rhs)
                }

                fn wrapping_add(self, rhs: Self) -> Self {
                    <$ty>::wrapping_add(self, rhs)
                }
            }
        )*
    }
}

impl_int! {
    u8: u128;
    u16: u128;
    u32: u128;
    u64: u128;
    u128: u128;
    usize: u128;
    i8: i128;
    i16: i128;
    i32: i128;
    i64: i128;
    i128: i128;
    isize: i128;
}
