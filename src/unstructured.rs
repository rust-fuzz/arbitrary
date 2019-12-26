// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{Arbitrary, Error, Result};
use std::{iter, slice};

/// A source of unstructured data with a finite size
///
/// This buffer is a finite source of unstructured data. Once the data is
/// exhausted it stays exhausted.
pub struct Unstructured<'a> {
    buffer: &'a [u8],
    offset: usize,
    max_len: usize,
}

impl<'a> Unstructured<'a> {
    /// Create a new Unstructured
    ///
    /// If the passed `buffer` is shorter than max_len the total number of bytes
    /// will be the bytes available in `buffer`. If `buffer` is longer than
    /// `max_len` the buffer will be trimmed.
    pub fn new(buffer: &'a [u8], max_len: usize) -> Result<Self> {
        let buf: &'a [u8] = if buffer.len() > max_len {
            &buffer[..max_len]
        } else {
            // This branch is hit if buffer is shorter than max_len. We might
            // choose to make this an error condition instead of, potentially,
            // surprising folks with less bytes.
            buffer
        };

        Ok(Unstructured {
            buffer: buf,
            offset: 0,
            max_len: buf.len(),
        })
    }

    /// Fill a `buffer` with bytes, forming the unstructured data from which
    /// `Arbitrary` structured data shall be generated.
    ///
    /// If this `Unstructured` cannot fill the whole `buffer`, an error is
    /// returned.
    pub fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<()> {
        if (self.max_len - self.offset) >= buffer.len() {
            let max = self.offset + buffer.len();
            for (i, idx) in (self.offset..max).enumerate() {
                buffer[i] = self.buffer[idx];
            }
            self.offset = max;
            Ok(())
        } else {
            Err(Error::NotEnoughData)
        }
    }

    /// Generate a size for container or collection, e.g. the number of elements
    /// in a vector.
    pub fn container_size(&mut self) -> Result<usize> {
        <usize as Arbitrary>::arbitrary(self).map(|x| x % self.max_len)
    }

    /// Get the number of bytes of underlying data that is still available.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3], 3)
    ///     .expect("`Unstructured::new` will never fail on non-empty input");
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
        self.buffer.len().saturating_sub(self.offset)
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
    /// let mut u = Unstructured::new(&[1, 2, 3, 4], 4)
    ///     .expect("`Unstructured::new` will never fail on non-empty input");
    ///
    /// // Initially, we are not empty.
    /// assert!(!u.is_empty());
    ///
    /// // Generating a `u32` consumes all four bytes of the underlying data, so
    /// // we become empty afterwards.
    /// let _ = u32::arbitrary(&mut u);
    /// assert!(u.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    /// let mut u = Unstructured::new(&[1, 2, 3], 3)
    ///     .expect("`Unstructured::new` will never fail when given non-empty data");
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
        if self.offset >= self.buffer.len() {
            Err(Error::NotEnoughData)
        } else {
            let offset = self.offset;
            self.offset = self.buffer.len();
            Ok(TakeRest {
                inner: self.buffer[offset..].iter().cloned(),
            })
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
