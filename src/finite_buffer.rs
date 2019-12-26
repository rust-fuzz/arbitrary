// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{Arbitrary, Unstructured};

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
