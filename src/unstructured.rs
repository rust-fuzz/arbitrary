// Copyright © 2019 The Rust Fuzz Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Wrappers around raw, unstructured bytes.

use crate::{Arbitrary, Dearbitrary, Error, Result, DearbitraryResult};
use std::marker::PhantomData;
use std::ops::ControlFlow;
use std::{mem, ops};

/// A source of unstructured data.
///
/// An `Unstructured` helps `Arbitrary` implementations interpret raw data
/// (typically provided by a fuzzer) as a "DNA string" that describes how to
/// construct the `Arbitrary` type. The goal is that a small change to the "DNA
/// string" (the raw data wrapped by an `Unstructured`) results in a small
/// change to the generated `Arbitrary` instance. This helps a fuzzer
/// efficiently explore the `Arbitrary`'s input space.
///
/// `Unstructured` is deterministic: given the same raw data, the same series of
/// API calls will return the same results (modulo system resource constraints,
/// like running out of memory). However, `Unstructured` does not guarantee
/// anything beyond that: it makes not guarantee that it will yield bytes from
/// the underlying data in any particular order.
///
/// You shouldn't generally need to use an `Unstructured` unless you are writing
/// a custom `Arbitrary` implementation by hand, instead of deriving it. Mostly,
/// you should just be passing it through to nested `Arbitrary::arbitrary`
/// calls.
///
/// # Example
///
/// Imagine you were writing a color conversion crate. You might want to write
/// fuzz tests that take a random RGB color and assert various properties, run
/// functions and make sure nothing panics, etc.
///
/// Below is what translating the fuzzer's raw input into an `Unstructured` and
/// using that to generate an arbitrary RGB color might look like:
///
/// ```
/// # #[cfg(feature = "derive")] fn foo() {
/// use arbitrary::{Arbitrary, Unstructured};
///
/// /// An RGB color.
/// #[derive(Arbitrary)]
/// pub struct Rgb {
///     r: u8,
///     g: u8,
///     b: u8,
/// }
///
/// // Get the raw bytes from the fuzzer.
/// #   let get_input_from_fuzzer = || &[];
/// let raw_data: &[u8] = get_input_from_fuzzer();
///
/// // Wrap it in an `Unstructured`.
/// let mut unstructured = Unstructured::new(raw_data);
///
/// // Generate an `Rgb` color and run our checks.
/// if let Ok(rgb) = Rgb::arbitrary(&mut unstructured) {
/// #   let run_my_color_conversion_checks = |_| {};
///     run_my_color_conversion_checks(rgb);
/// }
/// # }
/// ```
#[derive(Debug)]
pub struct Unstructured<'a> {
    data: &'a [u8],
}

impl<'a> Unstructured<'a> {
    /// Create a new `Unstructured` from the given raw data.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let u = Unstructured::new(&[1, 2, 3, 4]);
    /// ```
    pub fn new(data: &'a [u8]) -> Self {
        Unstructured { data }
    }

    /// Get the number of remaining bytes of underlying data that are still
    /// available.
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

    /// Generate an arbitrary instance of `A`.
    ///
    /// This is simply a helper method that is equivalent to `<A as
    /// Arbitrary>::arbitrary(self)`. This helper is a little bit more concise,
    /// and can be used in situations where Rust's type inference will figure
    /// out what `A` should be.
    ///
    /// # Example
    ///
    /// ```
    /// # #[cfg(feature="derive")] fn foo() -> arbitrary::Result<()> {
    /// use arbitrary::{Arbitrary, Unstructured};
    ///
    /// #[derive(Arbitrary)]
    /// struct MyType {
    ///     // ...
    /// }
    ///
    /// fn do_stuff(value: MyType) {
    /// #   let _ = value;
    ///     // ...
    /// }
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4]);
    ///
    /// // Rust's type inference can figure out that `value` should be of type
    /// // `MyType` here:
    /// let value = u.arbitrary()?;
    /// do_stuff(value);
    /// # Ok(()) }
    /// ```
    pub fn arbitrary<A>(&mut self) -> Result<A>
    where
        A: Arbitrary<'a>,
    {
        <A as Arbitrary<'a>>::arbitrary(self)
    }

    /// Get the number of elements to insert when building up a collection of
    /// arbitrary `ElementType`s.
    ///
    /// This uses the [`<ElementType as
    /// Arbitrary>::size_hint`][crate::Arbitrary::size_hint] method to smartly
    /// choose a length such that we most likely have enough underlying bytes to
    /// construct that many arbitrary `ElementType`s.
    ///
    /// This should only be called within an `Arbitrary` implementation.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::{Arbitrary, Result, Unstructured};
    /// # pub struct MyCollection<T> { _t: std::marker::PhantomData<T> }
    /// # impl<T> MyCollection<T> {
    /// #     pub fn with_capacity(capacity: usize) -> Self { MyCollection { _t: std::marker::PhantomData } }
    /// #     pub fn insert(&mut self, element: T) {}
    /// # }
    ///
    /// impl<'a, T> Arbitrary<'a> for MyCollection<T>
    /// where
    ///     T: Arbitrary<'a>,
    /// {
    ///     fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
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
    pub fn arbitrary_len<ElementType>(&mut self) -> Result<usize>
    where
        ElementType: Arbitrary<'a>,
    {
        let byte_size = self.arbitrary_byte_size()?;
        let (lower, upper) = ElementType::size_hint(0);
        let elem_size = upper.unwrap_or(lower * 2);
        let elem_size = std::cmp::max(1, elem_size);
        Ok(byte_size / elem_size)
    }

    fn arbitrary_byte_size(&mut self) -> Result<usize> {
        if self.data.is_empty() {
            Ok(0)
        } else if self.data.len() == 1 {
            self.data = &[];
            Ok(0)
        } else {
            // Take lengths from the end of the data, since the `libFuzzer` folks
            // found that this lets fuzzers more efficiently explore the input
            // space.
            //
            // https://github.com/rust-fuzz/libfuzzer-sys/blob/0c450753/libfuzzer/utils/FuzzedDataProvider.h#L92-L97

            // We only consume as many bytes as necessary to cover the entire
            // range of the byte string.
            // Note: We cast to u64 so we don't overflow when checking std::u32::MAX + 4 on 32-bit archs
            let len = if self.data.len() as u64 <= std::u8::MAX as u64 + 1 {
                let bytes = 1;
                let max_size = self.data.len() - bytes;
                let (rest, for_size) = self.data.split_at(max_size);
                self.data = rest;
                Self::int_in_range_impl(0..=max_size as u8, for_size.iter().copied())?.0 as usize
            } else if self.data.len() as u64 <= std::u16::MAX as u64 + 2 {
                let bytes = 2;
                let max_size = self.data.len() - bytes;
                let (rest, for_size) = self.data.split_at(max_size);
                self.data = rest;
                Self::int_in_range_impl(0..=max_size as u16, for_size.iter().copied())?.0 as usize
            } else if self.data.len() as u64 <= std::u32::MAX as u64 + 4 {
                let bytes = 4;
                let max_size = self.data.len() - bytes;
                let (rest, for_size) = self.data.split_at(max_size);
                self.data = rest;
                Self::int_in_range_impl(0..=max_size as u32, for_size.iter().copied())?.0 as usize
            } else {
                let bytes = 8;
                let max_size = self.data.len() - bytes;
                let (rest, for_size) = self.data.split_at(max_size);
                self.data = rest;
                Self::int_in_range_impl(0..=max_size as u64, for_size.iter().copied())?.0 as usize
            };

            Ok(len)
        }
    }

    /// Generate an integer within the given range.
    ///
    /// Do not use this to generate the size of a collection. Use
    /// `arbitrary_len` instead.
    ///
    /// # Panics
    ///
    /// Panics if `range.start > range.end`. That is, the given range must be
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
    pub fn int_in_range<T, const BYTES: usize>(&mut self, range: ops::RangeInclusive<T>) -> Result<T>
    where
        T: Int<BYTES>,
    {
        let (result, bytes_consumed) = Self::int_in_range_impl(range, self.data.iter().cloned())?;
        self.data = &self.data[bytes_consumed..];
        Ok(result)
    }

    fn int_in_range_impl<T, const BYTES: usize>(
        range: ops::RangeInclusive<T>,
        bytes: impl Iterator<Item = u8> + ExactSizeIterator,
    ) -> Result<(T, usize)>
    where
        T: Int<BYTES>,
    {
        let start = *range.start();
        let end = *range.end();
        assert!(
            start <= end,
            "`arbitrary::Unstructured::int_in_range` requires a non-empty range"
        );
        // When there is only one possible choice, don't waste any entropy from
        // the underlying data.
        if start == end {
            return Ok((start, 0));
        }

        // From here on out we work with the unsigned representation. All of the
        // operations performed below work out just as well whether or not `T`
        // is a signed or unsigned integer.
        let start = start.to_unsigned();
        let end = end.to_unsigned();

        let delta = end.wrapping_sub(start);
        debug_assert_ne!(delta, T::Unsigned::ZERO);

        // Compute an arbitrary integer offset from the start of the range. We
        // do this by consuming `min(size_of(T), bytes representing delta)`
        // bytes from the input to create an arbitrary integer and then
        // clamping that int into our range bounds with a modulo operation.

        let max_consumable_bytes = std::cmp::min(
            BYTES,
            delta.min_representable_bytes() as usize
        );

        let taken_bytes = bytes.take(max_consumable_bytes).collect::<Vec<_>>();

        let mut byte_slice = [0u8; BYTES];
        // never panics as consumed_slice.len() is always <= Bytes
        byte_slice[0..taken_bytes.len()].copy_from_slice(&taken_bytes);

        let arbitrary_int = T::Unsigned::from_le_bytes(byte_slice);

        let offset = if delta == T::Unsigned::MAX {
            arbitrary_int
        } else {
            arbitrary_int % (delta.checked_add(T::Unsigned::ONE).unwrap())
        };

        // Finally, we add `start` to our offset from `start` to get the result
        // actual value within the range.
        let result = start.wrapping_add(offset);

        // And convert back to our maybe-signed representation.
        let result = T::from_unsigned(result);
        debug_assert!(*range.start() <= result);
        debug_assert!(result <= *range.end());

        Ok((result, taken_bytes.len()))
    }

    /// Choose one of the given choices.
    ///
    /// This should only be used inside of `Arbitrary` implementations.
    ///
    /// Returns an error if there is not enough underlying data to make a
    /// choice or if no choices are provided.
    ///
    /// # Examples
    ///
    /// Selecting from an array of choices:
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    /// let choices = ['a', 'b', 'c', 'd', 'e', 'f', 'g'];
    ///
    /// let choice = u.choose(&choices).unwrap();
    ///
    /// println!("chose {}", choice);
    /// ```
    ///
    /// An error is returned if no choices are provided:
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    /// let choices: [char; 0] = [];
    ///
    /// let result = u.choose(&choices);
    ///
    /// assert!(result.is_err());
    /// ```
    pub fn choose<'b, T>(&mut self, choices: &'b [T]) -> Result<&'b T> {
        let idx = self.choose_index(choices.len())?;
        Ok(&choices[idx])
    }

    /// Choose one of the given iterator choices.
    ///
    /// This should only be used inside of `Arbitrary` implementations.
    ///
    /// Returns an error if there is not enough underlying data to make a
    /// choice or if no choices are provided.
    ///
    /// # Examples
    ///
    /// Selecting a random item from a set:
    ///
    /// ```
    /// use std::collections::BTreeSet;
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    /// let set = BTreeSet::from(['a', 'b', 'c']);
    ///
    /// let choice = u.choose_iter(set.iter()).unwrap();
    ///
    /// println!("chose {}", choice);
    /// ```
    pub fn choose_iter<T, I>(&mut self, choices: I) -> Result<T>
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut choices = choices.into_iter();
        let idx = self.choose_index(choices.len())?;
        let choice = choices
            .nth(idx)
            .expect("ExactSizeIterator should have correct len");
        Ok(choice)
    }

    /// Choose a value in `0..len`.
    ///
    /// Returns an error if the `len` is zero.
    ///
    /// # Examples
    ///
    /// Using Fisher–Yates shuffle shuffle to gerate an arbitrary permutation.
    ///
    /// [Fisher–Yates shuffle]: https://en.wikipedia.org/wiki/Fisher–Yates_shuffle
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    /// let mut permutation = ['a', 'b', 'c', 'd', 'e', 'f', 'g'];
    /// let mut to_permute = &mut permutation[..];
    /// while to_permute.len() > 1 {
    ///     let idx = u.choose_index(to_permute.len()).unwrap();
    ///     to_permute.swap(0, idx);
    ///     to_permute = &mut to_permute[1..];
    /// }
    ///
    /// println!("permutation: {:?}", permutation);
    /// ```
    ///
    /// An error is returned if the length is zero:
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    /// let array: [i32; 0] = [];
    ///
    /// let result = u.choose_index(array.len());
    ///
    /// assert!(result.is_err());
    /// ```
    pub fn choose_index(&mut self, len: usize) -> Result<usize> {
        if len == 0 {
            return Err(Error::EmptyChoose);
        }
        let idx = self.int_in_range(0..=len - 1)?;
        Ok(idx)
    }

    /// Generate a boolean according to the given ratio.
    ///
    /// # Panics
    ///
    /// Panics when the numerator and denominator do not meet these constraints:
    ///
    /// * `0 < numerator <= denominator`
    ///
    /// # Example
    ///
    /// Generate a boolean that is `true` five sevenths of the time:
    ///
    /// ```
    /// # fn foo() -> arbitrary::Result<()> {
    /// use arbitrary::Unstructured;
    ///
    /// # let my_data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 0];
    /// let mut u = Unstructured::new(&my_data);
    ///
    /// if u.ratio(5, 7)? {
    ///     // Take this branch 5/7 of the time.
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn ratio<T, const BYTES: usize>(&mut self, numerator: T, denominator: T) -> Result<bool>
    where
        T: Int<BYTES>,
    {
        assert!(T::ZERO < numerator);
        assert!(numerator <= denominator);
        let x = self.int_in_range(T::ONE..=denominator)?;
        Ok(x <= numerator)
    }

    /// Fill a `buffer` with bytes from the underlying raw data.
    ///
    /// This should only be called within an `Arbitrary` implementation. This is
    /// a very low-level operation. You should generally prefer calling nested
    /// `Arbitrary` implementations like `<Vec<u8>>::arbitrary` and
    /// `String::arbitrary` over using this method directly.
    ///
    /// If this `Unstructured` does not have enough underlying data to fill the
    /// whole `buffer`, it pads the buffer out with zeros.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4]);
    ///
    /// let mut buf = [0; 2];
    ///
    /// assert!(u.fill_buffer(&mut buf).is_ok());
    /// assert_eq!(buf, [1, 2]);
    ///
    /// assert!(u.fill_buffer(&mut buf).is_ok());
    /// assert_eq!(buf, [3, 4]);
    ///
    /// assert!(u.fill_buffer(&mut buf).is_ok());
    /// assert_eq!(buf, [0, 0]);
    /// ```
    pub fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<()> {
        let n = std::cmp::min(buffer.len(), self.data.len());
        buffer[..n].copy_from_slice(&self.data[..n]);
        for byte in buffer[n..].iter_mut() {
            *byte = 0;
        }
        self.data = &self.data[n..];
        Ok(())
    }

    /// Provide `size` bytes from the underlying raw data.
    ///
    /// This should only be called within an `Arbitrary` implementation. This is
    /// a very low-level operation. You should generally prefer calling nested
    /// `Arbitrary` implementations like `<Vec<u8>>::arbitrary` and
    /// `String::arbitrary` over using this method directly.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3, 4]);
    ///
    /// assert!(u.bytes(2).unwrap() == &[1, 2]);
    /// assert!(u.bytes(2).unwrap() == &[3, 4]);
    /// ```
    pub fn bytes(&mut self, size: usize) -> Result<&'a [u8]> {
        if self.data.len() < size {
            return Err(Error::NotEnoughData);
        }

        let (for_buf, rest) = self.data.split_at(size);
        self.data = rest;
        Ok(for_buf)
    }

    /// Peek at `size` number of bytes of the underlying raw input.
    ///
    /// Does not consume the bytes, only peeks at them.
    ///
    /// Returns `None` if there are not `size` bytes left in the underlying raw
    /// input.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let u = Unstructured::new(&[1, 2, 3]);
    ///
    /// assert_eq!(u.peek_bytes(0).unwrap(), []);
    /// assert_eq!(u.peek_bytes(1).unwrap(), [1]);
    /// assert_eq!(u.peek_bytes(2).unwrap(), [1, 2]);
    /// assert_eq!(u.peek_bytes(3).unwrap(), [1, 2, 3]);
    ///
    /// assert!(u.peek_bytes(4).is_none());
    /// ```
    pub fn peek_bytes(&self, size: usize) -> Option<&'a [u8]> {
        self.data.get(..size)
    }

    /// Consume all of the rest of the remaining underlying bytes.
    ///
    /// Returns a slice of all the remaining, unconsumed bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use arbitrary::Unstructured;
    ///
    /// let mut u = Unstructured::new(&[1, 2, 3]);
    ///
    /// let mut remaining = u.take_rest();
    ///
    /// assert_eq!(remaining, [1, 2, 3]);
    /// ```
    pub fn take_rest(mut self) -> &'a [u8] {
        mem::take(&mut self.data)
    }

    /// Provide an iterator over elements for constructing a collection
    ///
    /// This is useful for implementing [`Arbitrary::arbitrary`] on collections
    /// since the implementation is simply `u.arbitrary_iter()?.collect()`
    pub fn arbitrary_iter<'b, ElementType: Arbitrary<'a>>(
        &'b mut self,
    ) -> Result<ArbitraryIter<'a, 'b, ElementType>> {
        Ok(ArbitraryIter {
            u: &mut *self,
            _marker: PhantomData,
        })
    }

    /// Provide an iterator over elements for constructing a collection from
    /// all the remaining bytes.
    ///
    /// This is useful for implementing [`Arbitrary::arbitrary_take_rest`] on collections
    /// since the implementation is simply `u.arbitrary_take_rest_iter()?.collect()`
    pub fn arbitrary_take_rest_iter<ElementType: Arbitrary<'a>>(
        self,
    ) -> Result<ArbitraryTakeRestIter<'a, ElementType>> {
        Ok(ArbitraryTakeRestIter {
            u: self,
            _marker: PhantomData,
        })
    }

    /// Call the given function an arbitrary number of times.
    ///
    /// The function is given this `Unstructured` so that it can continue to
    /// generate arbitrary data and structures.
    ///
    /// You may optionaly specify minimum and maximum bounds on the number of
    /// times the function is called.
    ///
    /// You may break out of the loop early by returning
    /// `Ok(std::ops::ControlFlow::Break)`. To continue the loop, return
    /// `Ok(std::ops::ControlFlow::Continue)`.
    ///
    /// # Panics
    ///
    /// Panics if `min > max`.
    ///
    /// # Example
    ///
    /// Call a closure that generates an arbitrary type inside a context an
    /// arbitrary number of times:
    ///
    /// ```
    /// use arbitrary::{Result, Unstructured};
    /// use std::ops::ControlFlow;
    ///
    /// enum Type {
    ///     /// A boolean type.
    ///     Bool,
    ///
    ///     /// An integer type.
    ///     Int,
    ///
    ///     /// A list of the `i`th type in this type's context.
    ///     List(usize),
    /// }
    ///
    /// fn arbitrary_types_context(u: &mut Unstructured) -> Result<Vec<Type>> {
    ///     let mut context = vec![];
    ///
    ///     u.arbitrary_loop(Some(10), Some(20), |u| {
    ///         let num_choices = if context.is_empty() {
    ///             2
    ///         } else {
    ///             3
    ///         };
    ///         let ty = match u.int_in_range::<u8>(1..=num_choices)? {
    ///             1 => Type::Bool,
    ///             2 => Type::Int,
    ///             3 => Type::List(u.int_in_range(0..=context.len() - 1)?),
    ///             _ => unreachable!(),
    ///         };
    ///         context.push(ty);
    ///         Ok(ControlFlow::Continue(()))
    ///     })?;
    ///
    ///     // The number of loop iterations are constrained by the min/max
    ///     // bounds that we provided.
    ///     assert!(context.len() >= 10);
    ///     assert!(context.len() <= 20);
    ///
    ///     Ok(context)
    /// }
    /// ```
    pub fn arbitrary_loop(
        &mut self,
        min: Option<u32>,
        max: Option<u32>,
        mut f: impl FnMut(&mut Self) -> Result<ControlFlow<(), ()>>,
    ) -> Result<()> {
        let min = min.unwrap_or(0);
        let max = max.unwrap_or(u32::MAX);

        for _ in 0..self.int_in_range(min..=max)? {
            match f(self)? {
                ControlFlow::Continue(_) => continue,
                ControlFlow::Break(_) => break,
            }
        }

        Ok(())
    }
}

/// An intermediatery building struct for building an [Unstructured]
/// from [Dearbitary]-implementing objects.
pub struct UnstructuredBuilder {
    front: Vec<u8>,
    back: Vec<u8>
}

impl UnstructuredBuilder {
    /// Constructs an empty [UnstructuredBuilder].
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let b = UnstructuredBuilder::new();
    /// ```
    pub fn new() -> Self {
        UnstructuredBuilder {
            front: vec![],
            back: vec![]
        }
    }

    /// Constructs an [UnstructuredBuilder] with the given data.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let b = UnstructuredBuilder::new();
    /// ```
    pub fn new_with_vecs(front: Vec<u8>, back: Vec<u8>) -> Self {
        Self {
            front,
            back
        }
    }

    /// Pushes a byte to the front of the unstructured value.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.push_front(15u8);
    /// b.push_front(7u8);
    /// assert_eq!(b.len(), 2);
    /// ```
    pub fn push_front(&mut self, value: u8) {
        self.front.push(value);
    }

    /// Extends the front by an iterator.
    /// 
    /// Since [UnstructuredBuilder]'s `front` works in reverse,
    /// this iterator should be reversed from when it is usually arbitrated.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_front(1u8..5u8);
    /// assert_eq!(b.len(), 4);
    /// ```
    #[doc = include_str!("reverse_note.md")]
    pub fn extend_front<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        self.front.extend(iter);
    }

    /// Dearbitratates every value inside the passed iterator.
    /// 
    /// Generally, you would want to use [UnstructuredBuilder::extend_from_dearbitrary_iter_rev]
    /// to reverse the order of the passed iterator, unless this is already purposely in reverse
    /// for optimization reasons.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_from_dearbitrary_iter([1u8, 2u8].iter().copied());
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![2, 1]);
    /// ```
    #[doc = include_str!("reverse_note.md")]
    pub fn extend_from_dearbitrary_iter<
        'a,
        A: Dearbitrary<'a>,
        T: IntoIterator<Item = A>
    >(&mut self, iter: T) -> DearbitraryResult<()> {
        for value in iter {
            value.dearbitrary(self)?;
        }
        Ok(())
    }

    /// Dearbitrates every value in inside the passed iterator in reverse.
    /// 
    /// This is generally what you would want to do, as the front is later reversed
    /// to mimic how this structure would usually be when not built backwards.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_from_dearbitrary_iter_rev([1u8, 2u8].iter().copied());
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![1, 2]);
    /// ```
    pub fn extend_from_dearbitrary_iter_rev<
        'a,
        A: Dearbitrary<'a>,
        T: IntoIterator<Item = A, IntoIter = impl DoubleEndedIterator<Item = A>>
    >(&mut self, iter: T) -> DearbitraryResult<()> {
        for value in iter.into_iter().rev() {
            value.dearbitrary(self)?;
        }
        Ok(())
    }

    /// Extends the front from a slice.
    /// 
    /// Since [UnstructuredBuilder]'s `front` works in reverse,
    /// this slice should be reversed from when it is usually arbitrated.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_front_from_slice(&[1u8, 2u8]);
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![2, 1]);
    /// ```
    #[doc = include_str!("reverse_note.md")]
    pub fn extend_front_from_slice(&mut self, other: &[u8]) {
        self.front.extend_from_slice(other);
    }

    /// Pushes a byte to the back of the [UnstructuredBuilder].
    /// 
    #[doc = include_str!("back_note.md")]
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.push_front(1);
    /// b.push_back(2);
    /// b.push_front(3);
    /// b.push_back(4);
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![3, 1, 2, 4]);
    /// ```
    pub fn push_back(&mut self, value: u8) {
        self.back.push(value);
    }

    /// Extends the back by some iterator.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_back(1u8..=3u8);
    /// b.push_front(4);
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![4, 1, 2, 3]);
    /// ```
    #[doc = include_str!("back_note.md")]
    pub fn extend_back<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        self.back.extend(iter);
    }

    /// Extends the back by some slice of bytes.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_back_from_slice([1, 2, 3]);
    /// b.push_front(4);
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![4, 1, 2, 3]);
    /// ```
    #[doc = include_str!("back_note.md")]
    pub fn extend_back_from_slice(&mut self, other: &[u8]) {
        self.back.extend_from_slice(other);
    }

    /// Adds an dearbitratable iterator to this `UnstructuredBuilder`,
    /// along with its length information.
    pub fn extend_from_dearbitrary_iter_rev_with_length<'a, A, T>(
        &mut self, 
        iter: T
    ) -> DearbitraryResult<()>
    where
        A: Dearbitrary<'a>,
        T: DoubleEndedIterator<Item = A> + ExactSizeIterator<Item = A>
    {
        let iter_length = iter.len();
        
        self.extend_from_dearbitrary_iter_rev(iter)?;

        // Determine the amount of bytes we need to pretend to encode the max amount of possible
        // items in here; This mimics behavior found in `Unstructured::arbitrary_byte_size`.
        let byte_count = if self.len() as u64 <= std::u8::MAX as u64 + 1 {
            1
        } else if self.len() as u64 <= std::u16::MAX as u64 + 1 {
            2
        } else if self.len() as u64 <= std::u32::MAX as u64 + 1 {
            4
        } else {
            8
        };

        let max_size = self.len() - byte_count;

        // Encode the "expected" count of bytes - not the real amount, to help re-arbitrary later on.
        // This is the reverse of Unstructured::int_in_range_impl
        let (lower, upper) = A::size_hint(0);
        let elem_size = upper.unwrap_or(lower * 2);
        let elem_size = std::cmp::max(1, elem_size);
        let byte_size = iter_length * elem_size;

        self.back_bytes_from_constrained_int::<u64, 8>(0..=max_size as u64, byte_size as u64);

        Ok(())
    }

    /// This is the logical inverse of Unstructured::int_in_range_impl.
    /// 
    /// It converts a number and its constrained range to the smallest representable
    /// slice of bytes in big endian order.
    fn bytes_from_constrained_int<T, const BYTES: usize>(
        range: ops::RangeInclusive<T>,
        int: T
    ) -> Vec<u8>
    where 
        T: Int<BYTES> + core::fmt::Debug,
    {
        let start = *range.start();
        let end = *range.end();
        assert!(
            start <= end,
            "`UnstructuredBuilder::bytes_from_constrained_int` requires a non-empty range"
        );
        assert!(
            range.contains(&int),
            "`UnstructuredBuilder::bytes_from_constrained_int` requires {int:?} to be inside {range:?}."
        );

        if start == end {
            return vec![];
        }

        // int_in_range_impl works on unsigned numbers, which are then later converted to signed (if they
        // originally were)
        let start = start.to_unsigned();
        let end = end.to_unsigned();

        let delta = end.wrapping_sub(start);
        debug_assert_ne!(delta, T::Unsigned::ZERO);

        // start from the end - we need an unsigned number
        let int = int.to_unsigned();
        // offset lossly equals arbitrary_int (offset = arbitrary_int % (delta + 1), remainder information is lost)
        let arbitrary_int = int.wrapping_sub(start);

        arbitrary_int.to_le_bytes()[0..arbitrary_int.min_representable_bytes() as usize].to_vec()
    }

    /// Extends the front by some integer clasped to a range.
    /// 
    /// This is the inverse of [Unstructured::int_in_range].
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.front_bytes_from_constrained_int(0..=u8::MAX, 5u8);
    /// assert_eq!(builder.collect(), vec![5]);
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.front_bytes_from_constrained_int(5..=20u8, 6u8);
    /// assert_eq!(builder.collect(), vec![1]);
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.front_bytes_from_constrained_int(1_000u32..=20_000u32, 2_500u32);
    /// assert_eq!(builder.collect(), vec![5, 220]);
    /// //
    /// assert_eq!(u32::from_be_bytes([0u8, 0u8, 5u8, 220u8]), 1_500u32);
    /// ```
    pub fn front_bytes_from_constrained_int<T, const BYTES: usize>(
        &mut self,
        range: ops::RangeInclusive<T>,
        int: T
    )
    where
        T: Int<BYTES> + core::fmt::Debug
    {
        let bytes = Self::bytes_from_constrained_int(range, int);
        self.extend_front(bytes);
    }

    /// Extends the back by some integer clasped to a range.
    /// 
    /// This is the inverse of [Unstructured::int_in_range],
    /// generally for encoding length information.
    /// 
    /// See [UnstructuredBuilder::extend_from_dearbitrary_iter_rev_with_length].
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.back_bytes_from_constrained_int(0..=u8::MAX, 5u8);
    /// assert_eq!(builder.collect(), vec![5]);
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.back_bytes_from_constrained_int(5..=20u8, 6u8);
    /// assert_eq!(builder.collect(), vec![1]);
    /// 
    /// let mut builder = UnstructuredBuilder::new();
    /// builder.back_bytes_from_constrained_int(1_000u32..=20_000u32, 2_500u32);
    /// assert_eq!(builder.collect(), vec![5, 220]);
    /// //
    /// assert_eq!(u32::from_be_bytes([0u8, 0u8, 5u8, 220u8]), 1_500u32);
    /// ```
    pub fn back_bytes_from_constrained_int<T, const BYTES: usize>(
        &mut self,
        range: ops::RangeInclusive<T>,
        int: T
    )
    where
        T: Int<BYTES> + core::fmt::Debug
    {
        let mut bytes = Self::bytes_from_constrained_int(range, int);
        bytes.reverse();
        self.extend_back(bytes);
    }

    /// Gets the current amount of bytes inside this `UnstructuredBuilder`.
    /// 
    /// Length is a combination of both sides of this builder.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_back_from_slice(&[1, 2, 3]);
    /// b.extend_front_from_slice(&[4, 5, 6]);
    /// assert_eq!(b.len(), 6);
    /// ```
    pub fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    /// Collects and converts this instance into an owned `Vec<u8>`.
    /// This can be later be turned back into [Unstructured] or used
    /// for corpus generation purposes.
    /// 
    /// # Example
    /// 
    /// ```
    /// use arbitrary::UnstructuredBuilder;
    /// 
    /// let mut b = UnstructuredBuilder::new();
    /// b.extend_back_from_slice(&[1, 2, 3]);
    /// b.extend_front_from_slice(&[4, 5, 6]);
    /// let bytes = b.collect();
    /// assert_eq!(bytes, vec![6, 5, 4, 1, 2, 3]);
    /// ```
    pub fn collect(mut self) -> Vec<u8> {
        self.front.reverse();
        self.front.extend(self.back);
        self.front
    }
}

/// Utility iterator produced by [`Unstructured::arbitrary_iter`]
pub struct ArbitraryIter<'a, 'b, ElementType> {
    u: &'b mut Unstructured<'a>,
    _marker: PhantomData<ElementType>,
}

impl<'a, 'b, ElementType: Arbitrary<'a>> Iterator for ArbitraryIter<'a, 'b, ElementType> {
    type Item = Result<ElementType>;
    fn next(&mut self) -> Option<Result<ElementType>> {
        let keep_going = self.u.arbitrary().unwrap_or(false);
        if keep_going {
            Some(Arbitrary::arbitrary(self.u))
        } else {
            None
        }
    }
}

/// Utility iterator produced by [`Unstructured::arbitrary_take_rest_iter`]
pub struct ArbitraryTakeRestIter<'a, ElementType> {
    u: Unstructured<'a>,
    _marker: PhantomData<ElementType>,
}

impl<'a, ElementType: Arbitrary<'a>> Iterator for ArbitraryTakeRestIter<'a, ElementType> {
    type Item = Result<ElementType>;
    fn next(&mut self) -> Option<Result<ElementType>> {
        let keep_going = self.u.arbitrary().unwrap_or(false);
        if keep_going {
            Some(Arbitrary::arbitrary(&mut self.u))
        } else {
            None
        }
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
/// 
/// The `Bytes` generic defines how many bytes this number would take in the
/// worst possible case platform. `usize`
pub trait Int<const BYTES: usize>:
    Copy
    + std::fmt::Debug
    + PartialOrd
    + Ord
    + ops::Sub<Self, Output = Self>
    + ops::Rem<Self, Output = Self>
    + ops::Shr<Self, Output = Self>
    + ops::Shl<usize, Output = Self>
    + ops::BitOr<Self, Output = Self>
{
    #[doc(hidden)]
    type Unsigned: Int<BYTES>;

    #[doc(hidden)]
    const ZERO: Self;

    #[doc(hidden)]
    const ONE: Self;

    #[doc(hidden)]
    const MAX: Self;

    #[doc(hidden)]
    fn from_u8(b: u8) -> Self;

    #[doc(hidden)]
    fn from_usize(u: usize) -> Self;

    #[doc(hidden)]
    fn checked_add(self, rhs: Self) -> Option<Self>;

    #[doc(hidden)]
    fn wrapping_add(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn wrapping_sub(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn to_unsigned(self) -> Self::Unsigned;

    #[doc(hidden)]
    fn from_unsigned(unsigned: Self::Unsigned) -> Self;

    #[doc(hidden)]
    fn from_le_bytes(bytes: [u8; BYTES]) -> Self;

    #[doc(hidden)]
    fn to_le_bytes(self) -> [u8; BYTES];

    #[doc(hidden)]
    fn min_representable_bytes(self) -> u32;
}

macro_rules! impl_int {
    ( $( $ty:ty : $unsigned_ty: ty : $bytes:expr ; )* ) => {
        $(
            impl Int<$bytes> for $ty {
                type Unsigned = $unsigned_ty;

                const ZERO: Self = 0;

                const ONE: Self = 1;

                const MAX: Self = Self::MAX;

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

                fn wrapping_sub(self, rhs: Self) -> Self {
                    <$ty>::wrapping_sub(self, rhs)
                }

                fn to_unsigned(self) -> Self::Unsigned {
                    self as $unsigned_ty
                }

                fn from_unsigned(unsigned: $unsigned_ty) -> Self {
                    unsigned as Self
                }

                fn from_le_bytes(bytes: [u8; $bytes]) -> Self {
                    <$ty>::from_le_bytes(bytes)
                }

                fn to_le_bytes(self) -> [u8; $bytes] {
                    <$ty>::to_le_bytes(self)
                }

                fn min_representable_bytes(self) -> u32 {
                    // 0 as a number still needs to be represented by one byte for fuzzing
                    if self == 0 { return 1 };
                    (<$ty>::ilog2(self) + 1).div_ceil(8)
                }
            }
        )*
    }
}

impl_int! {
    u8: u8 : 1;
    u16: u16 : 2;
    u32: u32 : 4;
    u64: u64 : 8;
    u128: u128 : 16;
    usize: usize : 8;
    i8: u8 : 1;
    i16: u16 : 2;
    i32: u32 : 4;
    i64: u64 : 8;
    i128: u128 : 16;
    isize: usize : 8;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_size() {
        let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 6]);
        // Should take one byte off the end
        assert_eq!(u.arbitrary_byte_size().unwrap(), 6);
        assert_eq!(u.len(), 9);
        let mut v = vec![0; 260];
        v.push(1);
        v.push(4);
        let mut u = Unstructured::new(&v);
        // Should read two bytes off the end
        assert_eq!(u.arbitrary_byte_size().unwrap(), 0x104);
        assert_eq!(u.len(), 260);
    }

    #[test]
    fn int_in_range_of_one() {
        let mut u = Unstructured::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 6]);
        let x = u.int_in_range(0..=0).unwrap();
        assert_eq!(x, 0);
        let choice = *u.choose(&[42]).unwrap();
        assert_eq!(choice, 42)
    }

    #[test]
    fn min_representable_bytes_in_bigger_size() {
        assert_eq!(1, (u8::MAX as u16).min_representable_bytes());
    }

    #[test]
    fn int_in_range_uses_minimal_amount_of_bytes() {
        let mut u = Unstructured::new(&[1, 2]);
        assert_eq!(1, u.int_in_range::<u8, 1>(0..=u8::MAX).unwrap());
        assert_eq!(u.len(), 1);

        let mut u = Unstructured::new(&[1, 2]);
        assert_eq!(1, u.int_in_range::<u32, 4>(0..=u8::MAX as u32).unwrap());
        assert_eq!(u.len(), 1);

        let mut u = Unstructured::new(&[1]);
        assert_eq!(1, u.int_in_range::<u32, 4>(0..=u8::MAX as u32 + 1).unwrap());
        assert!(u.is_empty());
    }

    #[test]
    fn int_in_range_in_bounds() {
        for input in u8::MIN..=u8::MAX {
            let input = [input];

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(1..=u8::MAX).unwrap();
            assert_ne!(x, 0);

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(0..=u8::MAX - 1).unwrap();
            assert_ne!(x, u8::MAX);
        }
    }

    #[test]
    fn int_in_range_covers_unsigned_range() {
        // Test that we generate all values within the range given to
        // `int_in_range`.

        let mut full = [false; u8::MAX as usize + 1];
        let mut no_zero = [false; u8::MAX as usize];
        let mut no_max = [false; u8::MAX as usize];
        let mut narrow = [false; 10];

        for input in u8::MIN..=u8::MAX {
            let input = [input];

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(0..=u8::MAX).unwrap();
            full[x as usize] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(1..=u8::MAX).unwrap();
            no_zero[x as usize - 1] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(0..=u8::MAX - 1).unwrap();
            no_max[x as usize] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(100..=109).unwrap();
            narrow[x as usize - 100] = true;
        }

        for (i, covered) in full.iter().enumerate() {
            assert!(covered, "full[{}] should have been generated", i);
        }
        for (i, covered) in no_zero.iter().enumerate() {
            assert!(covered, "no_zero[{}] should have been generated", i);
        }
        for (i, covered) in no_max.iter().enumerate() {
            assert!(covered, "no_max[{}] should have been generated", i);
        }
        for (i, covered) in narrow.iter().enumerate() {
            assert!(covered, "narrow[{}] should have been generated", i);
        }
    }

    #[test]
    fn int_in_range_covers_signed_range() {
        // Test that we generate all values within the range given to
        // `int_in_range`.

        let mut full = [false; u8::MAX as usize + 1];
        let mut no_min = [false; u8::MAX as usize];
        let mut no_max = [false; u8::MAX as usize];
        let mut narrow = [false; 21];

        let abs_i8_min: isize = 128;

        for input in 0..=u8::MAX {
            let input = [input];

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(i8::MIN..=i8::MAX).unwrap();
            full[(x as isize + abs_i8_min) as usize] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(i8::MIN + 1..=i8::MAX).unwrap();
            no_min[(x as isize + abs_i8_min - 1) as usize] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(i8::MIN..=i8::MAX - 1).unwrap();
            no_max[(x as isize + abs_i8_min) as usize] = true;

            let mut u = Unstructured::new(&input);
            let x = u.int_in_range(-10..=10).unwrap();
            narrow[(x as isize + 10) as usize] = true;
        }

        for (i, covered) in full.iter().enumerate() {
            assert!(covered, "full[{}] should have been generated", i);
        }
        for (i, covered) in no_min.iter().enumerate() {
            assert!(covered, "no_min[{}] should have been generated", i);
        }
        for (i, covered) in no_max.iter().enumerate() {
            assert!(covered, "no_max[{}] should have been generated", i);
        }
        for (i, covered) in narrow.iter().enumerate() {
            assert!(covered, "narrow[{}] should have been generated", i);
        }
    }
    
}

// #[cfg(kani)]
// mod kani_suite {
//     use crate::UnstructuredBuilder;
//     use crate::Unstructured;

//     macro_rules! generate_int_check {
//         ($type:ty, $f:ident) => {
//             #[kani::proof]
//             #[kani::unwind(30)]
//             fn $f() {
//                 let first_number: $type = kani::any();
//                 let last_number: $type = kani::any();
//                 kani::assume(last_number >= first_number);
//                 let int: $type = kani::any();
//                 kani::assume(int >= first_number && int <= last_number);
//                 let range = first_number..=last_number;
//                 let bytes = UnstructuredBuilder::bytes_from_constrained_int(range.clone(), int);
//                 let generated_int = Unstructured::int_in_range_impl(range.clone(), bytes.iter().copied()).unwrap().0;
//                 assert_eq!(generated_int, int);
//             }
//         }
//     }

//     generate_int_check!(u8, test_u8);
//     generate_int_check!(u16, test_u16);
// }
