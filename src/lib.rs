#![feature(float_bits_conv)]

use std::borrow::{Cow, ToOwned};
use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::{BinaryHeap, BTreeSet, BTreeMap, HashMap, HashSet, LinkedList, VecDeque};
use std::ffi::{CString, OsString};
use std::iter;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicUsize, AtomicIsize};
use std::time::Duration;

/// Unstructured data from which structured `Arbitrary` data shall be generated.
///
/// This could be a random number generator, a static ring buffer of bytes or some such.
pub trait Unstructured {
    type Error;
    /// Fill a `buffer` with bytes, forming the unstructured data from which `Arbitrary` structured
    /// data shall be generated.
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

pub trait Arbitrary: Sized + 'static {
    /// Generate arbitrary structured data from unstructured data.
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error>;

    /// Generate derived values which are “smaller” than the original one.
    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new(iter::empty())
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
}

impl Arbitrary for u8 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let mut x = [0];
        u.fill_buffer(&mut x)?;
        Ok(x[0])
    }
}

impl Arbitrary for i8 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<u8 as Arbitrary>::arbitrary(u)? as i8)
    }
}

impl Arbitrary for u16 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let mut x = [0, 0];
        u.fill_buffer(&mut x)?;
        Ok(x[0] as u16 | (x[1] as u16) << 8)
    }
}

impl Arbitrary for i16 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<u16 as Arbitrary>::arbitrary(u)? as i16)
    }
}

impl Arbitrary for u32 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let mut x = [0, 0, 0, 0];
        u.fill_buffer(&mut x)?;
        Ok(x[0] as u32 | (x[1] as u32) << 8 | (x[2] as u32) << 16 | (x[3] as u32) << 24)
    }
}

impl Arbitrary for i32 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<u32 as Arbitrary>::arbitrary(u)? as i32)
    }
}

impl Arbitrary for u64 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let mut x = [0, 0, 0, 0, 0, 0, 0, 0];
        u.fill_buffer(&mut x)?;
        Ok(x[0] as u64 | (x[1] as u64) << 8 | (x[2] as u64) << 16 | (x[3] as u64) << 24
                       | (x[4] as u64) << 32 | (x[5] as u64) << 40 | (x[6] as u64) << 48
                       | (x[7] as u64) << 56)
    }
}

impl Arbitrary for i64 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<u64 as Arbitrary>::arbitrary(u)? as i64)
    }
}

impl Arbitrary for usize {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(match ::std::mem::size_of::<usize>() {
            2 => <u16 as Arbitrary>::arbitrary(u)? as usize,
            4 => <u32 as Arbitrary>::arbitrary(u)? as usize,
            _ => <u64 as Arbitrary>::arbitrary(u)? as usize,
        })
    }
}

impl Arbitrary for isize {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(<usize as Arbitrary>::arbitrary(u)? as isize)
    }
}

impl Arbitrary for f32 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(f32::from_bits(<u32 as Arbitrary>::arbitrary(u)?))
    }
}

impl Arbitrary for f64 {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(f64::from_bits(<u64 as Arbitrary>::arbitrary(u)?))
    }
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
            match ::std::char::from_u32(c) {
                Some(c) => return Ok(c),
                None => { c -= 1; }
            }
        }
    }
}

impl Arbitrary for AtomicBool {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(AtomicBool::new)
    }
}

impl Arbitrary for AtomicIsize {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(AtomicIsize::new)
    }
}

impl Arbitrary for AtomicUsize {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(AtomicUsize::new)
    }
}

impl Arbitrary for Duration {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Ok(Duration::new(Arbitrary::arbitrary(u)?,
                         <u32 as Arbitrary>::arbitrary(u)? % 1_000_000_000))
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

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        if let Some(ref a) = *self {
            Box::new(iter::once(None).chain(a.shrink().map(|x| Some(x))))
        } else {
            Box::new(iter::empty())
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

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        match *self {
            Ok(ref a) => Box::new(a.shrink().map(|x| Ok(x))),
            Err(ref a) => Box::new(a.shrink().map(|x| Err(x))),
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
            // TODO: shrink
        }
    };
}
arbitrary_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);

macro_rules! arbitrary_array {
    {$n:expr, $t:ident $($ts:ident)*} => {
        arbitrary_array!{($n - 1), $($ts)*}

        impl<T: Arbitrary> Arbitrary for [T; $n] {
            fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<[T; $n], U::Error> {
                Ok([Arbitrary::arbitrary(u)?,
                    $(<$ts as Arbitrary>::arbitrary(u)?),*])
            }
            // TODO: shrink
        }
    };
    ($n: expr,) => {};
}

arbitrary_array!{ 32, T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T T }

impl<A: Arbitrary> Arbitrary for Vec<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<K: Arbitrary + Ord, V: Arbitrary> Arbitrary for BTreeMap<K, V> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BTreeSet<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A: Arbitrary + Ord> Arbitrary for BinaryHeap<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<K: Arbitrary + Eq + ::std::hash::Hash, V: Arbitrary> Arbitrary for HashMap<K, V> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A: Arbitrary + Eq + ::std::hash::Hash> Arbitrary for HashSet<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A: Arbitrary> Arbitrary for LinkedList<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A: Arbitrary> Arbitrary for VecDeque<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| Arbitrary::arbitrary(u)).collect()
    }
}

impl<A> Arbitrary for Cow<'static, A>
where A: ToOwned + ?Sized, <A as ToOwned>::Owned: Arbitrary
{
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Cow::Owned)
    }
}

impl Arbitrary for String {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        let size = u.container_size()?;
        (0..size).map(|_| <char as Arbitrary>::arbitrary(u)).collect()
    }
}

impl Arbitrary for CString {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        <Vec<u8> as Arbitrary>::arbitrary(u).map(|mut x| {
            x.retain(|&c| c != 0);
            CString::new(x).unwrap()
        })
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
        Arbitrary::arbitrary(u).map(Box::new)
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
        Arbitrary::arbitrary(u).map(Arc::new)
    }
}

impl<A: Arbitrary> Arbitrary for Rc<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Rc::new)
    }
}

impl<A: Arbitrary> Arbitrary for Cell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Cell::new)
    }
}

impl<A: Arbitrary> Arbitrary for RefCell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(RefCell::new)
    }
}

impl<A: Arbitrary> Arbitrary for UnsafeCell<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(UnsafeCell::new)
    }
}

impl<A: Arbitrary> Arbitrary for Mutex<A> {
    fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
        Arbitrary::arbitrary(u).map(Mutex::new)
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


pub struct RingBuffer<'a>{
    buffer: &'a [u8],
    off: usize,
    max_len: usize
}

impl<'a> RingBuffer<'a> {
    pub fn new(buffer: &'a [u8], max_len: usize) -> Result<RingBuffer<'a>, &'static str> {
        if buffer.len() == 0 {
            return Err("buffer must not be empty")
        }
        Ok(RingBuffer {
            buffer: buffer,
            off: 0,
            max_len: max_len
        })
    }
}

impl<'a> Unstructured for RingBuffer<'a> {
    type Error = ();
    fn fill_buffer(&mut self, buffer: &mut [u8]) -> Result<(), Self::Error> {
        let b = [&self.buffer[self.off..], &self.buffer[..self.off]];
        let it = ::std::iter::repeat(&b[..]).flat_map(|x| x).flat_map(|&x| x);
        self.off = (self.off + buffer.len()) % self.buffer.len();
        for (d, f) in buffer.iter_mut().zip(it) {
            *d = *f;
        }
        Ok(())
    }

    fn container_size(&mut self) -> Result<usize, Self::Error> {
        <usize as Arbitrary>::arbitrary(self).map(|x| x % self.max_len )
    }

}

#[test]
fn ring_buffer_fill_buffer() {
    let x = [1, 2, 3, 4];
    let mut rb = RingBuffer::new(&x, 2);
    let mut z = [0; 10];
    rb.fill_buffer(&mut z).unwrap();
    assert_eq!(z, [1, 2, 3, 4, 1, 2, 3, 4, 1, 2]);
    rb.fill_buffer(&mut z).unwrap();
    assert_eq!(z, [3, 4, 1, 2, 3, 4, 1, 2, 3, 4]);
}

#[test]
fn ring_buffer_container_size() {
    let x = [1, 2, 3, 4, 5];
    let mut rb = RingBuffer::new(&x, 11);
    assert_eq!(rb.container_size().unwrap(), 9);
    assert_eq!(rb.container_size().unwrap(), 1);
    assert_eq!(rb.container_size().unwrap(), 2);
    assert_eq!(rb.container_size().unwrap(), 6);
    assert_eq!(rb.container_size().unwrap(), 1);
}
