//! A simple example of deriving the `Arbitrary` trait for an `enum`.
//!
//! Note that this requires enabling the "derive" cargo feature.

use arbitrary::{Arbitrary, FiniteBuffer};

#[derive(Arbitrary, Debug)]
enum MyEnum {
    UnitVariant,
    TupleVariant(bool, u32),
    StructVariant { x: i8, y: (u8, i32) },
}

fn main() {
    let raw = b"This is some raw, unstructured data!";
    let mut buf = FiniteBuffer::new(raw, raw.len())
        .expect("`raw` is non-empty so creating a `FiniteBuffer` cannot fail");
    let instance = MyEnum::arbitrary(&mut buf)
        .expect("`raw` has enough data to create all variants of `MyEnum`");
    println!("Here is an arbitrary enum: {:?}", instance);
}
