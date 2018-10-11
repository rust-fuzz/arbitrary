//! A simple test deriving the Arbitrary crate

#[macro_use]
extern crate derive_arbitrary;
extern crate arbitrary;

use arbitrary::{Arbitrary, FiniteBuffer};

#[derive(Arbitrary, Debug)]
enum Foo {
    A,
    B(bool, u32),
    C { x: i8, y: (u8, i32) },
}

fn main() {
    let mut buf = FiniteBuffer::new(b"This is a test", 14).unwrap();
    println!("{:?}", <Foo as Arbitrary>::arbitrary(&mut buf).unwrap());
}
