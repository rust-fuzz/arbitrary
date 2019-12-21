#![cfg(feature = "derive")]

extern crate arbitrary;
use arbitrary::*;

#[derive(Copy, Clone, Debug, Arbitrary)]
pub struct Rgb {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

#[test]
fn rgb() {
    let raw = vec![1, 2, 3];
    let mut buf = FiniteBuffer::new(&raw, raw.len()).expect("can create FiniteBuffer OK");
    let rgb = Rgb::arbitrary(&mut buf).expect("can generate arbitrary Rgb OK");
    assert_eq!(rgb.r, 1);
    assert_eq!(rgb.g, 2);
    assert_eq!(rgb.b, 3);
}
