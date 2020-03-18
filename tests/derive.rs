#![cfg(feature = "derive")]

use arbitrary::*;

fn arbitrary_from<T: Arbitrary>(input: &[u8]) -> T {
    let mut buf = Unstructured::new(input);
    T::arbitrary(&mut buf).expect("can create arbitrary instance OK")
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Arbitrary)]
pub struct Rgb {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

#[test]
fn struct_with_named_fields() {
    let rgb: Rgb = arbitrary_from(&[4, 5, 6]);
    assert_eq!(rgb.r, 4);
    assert_eq!(rgb.g, 5);
    assert_eq!(rgb.b, 6);

    assert_eq!(
        rgb.shrink().collect::<Vec<_>>(),
        vec![
            Rgb { r: 0, g: 0, b: 0 },
            Rgb { r: 2, g: 2, b: 3 },
            Rgb { r: 1, g: 1, b: 1 }
        ]
    );

    assert_eq!((3, Some(3)), <Rgb as Arbitrary>::size_hint(0));
}

#[derive(Copy, Clone, Debug, Arbitrary)]
struct MyTupleStruct(u8, bool);

#[test]
fn tuple_struct() {
    let s: MyTupleStruct = arbitrary_from(&[43, 42]);
    assert_eq!(s.0, 43);
    assert_eq!(s.1, false);

    let s: MyTupleStruct = arbitrary_from(&[42, 43]);
    assert_eq!(s.0, 42);
    assert_eq!(s.1, true);

    for ((a, b), s) in 42.shrink().zip(true.shrink()).zip(s.shrink()) {
        assert_eq!(a, s.0);
        assert_eq!(b, s.1);
    }

    assert_eq!((2, Some(2)), <MyTupleStruct as Arbitrary>::size_hint(0));
}

#[derive(Clone, Debug, Arbitrary)]
struct EndingInVec(u8, bool, u32, Vec<u16>);
#[derive(Clone, Debug, Arbitrary)]
struct EndingInString(u8, bool, u32, String);

#[test]
fn test_take_rest() {
    let bytes = [1, 1, 1, 2, 3, 4, 5, 6, 7, 8];
    let s1 = EndingInVec::arbitrary_take_rest(Unstructured::new(&bytes)).unwrap();
    let s2 = EndingInString::arbitrary_take_rest(Unstructured::new(&bytes)).unwrap();
    assert_eq!(s1.0, 1);
    assert_eq!(s2.0, 1);
    assert_eq!(s1.1, true);
    assert_eq!(s2.1, true);
    assert_eq!(s1.2, 0x4030201);
    assert_eq!(s2.2, 0x4030201);
    assert_eq!(s1.3, vec![0x605, 0x807]);
    assert_eq!(s2.3, "\x05\x06\x07\x08");
}

#[derive(Copy, Clone, Debug, Arbitrary)]
enum MyEnum {
    Unit,
    Tuple(u8, u16),
    Struct { a: u32, b: (bool, u64) },
}

#[test]
fn derive_enum() {
    let mut raw = vec![
        // The choice of which enum variant takes 4 bytes.
        1, 2, 3, 4,
        // And then we need up to 13 bytes for creating `MyEnum::Struct`, the
        // largest variant.
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
    ];

    let mut saw_unit = false;
    let mut saw_tuple = false;
    let mut saw_struct = false;

    for i in 0..=255 {
        // Choose different variants each iteration.
        for el in &mut raw[..4] {
            *el = i;
        }

        let e: MyEnum = arbitrary_from(&raw);

        match e {
            MyEnum::Unit => {
                saw_unit = true;
                assert_eq!(e.shrink().count(), 0);
            }
            MyEnum::Tuple(a, b) => {
                saw_tuple = true;
                assert_eq!(a, arbitrary_from(&raw[4..5]));
                assert_eq!(b, arbitrary_from(&raw[5..]));

                for ((a, b), e) in a.shrink().zip(b.shrink()).zip(e.shrink()) {
                    match e {
                        MyEnum::Tuple(c, d) => {
                            assert_eq!(a, c);
                            assert_eq!(b, d);
                        }
                        _ => panic!("should never shrink to a different variant"),
                    }
                }
            }
            MyEnum::Struct { a, b } => {
                saw_struct = true;
                assert_eq!(a, arbitrary_from(&raw[4..8]));
                assert_eq!(b, arbitrary_from(&raw[8..]));
                for ((a, b), e) in a.shrink().zip(b.shrink()).zip(e.shrink()) {
                    match e {
                        MyEnum::Struct { a: c, b: d } => {
                            assert_eq!(a, c);
                            assert_eq!(b, d);
                        }
                        _ => panic!("should never shrink to a different variant"),
                    }
                }
            }
        }
    }

    assert!(saw_unit);
    assert!(saw_tuple);
    assert!(saw_struct);

    assert_eq!((4, Some(17)), <MyEnum as Arbitrary>::size_hint(0));
}

#[derive(Arbitrary, Debug)]
enum RecursiveTree {
    Leaf,
    Node {
        left: Box<RecursiveTree>,
        right: Box<RecursiveTree>,
    },
}

#[test]
fn recursive() {
    let raw = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let _rec: RecursiveTree = arbitrary_from(&raw);

    let (lower, upper) = <RecursiveTree as Arbitrary>::size_hint(0);
    assert_eq!(lower, 4, "need a u32 for the discriminant at minimum");
    assert!(
        upper.is_none(),
        "potentially infinitely recursive, so no upper bound"
    );
}

#[derive(Arbitrary, Debug)]
struct Generic<T> {
    inner: T,
}

#[test]
fn generics() {
    let raw = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let gen: Generic<bool> = arbitrary_from(&raw);
    assert!(gen.inner);

    let (lower, upper) = <Generic<u32> as Arbitrary>::size_hint(0);
    assert_eq!(lower, 4);
    assert_eq!(upper, Some(4));
}
