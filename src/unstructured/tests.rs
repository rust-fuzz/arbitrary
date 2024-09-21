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
fn int_in_range_uses_minimal_amount_of_bytes() {
    let mut u = Unstructured::new(&[0x23, 0x42]);
    assert_eq!(0x23, u.int_in_range::<u8, _>(..).unwrap());
    assert_eq!(u.len(), 1);

    let mut u = Unstructured::new(&[0x42, 0x23]);
    assert_eq!(0x42, u.int_in_range::<u32, _>(..u8::MAX as u32).unwrap());
    assert_eq!(u.len(), 1);

    let mut u = Unstructured::new(&[0x37, 0x13]);
    assert_eq!(0x1337, u.int_in_range::<u32, _>(..).unwrap());
    assert!(u.is_empty());

    let mut u = Unstructured::new(&[42]);
    assert_eq!(
        42,
        u.int_in_range::<u32, _>(0..=u8::MAX as u32 + 1).unwrap()
    );
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
