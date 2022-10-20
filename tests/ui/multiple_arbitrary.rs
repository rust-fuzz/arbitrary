use arbitrary::Arbitrary;

#[derive(Arbitrary)]
struct Point {
    #[arbitrary(value = 2)]
    #[arbitrary(value = 3)]
    x: i32,
    y: i32
}

fn main() { }
