use arbitrary::Arbitrary;

#[derive(Arbitrary)]
struct Point {
    #[arbitrary(value)]
    x: i32,
    y: i32
}

fn main() { }
