use arbitrary::Arbitrary;

#[derive(Arbitrary)]
struct Point {
    #[arbitrary(unknown_attr)]
    x: i32,
    y: i32
}

fn main() { }
