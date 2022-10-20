use arbitrary::Arbitrary;

#[derive(Arbitrary)]
struct Point {
    #[arbitrary(unknown_attr = 255)]
    x: i32,
    y: i32
}

fn main() { }
