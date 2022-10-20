use arbitrary::Arbitrary;

#[derive(Arbitrary)]
struct Point {
    #[arbitrary(with)]
    x: i32,
    y: i32
}

fn main() { }
