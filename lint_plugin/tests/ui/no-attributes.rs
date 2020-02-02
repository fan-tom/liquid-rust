#![feature(plugin)]
#![plugin(liquid)]

fn is_positive(a: i32) -> bool {
    a > 0
}

fn main() {
    is_positive(5);
}