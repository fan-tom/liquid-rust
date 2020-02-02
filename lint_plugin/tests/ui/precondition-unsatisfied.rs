#![feature(plugin)]
#![plugin(liquid)]
#![feature(custom_attribute)]

#[requires("a: a>0")]
fn accept_only_positive(a: i32) -> bool {
    a > 0
}

fn main() {
    accept_only_positive(-5);
}