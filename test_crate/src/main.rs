#![feature(plugin, custom_attribute)]
#![plugin(rustproof)]
#![allow(unused_attributes)]

#[require(NonZero != 0)]
//#[NonZero == 5]
type NonZero = i32;

#[condition(pre="a:i32 != 0", post="result: i32 == 5")]
fn foo(a: NonZero) -> i32 {
    5
}

//#[require(tick_id > 20)]
//#[ensure(result == 10)]
fn main() {
    let x: NonZero = 5;
    let _ = foo(x);
    let mut y = 6: i32;
    let _ = foo(y);
    y=x;
    let mut v = Vec::new();
    v.push(y);
    foo(6);
    println!("Hello, world! {}", x);
}
