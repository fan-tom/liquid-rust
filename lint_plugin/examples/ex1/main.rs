#![cfg_attr(feature = "liquid", feature(plugin))]
#![cfg_attr(feature = "liquid", plugin(liquid))]

#![feature(custom_attribute)]
#![feature(type_ascription)]

//mod separate_module;


#[require(NonZero != 0)]
//#[NonZero == 5]
type NonZero = i32;

#[require(a > 30)]
#[ensure(result == a)]
fn foo(a: NonZero) -> i32 {
    if a < 5 || a > 10 {
        // a < 5
        // !(a<5) && a > 10
        // full: !(a>=5 && a<=10)
        let mut res: NonZero = a + 1;
        res += 2;
        res += 3;
        res += bar(4);
        res
    } else {
        // !(a<5) && !(a>10)
        let res = a;
        res * 6
    }
}

fn bar<T>(t: T) -> T {
    t
}

//#[require(tick_id > 20)]
//#[ensure(result == 10)]
fn main() {
//    let x: NonZero = 5;
//    let _ = foo(x);
//    let mut y = 6: i32;
//    let _ = foo(y);
//    y=x;
//    let mut v = Vec::new();
//    v.push(y);
//    foo(6);
//    println!("Hello, world! {}", x);
}
