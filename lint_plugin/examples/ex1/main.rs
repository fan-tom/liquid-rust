//#![cfg_attr(feature = "liquid", feature(plugin))]
//#![cfg_attr(feature = "liquid", plugin(liquid))]
#![feature(plugin)]
#![plugin(liquid)]

#![feature(custom_attribute)]
#![feature(type_ascription)]

//mod separate_module;


#[require(NonZero != 0)]
//#[NonZero == 5]
type NonZero = u32;

// fn bar(mut a: u32) -> u32 {
// //    a += 1;
//     let b = a + 5;
//     let c = accepts_nonzero(b);
//     c
// }
//#[require(a: a != 42)]
//#[requires(b: a < 50)]
//#[ensures(return == b)]
//#[requires(c: (a > 30 && d == true) <=> (c != b))]
//#[requires="c: (a > 30 && b == true) <=> (c != !b)"]
//#[requires("c: (a > 30 && b == true) <=> (c != !b)")]
//   (a>30 && b == true) =>  (c<5)  && !(a>30 && b == true) => !(c<5)
// (!(a>30 && b == true) ||  (c<5)) && ((a>30 && b == true) || !(c<5))
// !((a>30 && b == true) && !(c<5)  || !(a>30 && b == true) &&  (c<5))
//  !(a>30 && b == true) && !(c<5)  ||  (a>30 && b == true) &&  (c<5)

//        A => B  && B => A
//     (!A ||  B) &&  (!B ||  A)
// ! (!(!A ||  B) || !(!B ||  A))
// ! (  (A && !B) ||   (B && !A))
//
// !A && !B || A && B
//#[liquid_haskell_type({v: i32 | v != 42} -> {v: bool | v > a} -> {v: bool | v < 5 <=> a>30 && b == true} -> {v: i32 | v == a})]
//#[requires(a != 42, b > a, c < 5 <=> (a > 30 && b == true))]
//#[requires("c: c==b")]
//pub fn foo(mut a: NonZero, b: bool, mut c: i32) -> bool {
//    let mut b = 1;
//    if a < 5 {
//        b *= 2;
//        a= accepts_nonzero(b);
//    }
////    while a < 5 {
////        b *= 2;
////        if b > 10 {
////            a += 2;
////            c += a;
////        } else {
////            a += 3;
////            c -= 2 * a;
////        }
////        a*=accepts_nonzero(b);
////    }
//    b > 20
///*
//    if a < 5 || a > 10 {
//        // a < 5
//        // !(a<5) && a > 10
//        // full: !(a>=5 && a<=10)
//        let mut res: NonZero = a + 1;
////        res += 2;
////        res += 3;
////        res += bar(4);
//        res
//    } else {
//        // !(a<5) && !(a>10)
//        let res = a;
//        res * 6
//    }
//*/
//}

// #[requires("a: a != 0")]
#[ensures(return == a)]
fn accepts_nonzero(a: u32) -> u32 {
    a
}

//fn accepts_any(x: i32) -> i32 {
//    if x == 0 {
//        accepts_nonzero(x+1)
//    } else if x >= 1 {
//        accepts_nonzero(x)
//    } else if x < -1 {
//        x
//    } else {
//        accepts_only_zero(x+1)
//    }
//}

#[ensures(return > 0)]
fn returns_positive(x: i32) -> i32 {
   // accepts_nonzero(accepts_only_zero(0))
   if x < 0 {
       1
   } else if x == 0 {
       accepts_only_zero(x)
   } else {
       2 //accepts_nonzero(x)
   }
}

#[requires("a: a == 0")]
#[ensures(return == a+1)]
fn accepts_only_zero(a: i32) -> i32 {
//    switch(Some(a))
   a+1
}

//fn switch(v: Option<i32>) -> i32 {
//    match v {
//        None => 0,
//        Some(t) => t,
//    }
//}





//fn bar<T>(t: T) -> T { t }

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
//    let second = true;
//    let third = false;
    /// ;SMT asserts:
    /// ; declare all variables and arguments
    /// (declare-const a Int)
    /// (declare-const b Bool)
    /// (declare-const c Bool)
    /// (declare-const second Bool)
    /// (declare-const third Bool)
    /// ; given
    /// (define-fun given () Bool
    ///  (and
    ///   (= second true)
    ///   (= third false)
    ///   ; a = 6
    ///   (= a 6)
    ///   ; b = second
    ///   (= b second)
    ///   ; c = third
    ///   (= c third)
    ///  )
    /// )
    /// ; need
    /// (define-fun need () Bool
    ///  (and
    ///   ; a: NonZero
    ///   (not (= a 0))
    ///   ; c: (a > 30 && b == true) <=> (c != !b)
    ///   (= c (equiv (and (> a 30) (= b true)) (not (= c (not b)))))
    ///  )
    /// )
    /// ; should be true
    /// (define-fun pred () Bool (=> given need))
    /// ; if we cannot proof negation of predicate,
    /// ; then we proof that predicate is always true
    /// (assert (not pred))
    /// (check-sat)
//    let x = foo(36, second, third);
//    accepts_positive(1);
//     bar(1);
    let ret = returns_positive(i32::max_value());
    // println!("{}", ret);
//    println!("Hello, world! {}", x);
}
