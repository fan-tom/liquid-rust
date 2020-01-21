//#![cfg_attr(feature = "liquid", feature(plugin))]
//#![cfg_attr(feature = "liquid", plugin(liquid))]
#![feature(plugin)]
#![plugin(liquid)]

#![feature(custom_attribute)]
#![feature(type_ascription)]

//mod separate_module;


#[require(NonZero != 0)]
//#[NonZero == 5]
type NonZero = i32;

//#[require(a: a != 42)]
//#[requires(b: a < 50)]
//#[requires(c: (a > 30 && d == true) <=> (c != b))]
//#[requires="c: (a > 30 && b == true) <=> (c != !b)"]
#[requires("c: (a > 30 && b == true) <=> (c != !b)")]
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
//#[ensures(return == a)]
pub fn foo(a: NonZero, b: bool, c: bool) -> i32 {
    a
/*
    if a < 5 || a > 10 {
        // a < 5
        // !(a<5) && a > 10
        // full: !(a>=5 && a<=10)
        let mut res: NonZero = a + 1;
//        res += 2;
//        res += 3;
//        res += bar(4);
        res
    } else {
        // !(a<5) && !(a>10)
        let res = a;
        res * 6
    }
*/
}

#[requires("a: a != 0")]
fn accepts_nonzero(a: i32) -> i32 {
    a
}

#[requires("a: a > 0")]
fn accepts_positive(a: i32) -> i32 {
    accepts_nonzero(a)
}






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
    let second = true;
    let third = false;

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
    accepts_positive(1);
//    println!("Hello, world! {}", x);
}
