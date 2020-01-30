**Liquid Rust**

This project is attempt to implement Liquid Types type checker
for Rust code.

**Abstract**
-

The basic idea of refined types is to attach predicates to types, i.e
`type NonZero = { v: int | v != 0}`. Each value of that type satisfies that predicate,
so if we want function to accept only non-zero values(safe division, for example), we declare it's type as
`NonZero -> <whatever type you want>`. We may also use refined type in return position of function signature,
so we can use function invocation as source of refinements of variables.
The whole satisfiability of restriction and refinements checking machinery is implemented in SMT solvers, such as Z3.  

**Concrete**
-

To implement Liquid Types for rust, we need to allow programmer to supply restrictions of
function signatures and variables in source code and then check that that restrictions are always satisfied.

The key question here are:

 1) how to provide restrictions?

 2) how to analyze Rust code?

 3) how to interop with SMT solver?

The current answers are:

 1) We may use custom attributes, i.e
     ```rust
     //main.rs
     #![feature(custom_attribute)]
     
     #[require(a > 30)]
     #[ensure(result == a)]
     fn foo(a: i32) -> i32 {
         a
     }
     ```
     
     This way we may annotate functions, methods, variables, fields and may be other interesting syntax constructions.
     Another possibility is to create annotated type alias and use it anywhere type name is allowed.
     
     ```rust
     //main.rs
     #![feature(custom_attribute)]
     
     #[require(NonZero != 0)]
     type NonZero = i32;

     fn accept_refined(a: NonZero) -> i32 {
         a
     }
     fn return_refined(a: i32) -> NonZero {
         a
     }
     fn declare_refined() {
        let a: NonZero = 5;
     }
     
     fn ascript_refined() -> NonZero {
        let mut x;
        // init and mutate x
        x: NonZero + 5
     }
     ```
     
     After we get annotation we need to parse restriction, typecheck it and translate to SMT expression.
     The attribute is given as path (**require** or **ensure** above) + TokenStream of the rest.
     Currently I want to convert TokenStream to string and parse it with Pest(or rust-peg) parser.
     Question here is to discover what are all possible syntax constructs we may and want to support.
     
 2) Current approach of analyzing Rust code is to use Rust compiler lint infrastructure and 
    declare rustc plugin, that will use LatePass lint phase, where typed representation of AST is accessible (called HIR).
 
    The problem here is that this representation is very "high-level", because there are high-level constructs here,
    such as pattern matching, method calls, and so on. Ideally we want representation, where all high-level
    constructs are lowered to assignments (SSA?) and function calls. ~~There is such representation in compiler,
    called MIR, but it seems that there is no such phase in linting where we work with MIR.
    Generally speaking, we need to find all assignments to refined variables, that may come from
    actual assignment, initialization, function call (actual parameters assigned to formal parameters) and
    function return (result expression is assigned to implicit result variable).~~
    We can easily get MIR of function or constexpr if we know substitution of all type variables within that fun/const.
    It means however that we cannot analyze generic functions in abstract, only when they are called from monomorphized function.
    Possible approach here may be to maintain map from (`<function id>`, `<type substitution>`) -> <precondition + postcondition>
    in LintPass and query for it any time we want to refine function call from inside another function.
    
    How to check that restrictions required by function argument refined type is satisfied?
    We need to analyze what values actual argument may be equal to(we call them refinements), and pass them as preconditions
    to SMT solver.
    How to collect that refinements?
    Refinements may come from assignment of refined variable, if-check, match, reachability analysis
    ```rust
        let x = ...;
        if x == 5 {
            panic/return/break/continue;
        }
        // here x != 5
    ```
    and WHAT ELSE?
    
 3) Interaction may be done by adaptor libraries, such as rsmt2 and z3. What one to use?
    We want to translate parsing tree to AST accepted by library. z3 provides functions to
    construct different AST nodes (such as `x.eq(y)`), but that AST types are opaque so we
    cannot construct them by hands. rsmt2 has no AST type, but requires to provide type
    that may be converted to SMT solver predicate string and another type to parse SMT output
    (model) from string.
    There exists rustproof-libsmt that seems appropriate for our needs

**Links**

* Liquid Types original paper: https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf
* Liquid Haskell project, the most mature implementation of Liquid Types: https://ucsd-progsys.github.io/liquidhaskell-blog/
* Another attempt to implement refinement types for Rust code: https://github.com/Rust-Proof/rustproof/
(seems isn't maintained and doesn't compile as of May 2019)

19.12.2019

Currently I decided to analyze MIR in LatePass, deferring polymorphic functions analysis to call sites.
Notes about original paper:
* We don't need to perform HM type inference as we already have type information from rust compiler
* We don't need (sure? what about closures, including as arguments?) to handle function types.
* We don't need to infer types of functions as our analysis is local, we don't infer liquid types globally,
the same way rust does it. So we only must check explicitly provided type restrictions.
* We cannot analyze polymorphic functions alone, as we cannot get MIR without type substitutions, so we defer analysis
of them until they are called and we can get their MIR. It may be very inefficient, as a lot of rust code uses
generics, but we can cache analysis results using pair of (function id, type arguments) as key.
So we don't need the notion of 'type schema' (all our schemas are monotypes)
* Original paper describes algorithms using functional nature of analyzed language, i.e program consists of declarations
and expressions. There is no notion of expression in MIR, however it seems that we may replace it with notion of
SSA variable, that has type as once-assigned value. Environment of each that assignment consists of all the variables,
introduced earlier in that block or any of its predecessors, whereas in functional language each expr is in another expression and
there is notion of 'sibling' expressions.

28.01.2020

Currently plugin can infer types in simple cases, from assignment and arithmetic operations, can handle conditions in 
branches, check preconditions of called functions and use their postconditions to refine variables. The main problem
now is to infer most common type **after** branches, as we need to somehow handle the fact that refienements in
different branches are valid under different conditions. For example, consider next piece of code:
 
```rust
#[ensures(return > 0)]
fn returns_positive(x: i32) -> i32 {
    if x < 0 {          // 1
        1               // 2
    } else if x == 0 {  // 3
        x+1             // 4
    } else {            // 5
        x               // 6
    }                   // 7
                        // 8
}
```
As you can see, postcondition is always satisfied, but plugin infers types after `if` (line 8) as
`(x < 0 \/ x = 0 \/ not (x < 0 \/ x = 0)) /\ (return = 1 \/ return = x + 1 \/ return = x)` and so postcondition check fails, because
we lost connection between condition over `x` and corresponding `return` value.
Instead, we need to infer most common type for all variables among all branches. Here it may be `return > 0`. But that 
type is imprecise, as we lose information that `return = x` if `x > 0` or `return = 1` otherwise. Can we handle this?

30.01.2020

I considered to try to not infer most common type among all condition branches, but instead track refinement predicates
with corresponding conditions, under which their was assigned and then convert them to SMT `ite` cascades.
Let's consider previous example again
```rust
#[ensures(return > 0)]
fn returns_positive(x: i32) -> i32 {
    let ret = if x < 0 {// 1
        1               // 2
    } else if x == 0 {  // 3
        x+1             // 4
    } else {            // 5
        x               // 6
    };                  // 7
    ret                 // 8
}
```
(I changed it a little to have the variable to reason about)
Such code is translated into the next CFG:
```rust
                                   +----------------+
                                   |  bb0           |
                                   +-----------+----+
                                   |  tmp1 = x < 0  |
                          false    +-----------+----+ true
                        +----------+  switch tmp1   +------+
                        |          +----------------+      |
                        |                                  |
             +----------v---------+                  +-----v-----+
             |  bb2               |                  |  bb1      |
             +--------------------+                  +-----------+
             |  tmp1 = x == 0     |                  |  ret = 1  |
             +--------------------+                  +-----------+
      +------+  switch tmp2       +------+           |   goto    |
      |      +--------------------+      |           +-----+-----+
      |                                  |                 |
+-----v-----+                      +-----v----------+      |
|  bb4      |                      |  bb3           |      |
+-----------+                      +----------------+      |
|  ret = x  |                      |  ret = x + 1   |      |
+-----------+                      +----------------+      |
|   goto    +----------+-----------+   goto         |      |
+-----------+          |           +----------------+      |
                +------v-------+                           |
                |  bb5         |                           |
                +--------------<---------------------------+
                |  return ret  |
                +--------------+

```
Each rectangle denotes basic block, has header, statements and terminator.
In bb1 we refine `ret` with predicate `{v: int | v = 1}`, in bb3 - with `{v: int | v = x+1}`,
in bb 4 - with `{v: int | v = x}`. However, in bb5 we don't know what value of `ret` will have, as we lost path predicates.
To fix this, we can modify our refinement predicates to carry path predicates.
In bb1 we will now refine `ret` with predicate `{v: int | v = 1 if x < 0}`, 
in bb3 - with `{v: int | v = x+1 if x = 0}`
and in bb 4 - with `{v: int | v = x if (not (x < 0)) /\ (not (x = 0))}`.
When we convert them to SMT solver, we build `ite` cascade:
```
(assert (ret = (ite (< x 0) 1 (ite (= x 0) (+ x 1) x))))
```
Note, here we assume that condition predicate of last refinement is equal to negation of all other predicates.
To check this exhaustiveness, we can supply additional assert, that ensures our assumption:
```
(assert (not (= (not (or (< x 0) (= x 0))) ((not (< x 0)) /\ (not (= x 0))))))
```
If this assert is satisfied, then there are conditions, that are not covered by any of conditional predicates, but it
seem that Rust compiler must reject such code, as it means not each branch returns value.
