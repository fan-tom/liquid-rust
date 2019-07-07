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
    Possible approach here may be to maintain map from (<function id>, <type substitution>) -> <precondition + postcondition>
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