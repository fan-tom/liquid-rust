//use peg_syntax_ext::*;
use crate::restriction_expr::*;

//#[cfg(debug_assertions)]
//peg_file!restriction("parser/grammar.rustpeg");

//#[cfg(not(debug_assertions))]
//mod restriction {
//    include!(concat!(env!("OUT_DIR"), "/grammar.rs"));
//}

peg::parser!{grammar restriction() for str {
    //float -> f64 = n:$(int ("." [0-9]*)? (^"e" int)?) {n.parse().unwrap()}

    rule int() -> &'input str = $(("+" / "-")? ['0'..='9']+)
    pub rule integer() -> u64 = n:int() {n.parse().unwrap()}

    rule paren<T>(x: rule<T>) -> T = "(" _ v:x() _ ")" {v}
    rule quoted<T>(x: rule<T>) -> T = "\"" _ v:x() _ "\"" {v}

    rule keyword() -> Expr = "true" {Expr::r#true()} / "false" {Expr::r#false()}

    pub rule ident() -> &'input str = !keyword() s:$(['_' | 'a' ..='z' | 'A'..='Z']['_' | 'a' ..='z' | 'A'..='Z' | '0'..='9']*) {s}

    rule arith_operator() = add() / sub() / mul() / div()
    rule add() =  _ "+" _
    rule sub() =  _ "-" _
    rule mul() =  _ "*" _
    rule div() =  _ "/" _

    pub rule arith_expr() -> Expr = precedence!{
        x:(@) add() y:@ { Expr::BinaryOp(BinOp::Add, box x, box y)}
        x:(@) sub() y:@ { Expr::BinaryOp(BinOp::Sub, box x, box y)}
        --
        x:(@) mul() y:@ { Expr::BinaryOp(BinOp::Mul, box x, box y)}
        x:(@) div() y:@ { Expr::BinaryOp(BinOp::Div, box x, box y)}
        //#R x "^" y { x.pow(y as u32) }
        --
        i:ident() {Expr::Var(i.to_string())}
        --
        n:integer() {Expr::Const(Const::Int{bits: u128::from(n), size: 64})}
        --
        e:paren(<arith_expr()>) {e}
    }

    pub rule rel_operator() -> BinOp = eq() / le() / lt() / ge() / gt()
    // TODO: handle neq separately, as Not(Eq)
//    / neq()
    rule eq() -> BinOp = _ "==" _ {BinOp::Eq}
    rule lt() -> BinOp = _ "<" _ {BinOp::Lt}
    rule le() -> BinOp = _ "<=" _ {BinOp::Le}
    rule gt() -> BinOp = _ ">" _ {BinOp::Gt}
    rule ge() -> BinOp = _ ">=" _ {BinOp::Ge}

    rule neq() = _ "!=" _

    pub rule relation() -> Expr =
        lhs:arith_expr() op:rel_operator() rhs:arith_expr() {Expr::BinaryOp(op, box lhs, box rhs)}
        / lhs:arith_expr() neq() rhs:arith_expr() {Expr::UnaryOp(UnaryOp::Not, box Expr::BinaryOp(BinOp::Eq, box lhs, box rhs))}
        / a:arith_expr() {a}

    rule log_operator() -> BinOp = and() / or() / imp() / equiv()
    rule and() -> BinOp = _ "&&" _ {BinOp::And}
    rule or() -> BinOp = _ "||" _ {BinOp::Or}
    rule imp() -> BinOp = _ "=>" _ {BinOp::Imp}
    rule equiv() -> BinOp = _ "<=>" _ {BinOp::Equiv}

    pub rule predicate_expr() -> Expr = precedence!{
        lhs:@ equiv() rhs:(@) {Expr::BinaryOp(BinOp::Equiv, box lhs, box rhs)}
        lhs:@ imp() rhs:(@) {Expr::BinaryOp(BinOp::Imp, box lhs, box rhs)}
        --
        lhs:(@) or() rhs:@ {Expr::BinaryOp(BinOp::Or, box lhs, box rhs)}
        lhs:(@) and() rhs:@ {Expr::BinaryOp(BinOp::And, box lhs, box rhs)}
        --
        lhs:(@) eq() rhs:@ {Expr::BinaryOp(BinOp::Eq, box lhs, box rhs)}
        lhs:(@) neq() rhs:@ {Expr::UnaryOp(UnaryOp::Not, box Expr::BinaryOp(BinOp::Eq, box lhs, box rhs))}
        --
        "!" e:predicate_expr() {Expr::not(e)}
        --
        r:relation() {r}
        --
        k:keyword() {k}
        --
        e:paren(<predicate_expr()>) {e}
    }

    pub rule predicate() -> (&'input str, Expr) = v:ident() _ ":" _ e:predicate_expr() {(v, e)}

    rule _restrictions() -> Vec<(&'input str, Expr)> = v:(predicate() ** (_ "," _)) {v}

    rule _quot_restrictions() -> Vec<(&'input str, Expr)> = quoted(<_restrictions()>)

    rule _eq_restrictions() -> Vec<(&'input str, Expr)> = _ "=" _ v:_quot_restrictions() {v}

    pub rule restrictions() -> Vec<(&'input str, Expr)> = v:_eq_restrictions() {v} / v:paren(<_quot_restrictions()>) {v}

    rule _() = quiet!{[' ' | '\n' | '\t']*}
}}

pub struct RestrictionParser;

impl RestrictionParser {
    pub fn parse_preconditions(input: &str) -> Result<Vec<(&str, Expr)>, failure::Error> {
        Ok(restriction::restrictions(input)?)
    }

    pub fn parse_postconditions(input: &str) -> Result<Expr, failure::Error> {
        Ok(restriction::predicate_expr(input)?)
    }
}

#[test]
fn check_single() -> Result<(), failure::Error> {
    let pred = r#"("b: abc_d >30")"#;
    let actual_expr = RestrictionParser::parse_preconditions(pred)?;
    let expected_expr = ("b", Expr::BinaryOp(BinOp::Gt, box Expr::Var("abc_d".into()), box Expr::Const(Const::Int{ bits: 30 as u128, size: 64})));
    assert_eq!(actual_expr, vec![expected_expr]);
    Ok(())
}

#[test]
fn check_complex() -> Result<(), failure::Error> {
    let pred = r#"( "c:(a>30&&d==true)<=>(c!=!b)")"#;
    let actual_expr = RestrictionParser::parse_preconditions(pred)?;
    let expected_expr = ("c",
                         Expr::BinaryOp(
                             BinOp::Equiv,
                             box Expr::BinaryOp(
                                 BinOp::And,
                                 box Expr::BinaryOp(
                                     BinOp::Gt,
                                     box Expr::Var("a".to_string()),
                                     box Expr::Const(Const::Int { size: 64, bits: 30 })),
                                 box Expr::BinaryOp(
                                     BinOp::Eq,
                                     box Expr::Var("d".to_string()),
                                     box Expr::Const(Const::Bool(true)))),
                             box Expr::UnaryOp(
                                 UnaryOp::Not,
                                 box Expr::BinaryOp(
                                     BinOp::Eq,
                                     box Expr::Var("c".to_string()),
                                     box Expr::UnaryOp(
                                         UnaryOp::Not,
                                         box Expr::Var("b".to_string())
                                     )
                                 )
                             )
                         )
    );
    assert_eq!(actual_expr, vec![expected_expr]);
    Ok(())
}
