use lazy_static::*;
use pest::{Parser, prec_climber::*};
use pest::iterators::Pair;
use pest_derive::*;

use crate::expr::{Expr, BinOp};

lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
        use Rule::*;
        use Assoc::*;

        PrecClimber::new(vec![
            Operator::new(add, Left) | Operator::new(subtract, Left),
            Operator::new(multiply, Left) | Operator::new(divide, Left),
        ])
    };
}

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
pub(crate) struct RestrictionParser;

//impl RestrictionParser {
//    pub fn parse_to_expr(input: &str) -> Result<Expr, pest::error::Error<Rule>> {
//        let pair: Pair<_> = RestrictionParser::parse(Rule::restriction, input)?.next().unwrap();
//        fn parse_arith_operator(op: Rule) -> BinOp {
//            match op {
//                Rule::add => BinOp::Add,
//                Rule::substract => BinOp::Sub,
//                Rule::multiply => BinOp::Mul,
//                Rule::divide => BinOp::Div,
//                _ => unreachable!()
//            }
//        }
//
//        fn parse_rel_operator(op: Rule) -> BinOp {
//            match op {
//                Rule::eq => BinOp::Eq,
//                Rule::neq => BinOp::Ne,
//                Rule::lt => BinOp::Lt,
//                Rule::le => BinOp::Le,
//                Rule::gt => BinOp::Gt,
//                Rule::ge => BinOp::Ge,
//                _ => unreachable!()
//            }
//        }
//
//        fn parse_log_operator(op: Rule) -> Expr {
//            match op {
//                Rule::and |
//                Rule::or |
//                Rule::imp |
//                Rule::equiv => unimplemented!(),
//                _ => unreachable!()
//            }
//        }
//
//        fn parse_predicate(pair: Pair<Rule>) -> Expr {
//            match pair.as_rule() {
//                Rule::predicate => {
//                    let mut inner = pair.into_inner();
//                    let lhs = parse_predicate(inner.next().unwrap());
//                    if let Some(op) = inner.next() {
//                        let op = parse_arith_operator(op);
//                        let rhs = parse_predicate(inner.next().unwrap());
//                        Expr::BinaryOp(op, box lhs, box rhs)
//                    } else {
//                        lhs
//                    }
//                }
//                Rule::arith_expr => {
//                    let mut inner = pair.into_inner();
//                    let lhs = parse_term(inner.next().unwrap());
//                    if let Some(op) = inner.next() {
//                        let op = parse_arith_operator(op);
//                        let rhs = parse_term(inner.next().unwrap());
//                        Expr::BinaryOp(op, box lhs, box rhs)
//                    } else {
//                        lhs
//                    }
//                }
//                _ => unimplemented!()
//            }
//        }
//        Ok(parse_predicate(pair)?)
//    }
//}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn check_true() {
        let mut tru = RestrictionParser::parse(Rule::restriction, "true").unwrap();
        assert_eq!(tru
                       .next()
                       .unwrap()
                       .into_inner()
                       .next()
                       .unwrap()
                       .as_rule(), Rule::bool_expr);
    }

    #[test]
    fn check_false() {
        let fls = RestrictionParser::parse(Rule::restriction, "false").unwrap();
        assert_eq!(fls.as_str(), "false");
    }

    #[test]
    fn check_relation() {
        let rel = RestrictionParser::parse(Rule::restriction, "x>0").unwrap();
        assert_eq!(rel.as_str(), "x>0");
    }
}
