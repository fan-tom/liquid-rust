use pest::{Parser, prec_climber::*};
use pest_derive::*;
use lazy_static::*;

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
