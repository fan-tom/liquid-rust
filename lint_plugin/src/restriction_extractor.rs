use crate::refinements_registry::FunctionRestrictions;
use rustc::ty::{TyCtxt, Instance};
use rustc::hir::def_id::DefId;
use syntax::print::pprust;
use crate::rustpeg_parser::RestrictionParser;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use crate::restriction_expr::Expr;
use crate::visitor::Visitable;
use rustc::mir::{Body};
use crate::expr::BinOp;
use crate::utils::ANN_RET_NAME;

pub fn extract_restrictions<'tcx>(tcx: TyCtxt<'tcx>, fun_id: DefId) -> (FunctionRestrictions, Result<&Body<'tcx>, failure::Error>) {

    let (mut requires, mut ensures) = (Vec::new(), Vec::new());
    for attr in tcx.get_attrs(fun_id).iter() {
        match &*attr.path.segments[0].ident.as_str() {
            v @ "requires" | v @ "ensures" => {
                let input = pprust::tts_to_string(attr.tokens.clone());
                println!("Parsing attribute {}({:?})", input, attr);
                if v == "requires" {
                    requires.push(RestrictionParser::parse_preconditions(&input)
                                      .map(|v| v.into_iter().map(|(a, e)| (a.to_string(), e)).collect::<Vec<_>>())
                    )
                } else {
                    ensures.push(RestrictionParser::parse_postconditions(&input))
                }
            },
            _ => continue
        }

    }

    println!("Raw requirements: {:?}", requires);

    let (requires, ensures) = match (requires
                                         .into_iter()
                                         .try_fold(HashMap::new(), |mut hm: HashMap<_, _>, r| {
//                                             r.map(|v| hm.extend(v))
                                             match r {
                                                 // TODO: Here we replace existing preconditions, instead we need to merge them
                                                 Ok(v) => hm.extend(v),
                                                 Err(e) => return Err(e)
                                             };
                                             Ok(hm)
                                         }),
                                     ensures
                                         .into_iter()
                                         .try_fold(Vec::new(), |mut v: Vec<_>, r| {
                                             v.push(r?);
                                             Ok(v)
                                         })
                                         .map(|v| v
                                             .into_iter()
                                             .fold(None, |r: Option<_>, expr| Some(if let Some(e) = r {
                                                 Expr::BinaryOp(BinOp::And, box e, box expr)
                                             } else {
                                                 expr
                                             }))
                                         ),
    ) {
        (Ok(r), Ok(e)) => {
            println!("Requirements: {:?}", r);
            (r, e)
        }
        (Ok(pre), Err(post_err)) => {
            println!("Found errors in postcondition syntax, exit");
            return (FunctionRestrictions::new(pre, Default::default()), Err(post_err))
        }
        (Err(pre_err), Ok(post)) => {
            println!("Found errors in precondition syntax, exit");
            return (FunctionRestrictions::new(Default::default(), post), Err(pre_err))
        }
        (Err(pre_err), Err(post_err)) => {
            println!("Found errors in postcondition and precondition syntaxes, exit");
            return (
                FunctionRestrictions::new(Default::default(), Default::default()),
                Err(failure::format_err!("{}\n{}", pre_err, post_err))
            )
        }
    };
    let mir = tcx.instance_mir(Instance::mono(tcx, fun_id).def);
    let function_arguments_names = mir
        .args_iter()
        .filter_map(|i| Some(mir.local_decls[i].name?.as_str().to_string()))
        .collect::<Vec<_>>();

    let requires_err = check_requires_wf(&function_arguments_names, &requires);
    let ensures_err = if let Some(e) = &ensures {
        check_ensures_wf(&function_arguments_names, e)
    } else {
        Ok(())
    };

    match (requires_err, ensures_err) {
        (Ok(_), Ok(_)) => (FunctionRestrictions::new(requires, ensures), Ok(mir)),
        (Ok(_), Err(e)) => {
            println!("Error in postcondition wellformedness");
            (
                FunctionRestrictions::new(requires, Default::default()),
                Err(failure::err_msg(format!("unknown variables in postcondition predicate: {}", e.into_iter().join(", "))))
            )
        },
        (Err(pre_err), Ok(_)) => {
            println!("Error in precondition wellformedness");
            (
                FunctionRestrictions::new(Default::default(), ensures),
                Err(failure::err_msg(
                    pre_err.into_iter()
                        .map(|(a, u)| if u.is_empty() {
                            format!("unknown variable in predicate: {}", a)
                        } else {
                            format!("unknown variables in predicate over {}: {}", a, u.into_iter().join(", "))
                        })
                        .join("\n")
                )
                )
            )
        },
        (Err(pre_err), Err(post_err)) => {
            println!("Errors in preconditions and postconditions wellformedness");
            (
                FunctionRestrictions::new(Default::default(), Default::default()),
                Err(
                    failure::err_msg(
                        format!("errors in preconditions: {}\nerrors in postconditions: {}",
                                pre_err.into_iter()
                                    .map(|(a, u)| if u.is_empty() {
                                        format!("unknown variable in predicate: {}", a)
                                    } else {
                                        format!("unknown variables in predicate over {}: {}", a, u.into_iter().join(", "))
                                    })
                                    .join("\n"),
                                post_err.into_iter().join(", ")
                        )
                    )
                )
            )
        }
    }

//    if let Err(e) =  {
//        println!("Error in requirements");
//        (
//            FunctionRestrictions::new(Default::default(), ensures.get(ANN_RET_NAME).cloned()),
//            Err(failure::err_msg(
//                e.into_iter()
//                    .map(|(a, u)| if u.is_empty() {
//                        format!("unknown variable in predicate: {}", a)
//                    } else {
//                        format!("unknown variables in predicate over {}: {}", a, u.into_iter().join(", "))
//                    })
//                    .join("\n")
//            )
//            )
//        )
//    } else {
//        (FunctionRestrictions::new(requires, ensures.get("result").cloned()), Ok(mir))
//    }
}

/// Here we check that precondition of every function argument refers only to preceding arguments
/// and that every precondition is associated with existing function argument
/// i.e in function
/// ```rust
/// fn foo(a: i32, b: bool, c: String) { /* body */ }
/// ```
/// precondition can be associated only with names `a`, `b` or `c`
/// and precondition over `a` cannot refer to `b` or `c`,
/// precondition over `b` can only refer to `a`,
/// precondition over `c` can refer to both `a` and `b`
pub fn check_requires_wf<'e>(function_arguments_names: &[impl AsRef<str>], requires: impl IntoIterator<Item=(&'e String, &'e Expr)>) -> Result<(), HashMap<&'e str, HashSet<&'e str>>> {
    let mut unknown_vars = HashMap::<_, HashSet<_>>::new();
    requires
        .into_iter()
        .for_each(|(arg, expr)| {
            if !function_arguments_names.iter().any(|a| a.as_ref() == arg.as_str()) {
                unknown_vars.entry(arg.as_str()).or_default();
            }
            println!("Checking requirement {}", expr);
            expr.accept(&mut |e: &'e Expr| {
                println!("Visiting expr {}", e);
                if let Expr::Var(ref s) = e {
                    println!("Checking var {} in requirement", s);
                    if s != arg && !function_arguments_names
                        .iter()
                        .take_while(|a| a.as_ref() != arg)
                        .any(|a| a.as_ref() == s.as_str()) {
                        unknown_vars
                            .entry(arg.as_str())
                            .or_default()
                            .insert(s.as_str());
                    }
                }
            });
        });
    println!("End checking requirements, unknown vars: {:?}", unknown_vars);
    if unknown_vars.is_empty() {
        Ok(())
    } else {
        Err(unknown_vars)
    }
}

/// Here we check that postcondition only refers to function arguments
pub fn check_ensures_wf<'e>(function_arguments_names: &[impl AsRef<str>], ensures: &'e Expr) -> Result<(), HashSet<&'e str>> {
    let mut unknown_vars = HashSet::new();
    ensures.accept(&mut |e: &'e Expr| {
        println!("Visiting expr {}", e);
        if let Expr::Var(ref s) = e {
            println!("Checking var {} in requirement", s);
            if s != ANN_RET_NAME && !function_arguments_names
                .iter()
                .any(|a| a.as_ref() == s.as_str()) {
                unknown_vars.insert(s.as_str());
            }
        }
    });
    println!("End checking requirements, unknown vars: {:?}", unknown_vars);
    if unknown_vars.is_empty() {
        Ok(())
    } else {
        Err(unknown_vars)
    }
}
