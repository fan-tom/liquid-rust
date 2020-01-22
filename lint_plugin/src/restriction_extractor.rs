use crate::refinements_registry::FunctionRestrictions;
use rustc::ty::{TyCtxt, Instance};
use rustc::hir::def_id::DefId;
use syntax::print::pprust;
use crate::rustpeg_parser::RestrictionParser;
use itertools::{Either, Itertools};
use std::convert::identity;
use std::collections::{HashMap, HashSet};
use crate::restriction_expr::Expr;
use syntax::ast::Attribute;
use crate::visitor::Visitable;

pub fn extract_restrictions<'tcx>(tcx: TyCtxt<'tcx>, fun_id: DefId) -> Result<FunctionRestrictions, failure::Error> {
//    let (requires, ensures): (Vec<_>, Vec<_>) = tcx.get_attrs(fun_id)
//        .iter()
//        .filter_map(|attr| {
//            let parsed = || {
//                let input = pprust::tts_to_string(attr.tokens.clone());
//                println!("Parsing attribute {}({:?})", input, attr);
//                RestrictionParser::parse(&input)
//                    .map(|v| v.into_iter().map(|(a, e)| (a.to_string(), e)).collect::<Vec<_>>())
////                    .map_err(|e| cx.span_lint(LIQUID_RUST_LINT, attr.span, &e.to_string()))
//            };
//            match &*attr.path.segments[0].ident.as_str() {
//                "requires" => Some(Either::Left(parsed())),
//                "ensures" => Some(Either::Right(parsed())),
//                _ => None
//            }
//        })
//        .partition_map(identity);

    let parsed = |attr: &Attribute| {
        let input = pprust::tts_to_string(attr.tokens.clone());
        println!("Parsing attribute {}({:?})", input, attr);
        RestrictionParser::parse(&input)
            .map(|v| v.into_iter().map(|(a, e)| (a.to_string(), e)).collect::<Vec<_>>())
//                    .map_err(|e| cx.span_lint(LIQUID_RUST_LINT, attr.span, &e.to_string()))
    };
    let (mut requires, mut ensures) = (Vec::new(), Vec::new());
    for attr in tcx.get_attrs(fun_id).iter() {
        match &*attr.path.segments[0].ident.as_str() {
            "requires" => requires.push(parsed(attr)),
            "ensures" => ensures.push(parsed(attr)),
            _ => continue
        }

    }

    println!("Raw requirements: {:?}", requires);

    let (requires, ensures) = match (requires
                                         .into_iter()
                                         .try_fold(HashMap::new(), |mut hm: HashMap<_, _>, r| {
//                                             r.map(|v| hm.extend(v))
                                             match r {
                                                 Ok(v) => hm.extend(v),
                                                 Err(e) => return Err(e)
                                             };
                                             Ok(hm)
                                         }),
                                     ensures
                                         .into_iter()
                                         .try_fold(HashMap::new(), |mut hm: HashMap<_, _>, r| {
                                             hm.extend(r?);
                                             Ok(hm)
                                         }),
    ) {
        (Ok::<_, _>(r), Ok::<_, _>(e)) => {
            println!("Requirements: {:?}", r);
            (r, e)
        }
        (pre_err, post_err) => {
            println!("Found errors in specs, exit");
            return Err(failure::err_msg(pre_err.err().into_iter().chain(post_err.err()).map(|e| e.to_string()).join("\n")))
        }
    };
    let mir = tcx.instance_mir(Instance::mono(tcx, fun_id).def);
    let function_arguments_names = mir
        .args_iter()
        .filter_map(|i| Some(mir.local_decls[i].name?.as_str().to_string()))
        .collect::<Vec<_>>();
    if let Err(e) = check_requires_wf(&function_arguments_names, &requires) {
        println!("Error in requirements");
        Err(failure::err_msg(
                     e.into_iter()
                         .map(|(a, u)| if u.is_empty() {
                             format!("unknown variable in predicate: {}", a)
                         } else {
                             format!("unknown variables in predicate over {}: {}", a, u.into_iter().join(", "))
                         })
                         .join("\n")
                         )
        )
    } else {
        Ok(FunctionRestrictions::new(requires, ensures.get("result").cloned()))
    }
}

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
