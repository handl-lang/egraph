//! The kernel bridge: `hnl_engine::Term` / `serde_json::Value` ↔
//! the crate's [`Term`].
//!
//! Encoding contract — every `Term` variant maps to an `Op` node whose
//! `op` is the variant tag (except `Term::Op`, whose enode op is the
//! domain operator `name`), with `Term`-typed fields as child positions
//! in declaration order and scalar/`Value` fields as literal attrs.
//! `Term::Op` additionally encodes `dim` as **child position 0** so
//! rewrites can reach it; `source`/`lit` ride attrs:
//!
//! | `Term` variant | enode `op` | children | attrs |
//! |---|---|---|---|
//! | `Arr{dim, value}` | `arr` | `[dim]` | `value` |
//! | `Const{value}` | — *leaf* | `[]` | self-describing key |
//! | `Op{dim,name,args,source,lit}` | `name` | `[dim, ..args]` | `source`, `foreign`?, `lit`? |
//! | `Seq{axis,fst,snd}` | `seq` | `[axis,fst,snd]` | |
//! | `First{inner}` | `first` | `[inner]` | |
//! | `Choice{l,r}` | `choice` | `[l,r]` | |
//! | `Loop{body}` | `loop` | `[body]` | |
//! | `App{callee,args}` | `app` | `[callee, ..args]` | |
//! | `Iter{fuel,predicate,step,initial}` | `iter` | 4 children | |
//! | `Child{role}` | `child` | `[]` | `role` |
//! | `Handle{body,target,impl_}` | `handle` | `[body,impl_]` | `target` |
//! | `Rewrite{source,target,witness}` | `rewrite` | `[source,target]` | `witness`, `witness_name`? |
//! | `Src{cell}` / `Tgt{cell}` | `src`/`tgt` | `[cell]` | |
//! | `RecordProj{record,field}` | `record_proj` | `[record]` | `field` |
//! | `RecordWith{record,field,value}` | `record_with` | `[record,value]` | `field` |
//! | `Tag{tag,value}` | `tag` | `[value]` | `tag` |
//! | `Cobind{grade,body}` | `cobind` | `[grade,body]` | |
//! | `Opaque{data}` | — *leaf* | `[]` | self-describing key |
//!
//! **Self-describing leaf keys** replace the spec's global
//! `_LeafRegistry` (a named wart — process-global mutable state whose
//! decode depended on registration order). A leaf term serializes to
//! its own JSON `Term` encoding as the key, so `to_term` decodes it
//! standalone; an unrecognized key decodes to `Term::Opaque`, keeping
//! the round-trip total.

use std::rc::Rc;

use handl_language::term::{ArrSource, RewriteWitness, Term as KTerm};
use serde_json::Value;

use crate::term::{Op, Term, TermAttr};
use crate::value::AttrValue;

/// Lift a kernel `Term` into the e-graph term domain.
pub fn from_kernel(t: &KTerm) -> Term {
    use KTerm::*;
    match t {
        Arr { dim, value } => Term::op(
            "arr",
            Rc::from(vec![from_kernel(dim)]),
            [(Rc::from("value"), alit(json(value)))],
        ),
        Const { .. } => leaf_term(t),
        Op {
            dim,
            name,
            args,
            source,
            lit,
        } => {
            let mut children = Vec::with_capacity(args.len() + 1);
            children.push(from_kernel(dim));
            children.extend(args.iter().map(from_kernel));
            let mut attrs: Vec<(Rc<str>, TermAttr)> =
                vec![(Rc::from("source"), alit(source_tag(source).into()))];
            if let ArrSource::Foreign(n) = source {
                attrs.push((Rc::from("foreign"), alit(n.as_str().into())));
            }
            if let Some(l) = lit {
                attrs.push((Rc::from("lit"), alit(json(l))));
            }
            Term::op(name.as_str(), Rc::from(children), attrs)
        }
        Seq { axis, fst, snd } => Term::opl(
            "seq",
            vec![from_kernel(axis), from_kernel(fst), from_kernel(snd)],
        ),
        First { inner } => Term::opl("first", vec![from_kernel(inner)]),
        Choice { l, r } => Term::opl("choice", vec![from_kernel(l), from_kernel(r)]),
        Loop { body } => Term::opl("loop", vec![from_kernel(body)]),
        App { callee, args } => {
            let mut children = Vec::with_capacity(args.len() + 1);
            children.push(from_kernel(callee));
            children.extend(args.iter().map(from_kernel));
            Term::opl("app", children)
        }
        Iter {
            fuel,
            predicate,
            step,
            initial,
        } => Term::opl(
            "iter",
            vec![
                from_kernel(fuel),
                from_kernel(predicate),
                from_kernel(step),
                from_kernel(initial),
            ],
        ),
        Child { role } => Term::op(
            "child",
            Rc::from(Vec::new()),
            [(Rc::from("role"), alit(role.as_str().into()))],
        ),
        Handle {
            body,
            target,
            impl_,
        } => Term::op(
            "handle",
            Rc::from(vec![from_kernel(body), from_kernel(impl_)]),
            [(Rc::from("target"), alit(target.as_str().into()))],
        ),
        Rewrite {
            source,
            target,
            witness,
        } => {
            let mut attrs: Vec<(Rc<str>, TermAttr)> =
                vec![(Rc::from("witness"), alit(witness_tag(witness).into()))];
            if let RewriteWitness::Named(n) = witness {
                attrs.push((Rc::from("witness_name"), alit(n.as_str().into())));
            }
            Term::op(
                "rewrite",
                Rc::from(vec![from_kernel(source), from_kernel(target)]),
                attrs,
            )
        }
        Src { cell } => Term::opl("src", vec![from_kernel(cell)]),
        Tgt { cell } => Term::opl("tgt", vec![from_kernel(cell)]),
        RecordProj { record, field } => Term::op(
            "record_proj",
            Rc::from(vec![from_kernel(record)]),
            [(Rc::from("field"), alit(field.as_str().into()))],
        ),
        RecordWith {
            record,
            field,
            value,
        } => Term::op(
            "record_with",
            Rc::from(vec![from_kernel(record), from_kernel(value)]),
            [(Rc::from("field"), alit(field.as_str().into()))],
        ),
        Tag { tag, value } => Term::op(
            "tag",
            Rc::from(vec![from_kernel(value)]),
            [(Rc::from("tag"), alit(tag.as_str().into()))],
        ),
        Cobind { grade, body } => Term::opl("cobind", vec![from_kernel(grade), from_kernel(body)]),
        Opaque { .. } => leaf_term(t),
    }
}

/// Lower a [`Term`] back to a kernel `Term`.
///
/// Total by construction: an unknown `op` lowers to a native
/// `Term::Op` of that name (its `dim` defaults to `1`); a leaf key that
/// is not a serialized `Term` lowers to `Term::Opaque` carrying the key
/// (`{"__tag__": "egraph.leaf", "key": k}`) — honest data, never a
/// silent drop. A `Var`/unbound `Meta` in pattern position lowers to
/// the same opaque marker (a metavariable is not a kernel term).
pub fn to_kernel(t: &Term) -> KTerm {
    match t {
        Term::Var(name) => opaque_leaf(&format!("var:{name}")),
        Term::Leaf(key) => decode_leaf(key),
        Term::Op(Op { op, args, attrs }) => {
            let get = |k: &str| -> Option<&AttrValue> {
                attrs
                    .iter()
                    .find(|(n, _)| n.as_ref() == k)
                    .and_then(|(_, v)| {
                        if let TermAttr::Lit(v) = v {
                            Some(v)
                        } else {
                            None
                        }
                    })
            };
            match &**op {
                "arr" if args.len() == 1 => KTerm::Arr {
                    dim: Box::new(to_kernel(&args[0])),
                    value: get("value").map(AttrValue::to_json).unwrap_or(Value::Null),
                },
                "seq" if args.len() == 3 => KTerm::Seq {
                    axis: boxed(&args[0]),
                    fst: boxed(&args[1]),
                    snd: boxed(&args[2]),
                },
                "first" if args.len() == 1 => KTerm::First {
                    inner: boxed(&args[0]),
                },
                "choice" if args.len() == 2 => KTerm::Choice {
                    l: boxed(&args[0]),
                    r: boxed(&args[1]),
                },
                "loop" if args.len() == 1 => KTerm::Loop {
                    body: boxed(&args[0]),
                },
                "app" if !args.is_empty() => KTerm::App {
                    callee: boxed(&args[0]),
                    args: args[1..].iter().map(to_kernel).collect(),
                },
                "iter" if args.len() == 4 => KTerm::Iter {
                    fuel: boxed(&args[0]),
                    predicate: boxed(&args[1]),
                    step: boxed(&args[2]),
                    initial: boxed(&args[3]),
                },
                "child" if args.is_empty() => KTerm::Child {
                    role: str_attr(get("role")),
                },
                "handle" if args.len() == 2 => KTerm::Handle {
                    body: boxed(&args[0]),
                    target: str_attr(get("target")),
                    impl_: boxed(&args[1]),
                },
                "rewrite" if args.len() == 2 => KTerm::Rewrite {
                    source: boxed(&args[0]),
                    target: boxed(&args[1]),
                    witness: match str_attr(get("witness")).as_str() {
                        "named" => RewriteWitness::Named(str_attr(get("witness_name"))),
                        "compute" => RewriteWitness::Compute,
                        "handler_hint" => RewriteWitness::HandlerHint,
                        _ => RewriteWitness::Cast,
                    },
                },
                "src" if args.len() == 1 => KTerm::Src {
                    cell: boxed(&args[0]),
                },
                "tgt" if args.len() == 1 => KTerm::Tgt {
                    cell: boxed(&args[0]),
                },
                "record_proj" if args.len() == 1 => KTerm::RecordProj {
                    record: boxed(&args[0]),
                    field: str_attr(get("field")),
                },
                "record_with" if args.len() == 2 => KTerm::RecordWith {
                    record: boxed(&args[0]),
                    field: str_attr(get("field")),
                    value: boxed(&args[1]),
                },
                "tag" if args.len() == 1 => KTerm::Tag {
                    tag: str_attr(get("tag")),
                    value: boxed(&args[0]),
                },
                "cobind" if args.len() == 2 => KTerm::Cobind {
                    grade: boxed(&args[0]),
                    body: boxed(&args[1]),
                },
                // Domain ops and any unrecognised enode shape lower to
                // native `Term::Op`: child 0 is the dim slot when the
                // node carries a `source` attr (the `Term::Op` encoding),
                // otherwise every child is an argument.
                _ => {
                    let sourced = get("source").is_some();
                    let (dim, rest) = if sourced && !args.is_empty() {
                        (boxed(&args[0]), &args[1..])
                    } else {
                        (KTerm::default_dim(), &args[..])
                    };
                    KTerm::Op {
                        dim,
                        name: op.to_string(),
                        args: rest.iter().map(to_kernel).collect(),
                        source: decode_source(get("source"), get("foreign")),
                        lit: get("lit").map(AttrValue::to_json),
                    }
                }
            }
        }
    }
}

fn boxed(t: &Term) -> Box<KTerm> {
    Box::new(to_kernel(t))
}

fn alit(v: AttrValue) -> TermAttr {
    TermAttr::Lit(v)
}

fn json(v: &Value) -> AttrValue {
    AttrValue::from(v)
}

fn str_attr(v: Option<&AttrValue>) -> String {
    match v {
        Some(AttrValue::Str(s)) => s.to_string(),
        Some(other) => other.to_json().to_string(),
        None => String::new(),
    }
}

/// A leaf carrying its own serialized `Term` encoding as key.
fn leaf_term(t: &KTerm) -> Term {
    let key = serde_json::to_string(t).unwrap_or_else(|_| format!("{t:?}"));
    Term::leaf(key)
}

/// Decode a leaf key: a serialized `Term` round-trips; anything else
/// is an opaque domain leaf.
fn decode_leaf(key: &str) -> KTerm {
    match serde_json::from_str::<KTerm>(key) {
        Ok(t) => t,
        Err(_) => opaque_leaf(key),
    }
}

fn opaque_leaf(key: &str) -> KTerm {
    KTerm::Opaque {
        data: serde_json::json!({"__tag__": "egraph.leaf", "key": key}),
    }
}

fn source_tag(s: &ArrSource) -> &'static str {
    match s {
        ArrSource::Native => "native",
        ArrSource::Foreign(_) => "foreign",
        ArrSource::Judgment => "judgment",
        ArrSource::DynamicForeign => "dynamic",
    }
}

fn witness_tag(w: &RewriteWitness) -> &'static str {
    match w {
        RewriteWitness::Named(_) => "named",
        RewriteWitness::Compute => "compute",
        RewriteWitness::HandlerHint => "handler_hint",
        RewriteWitness::Cast => "cast",
    }
}

fn decode_source(source: Option<&AttrValue>, foreign: Option<&AttrValue>) -> ArrSource {
    match source {
        Some(AttrValue::Str(s)) => match &**s {
            "judgment" => ArrSource::Judgment,
            "dynamic" => ArrSource::DynamicForeign,
            "foreign" => match foreign {
                Some(AttrValue::Str(n)) => ArrSource::Foreign(n.to_string()),
                _ => ArrSource::Native,
            },
            _ => ArrSource::Native,
        },
        _ => ArrSource::Native,
    }
}
