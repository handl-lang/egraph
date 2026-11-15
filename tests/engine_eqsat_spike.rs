//! P2 spike (ADR-0174/0175): `engine-eqsat` feasibility prototype.
//!
//! Proves the search loop closes end-to-end over *kernel* `Term`s
//! (`hnl_engine::Term`): lift via `from_kernel`, saturate with rewrite
//! rules authored in the crate's pattern space, extract a best term,
//! lower via `to_kernel`, and check the result is a kernel `Term`
//! again — with provenance recorded.
//!
//! Scratch evidence for `host/project/reports/engine-eqsat-spike.md`.
//! Not shipped behavior; the `engine-eqsat` interpretation crate does
//! not exist yet — this test is the thinnest possible stand-in for it.

use std::rc::Rc;

use handl_egraph::{
    AttrValue, EGraph, KernelTerm, Rewrite, RunOptions, StopReason, Term, TermAttr, attr,
    attr_meta, from_kernel, to_kernel,
};
use serde_json::json;

/// The bridge encoding of a kernel `Op{source: Native}` carries exactly
/// one attr — `source: "native"` — so every pattern below pins that
/// keyset (the matcher's attr gate is exact-keyset).
fn native_attrs() -> Vec<(Rc<str>, TermAttr)> {
    vec![attr("source", "native")]
}

/// A pattern leaf for a kernel `Const` — the self-describing leaf key
/// the bridge mints (`leaf_term` = the term's own JSON encoding).
fn const_leaf(v: serde_json::Value) -> Term {
    from_kernel(&KernelTerm::constant(v))
}

/// `add(?d, ?x, 0) -> ?x` over the bridge encoding: child 0 is the
/// kernel `dim` slot (bound, not constrained — see the report's open
/// questions), the constant `0` is a leaf pattern.
fn add_zero() -> Rewrite {
    Rewrite::new(
        "add_zero",
        Term::op(
            "add",
            vec![
                Term::var("d"),
                Term::var("x"),
                const_leaf(json!(0)),
            ],
            native_attrs(),
        ),
        Term::var("x"),
    )
    .with_law("add_zero")
}

/// `mul(?d, ?x, 1) -> ?x`.
fn mul_one() -> Rewrite {
    Rewrite::new(
        "mul_one",
        Term::op(
            "mul",
            vec![
                Term::var("d"),
                Term::var("x"),
                const_leaf(json!(1)),
            ],
            native_attrs(),
        ),
        Term::var("x"),
    )
    .with_law("mul_one")
}

/// Tiny evaluator over the spike's fragment — `Const` plus native
/// `add`/`mul` on constant args — used to check the rewrite preserved
/// meaning, not just shape.
fn eval_const_fragment(t: &KernelTerm) -> Option<f64> {
    match t {
        KernelTerm::Const { value } => value.as_f64(),
        KernelTerm::Op { name, args, .. } if args.len() == 2 => {
            let a = eval_const_fragment(&args[0])?;
            let b = eval_const_fragment(&args[1])?;
            match name.as_str() {
                "add" => Some(a + b),
                "mul" => Some(a * b),
                _ => None,
            }
        }
        _ => None,
    }
}

#[test]
fn saturation_loop_closes_over_kernel_terms() {
    // input: add(mul(2, 1), 0)  — all `op_native`, default dim.
    let two = KernelTerm::constant(json!(2));
    let one = KernelTerm::constant(json!(1));
    let zero = KernelTerm::constant(json!(0));
    let input = KernelTerm::op_native(
        "add",
        vec![
            KernelTerm::op_native("mul", vec![two.clone(), one.clone()]),
            zero.clone(),
        ],
    );

    let mut g = EGraph::new();
    let root = g.add_term(&from_kernel(&input), "input").unwrap();
    let stats = g
        .run(
            &[add_zero(), mul_one()],
            root,
            &mut RunOptions::default(),
        )
        .unwrap();
    assert_eq!(stats.stop, StopReason::FixedPoint);

    // Extract the cheapest member and lower it back to a kernel Term.
    let best_egraph = g
        .extract_best(root, &mut |t: &Term| t.size() as f64, None, None)
        .expect("extraction");
    let best_kernel = to_kernel(&best_egraph);

    // The loop closed: the result is a kernel `Term` — here the
    // constant `2`, both identities applied.
    assert_eq!(best_kernel, KernelTerm::constant(json!(2)));

    // Meaning preserved on the fragment: input and output evaluate equal.
    assert_eq!(
        eval_const_fragment(&input),
        eval_const_fragment(&best_kernel)
    );

    // Provenance: the merges name their firing rules.
    let fired: Vec<&str> = g
        .merge_log()
        .iter()
        .filter_map(|e| e.rule.as_deref())
        .collect();
    assert!(fired.contains(&"add_zero"), "merge log: {fired:?}");
    assert!(fired.contains(&"mul_one"), "merge log: {fired:?}");
    assert!(!g.applications().is_empty());
}

#[test]
fn attrs_payload_round_trips_through_a_rewrite() {
    // `tensor.reshape(x, attrs={"shape":[2,2]})` — the P0.5
    // `Term::Op.attrs` payload rides the bridge under `"__attrs__"`.
    let x = KernelTerm::constant(json!(7));
    let shape = json!({"shape": [2, 2]});
    let input = KernelTerm::op_native_attrs("tensor.reshape", vec![x], shape.clone());

    // Law: reshape(?d, ?x, attrs=?a) -> flatten(?d, ?x, attrs=?a)
    // — the `__attrs__` object is bound as an attr metavariable and
    // re-emitted verbatim on the RHS.
    let reshape_flatten = Rewrite::new(
        "reshape_flatten",
        Term::op(
            "tensor.reshape",
            vec![Term::var("d"), Term::var("x")],
            vec![attr("source", "native"), attr_meta("__attrs__", "a")],
        ),
        Term::op(
            "tensor.flatten",
            vec![Term::var("d"), Term::var("x")],
            vec![attr("source", "native"), attr_meta("__attrs__", "a")],
        ),
    )
    .with_law("reshape_flatten");

    let mut g = EGraph::new();
    let root = g.add_term(&from_kernel(&input), "input").unwrap();
    g.run(&[reshape_flatten], root, &mut RunOptions::default())
        .unwrap();

    // The rewritten member exists in the root class and lowers back to
    // a kernel `Op` carrying the *same* attrs payload.
    let flatten_eterm = Term::op(
        "tensor.flatten",
        vec![
            const_leaf(json!(1)), // default dim == Const(1)
            const_leaf(json!(7)),
        ],
        vec![
            attr("source", "native"),
            attr("__attrs__", AttrValue::from(&shape)),
        ],
    );
    let class = g
        .class_of_term(&flatten_eterm)
        .expect("flatten member was instantiated");
    assert_eq!(g.find_ref(class), g.find_ref(root));

    let lowered = to_kernel(&flatten_eterm);
    match &lowered {
        KernelTerm::Op { name, attrs, .. } => {
            assert_eq!(name, "tensor.flatten");
            assert_eq!(attrs, &Some(shape));
        }
        other => panic!("expected Op, got {other:?}"),
    }
}
