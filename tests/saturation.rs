//! Saturation fixture: determinism, extraction correctness, budgets,
//! and provenance — mirroring the Python spec's behaviours on a small
//! domain-free term set.

use std::collections::BTreeMap;

use handl_egraph::{
    AttrValue, EGraph, KernelTerm, MergeInfo, Offer, Rewrite, RunOptions, Stop, StopReason, Term,
    attr, attr_meta, dag_cost, from_kernel, to_kernel,
};

fn leaf(s: &str) -> Term {
    Term::leaf(s)
}

fn op(name: &str, args: Vec<Term>) -> Term {
    Term::opl(name, args)
}

fn size(t: &Term) -> f64 {
    t.size() as f64
}

/// The fixture rule set: identity laws, an involution, and one
/// symmetry generator (comm) — small closure, exact fixed point.
fn rules() -> Vec<Rewrite> {
    vec![
        // add(?x, 0) -> ?x
        Rewrite::new(
            "add_zero",
            op("add", vec![Term::var("x"), leaf("0")]),
            Term::var("x"),
        ),
        // mul(?x, 1) -> ?x
        Rewrite::new(
            "mul_one",
            op("mul", vec![Term::var("x"), leaf("1")]),
            Term::var("x"),
        ),
        // neg(neg(?x)) -> ?x
        Rewrite::new(
            "involution",
            op("neg", vec![op("neg", vec![Term::var("x")])]),
            Term::var("x"),
        ),
        // comm: add(?a, ?b) -> add(?b, ?a)
        Rewrite::new(
            "comm_add",
            op("add", vec![Term::var("a"), Term::var("b")]),
            op("add", vec![Term::var("b"), Term::var("a")]),
        ),
    ]
}

fn build() -> (EGraph, usize) {
    let mut g = EGraph::new();
    // input: add(mul(a, 1), 0)
    let t = op(
        "add",
        vec![op("mul", vec![leaf("a"), leaf("1")]), leaf("0")],
    );
    let root = g.add_term(&t, "input").unwrap();
    (g, root)
}

#[test]
fn saturation_folds_identity_to_leaf() {
    let (mut g, root) = build();
    let stats = g.run(&rules(), root, &mut RunOptions::default()).unwrap();
    assert_eq!(stats.stop, StopReason::FixedPoint);
    let best = g.extract_best(root, &mut size, None, None);
    assert_eq!(best, Some(leaf("a")));
}

#[test]
fn saturation_is_deterministic_across_runs() {
    // Two from-scratch runs produce bit-identical results — the
    // canonical member order makes every decision-reaching scan
    // process-independent (the spec's _member_key contract).
    let run_once = || {
        let (mut g, root) = build();
        let s = g.run(&rules(), root, &mut RunOptions::default()).unwrap();
        let t = g.extract_best(root, &mut size, None, None);
        (s, t, g.n_proof_edges())
    };
    let (s1, t1, p1) = run_once();
    let (s2, t2, p2) = run_once();
    assert_eq!(t1, t2);
    assert_eq!(p1, p2);
    assert_eq!(s1.iterations, s2.iterations);
    assert_eq!(s1.n_enodes, s2.n_enodes);
    assert_eq!(s1.n_classes, s2.n_classes);
}

#[test]
fn saturation_produces_commuted_members() {
    let (mut g, root) = build();
    g.run(&rules(), root, &mut RunOptions::default()).unwrap();
    // comm_add must have produced the swapped spelling somewhere in
    // the root class cone: an add(b, a) member exists in the graph.
    let commuted = op("add", vec![leaf("0"), leaf("a")]);
    let found = g.class_of_term(&commuted);
    assert!(found.is_some(), "comm_add never instantiated add(0, a)");
}

#[test]
fn rule_budgets_suspend_explosive_rules() {
    // comm on a wide summation is the canonical explosive rule — cap
    // its enode contribution; unbudgeted rules still reach the point.
    let mut g = EGraph::new();
    let t = op(
        "add",
        vec![
            leaf("a"),
            op(
                "add",
                vec![leaf("b"), op("add", vec![leaf("c"), leaf("d")])],
            ),
        ],
    );
    let root = g.add_term(&t, "input").unwrap();
    let mut opts = RunOptions {
        rule_budgets: BTreeMap::from([("comm_add".to_string(), 2usize)]),
        ..RunOptions::default()
    };
    let stats = g.run(&rules(), root, &mut opts).unwrap();
    assert_eq!(stats.stop, StopReason::FixedPoint);
    assert_eq!(stats.budget_suspended, vec!["comm_add".to_string()]);
    assert!(stats.rule_budgets["comm_add"] >= 2);
}

#[test]
fn provenance_records_applications_and_edges() {
    let (mut g, root) = build();
    g.run(&rules(), root, &mut RunOptions::default()).unwrap();
    // Merge log: every union carries its firing rule.
    let log = g.merge_log();
    assert!(!log.is_empty());
    assert!(log.iter().any(|e| e.rule.as_deref() == Some("add_zero")));
    assert!(log.iter().any(|e| e.rule.as_deref() == Some("mul_one")));
    // Applications: a recorded firing names its rule + RHS root enode,
    // and `enode_app` points the produced enode back at it — the
    // cascade-forgiveness data.
    let apps = g.applications();
    assert!(!apps.is_empty());
    let app = apps
        .iter()
        .find(|a| a.rhs_root_enode.is_some())
        .expect("at least one rooted application");
    let en = app.rhs_root_enode.clone().unwrap();
    let idx = g.enode_app(&en).expect("enode_app for produced enode");
    assert_eq!(&apps[idx].rule, &app.rule);
    // rule_fires counted the merges.
    assert!(g.rule_fires.get("add_zero").copied().unwrap_or(0) >= 1);
}

#[test]
fn quotient_graph_records_no_provenance() {
    let mut g = EGraph::quotient();
    let t = op("add", vec![leaf("a"), leaf("0")]);
    let root = g.add_term(&t, "input").unwrap();
    g.run(&rules(), root, &mut RunOptions::default()).unwrap();
    assert_eq!(g.truncation_level, 1);
    assert_eq!(g.n_proof_edges(), 0);
    assert!(g.applications().is_empty());
}

#[test]
fn offer_mints_a_replayable_witness() {
    let mut g = EGraph::new();
    let a = g.add_term(&leaf("a"), "input").unwrap();
    // A non-local pass offers `g(a)` — a member no LHS could produce —
    // under a pointwise witness.
    let offered = op("g", vec![leaf("a")]);
    let merged = g
        .offer(
            a,
            &Offer {
                rhs_term: Some(&offered),
                provenance: "pair_pass",
                law: "paired",
                witness: true,
                ..Offer::default()
            },
        )
        .unwrap();
    assert!(merged);
    assert!(g.merge_log().iter().any(|e| {
        e.rule
            .as_deref()
            .is_some_and(|r| r.starts_with("pair_pass#"))
    }));
    // The synthetic application makes the member expandable.
    assert!(
        g.applications()
            .iter()
            .any(|a| a.rule.starts_with("pair_pass#"))
    );
}

#[test]
fn direct_union_records_unwitnessed_edge() {
    let mut g = EGraph::new();
    let a = g.add_term(&leaf("a"), "input").unwrap();
    let b = g.add_term(&leaf("b"), "input").unwrap();
    assert!(g.union_with(
        a,
        b,
        &MergeInfo {
            note: "manual".to_string(),
            ..MergeInfo::default()
        }
    ));
    let edge = g.merge_log().last().unwrap();
    assert!(edge.rule.is_none());
    assert_eq!(edge.note, "manual");
}

#[test]
fn check_and_derive_hooks_fire() {
    let mut g = EGraph::new();
    // sq(x, dim=D) -> pow2(x) only when D == 2, deriving attr "k".
    let t = Term::op("sq", vec![leaf("x")], [attr("dim", AttrValue::Int(2))]);
    let e = g.add_term(&t, "input").unwrap();
    let rule = Rewrite::new(
        "sq_to_pow2",
        Term::op("sq", vec![Term::var("x")], [attr_meta("dim", "d")]),
        Term::op("pow2", vec![Term::var("x")], [attr_meta("k", "d")]),
    )
    .with_check(|env| {
        env.attrs.get("d") == Some(&AttrValue::Int(2)) && env.terms.contains_key("x")
    });
    assert!(g.apply_rule(&rule, e, None, None));
    g.rebuild(None);
    assert_eq!(g.find(e), {
        let want = Term::op("pow2", vec![leaf("x")], [attr("k", AttrValue::Int(2))]);
        g.class_of_term(&want).unwrap()
    });
}

#[test]
fn check_veto_skips_the_firing() {
    let mut g = EGraph::new();
    let t = Term::op("sq", vec![leaf("x")], [attr("dim", AttrValue::Int(3))]);
    let e = g.add_term(&t, "input").unwrap();
    let rule = Rewrite::new(
        "sq_to_pow2",
        Term::op("sq", vec![Term::var("x")], [attr_meta("dim", "d")]),
        Term::var("x"),
    )
    .with_check(|env| env.attrs.get("d") == Some(&AttrValue::Int(2)));
    assert!(!g.apply_rule(&rule, e, None, None));
}

#[test]
fn improving_stop_terminates_on_stall() {
    let (mut g, root) = build();
    let mut cost = |t: &Term| t.size() as f64;
    let mut opts = RunOptions {
        stop: Stop::Improving,
        patience: 2,
        cost_fn: Some(&mut cost),
        ..RunOptions::default()
    };
    let stats = g.run(&rules(), root, &mut opts).unwrap();
    // Improving either stalls out or hits the fixed point first —
    // either way it must terminate and report.
    assert!(matches!(
        stats.stop,
        StopReason::Improving | StopReason::FixedPoint
    ));
    assert!(stats.improved.is_some());
}

#[test]
fn extract_overrides_force_a_member() {
    let mut g = EGraph::new();
    let z = g.add_term(&leaf("z"), "input").unwrap();
    let big = op("f", vec![op("f", vec![leaf("a")])]);
    let b = g.add_term(&big, "input").unwrap();
    // z ~ f(f(a)): the class holds a leaf and an op member; the union
    // does NOT cycle (the big member's cone stays below the class).
    g.union(z, b);
    g.rebuild(None);
    let root = g.find(z);
    // Greedy picks the leaf; the override forces the f(f(a)) member.
    let (_, enode) = g.locate(&big, None);
    let over = rustc_hash::FxHashMap::from_iter([(root, enode.expect("f member"))]);
    let forced = g.extract_best(root, &mut size, Some(&over), None);
    assert_eq!(forced, Some(big));
    // And unconstrained extraction returns the (cheaper) leaf.
    assert_eq!(g.extract_best(root, &mut size, None, None), Some(leaf("z")));
}

#[test]
fn dag_cost_bills_shared_subterms_once() {
    // share(x) = add(x, x): the shared child prices once.
    let x = leaf("x");
    let t = op("add", vec![x.clone(), x]);
    let mut unit = |_t: &Term| 1.0;
    // distinct subterms: add-node + leaf x → 2
    assert_eq!(dag_cost(&t, &mut unit), 2.0);
}

#[test]
fn kernel_term_round_trip() {
    // Const leaf: self-describing key, decodes back to Const.
    let k = KernelTerm::constant(serde_json::json!(3));
    let t = from_kernel(&k);
    assert_eq!(to_kernel(&t), k);

    // A domain op round-trips through the whole graph.
    let kadd = KernelTerm::op_native(
        "add",
        vec![
            KernelTerm::constant(serde_json::json!(1)),
            KernelTerm::constant(serde_json::json!(2)),
        ],
    );
    let mut g = EGraph::new();
    let et = from_kernel(&kadd);
    let e = g.add_term(&et, "input").unwrap();
    let back = g.any_term(e).unwrap();
    let k2 = to_kernel(&back);
    assert_eq!(k2, kadd);
}
