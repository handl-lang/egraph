//! Unit tests for the e-graph substrate: interning, union-find,
//! matching, congruence, and the attr two-tier semantics.

use handl_egraph::{AttrValue, EGraph, Term, UnionFind, attr, attr_meta};

fn leaf(s: &str) -> Term {
    Term::leaf(s)
}

fn op(name: &str, args: Vec<Term>) -> Term {
    Term::opl(name, args)
}

#[test]
fn union_find_basics() {
    let mut uf = UnionFind::default();
    let a = uf.make();
    let b = uf.make();
    let c = uf.make();
    assert_eq!(uf.find(a), a);
    assert!(uf.union(a, b));
    assert_eq!(uf.find(b), uf.find(a));
    assert!(!uf.union(a, b));
    assert!(uf.union(b, c));
    assert_eq!(uf.find(c), uf.find(a));
}

#[test]
fn hash_consing_shares_classes() {
    let mut g = EGraph::new();
    let t = op("add", vec![leaf("x"), leaf("0")]);
    let e1 = g.add_term(&t, "input").unwrap();
    let e2 = g.add_term(&t, "input").unwrap();
    assert_eq!(e1, e2);
    assert_eq!(g.n_enodes(), 3); // add, leaf x, leaf 0
    assert_eq!(g.n_classes(), 3);
}

#[test]
fn metavar_rejected_in_concrete_terms() {
    let mut g = EGraph::new();
    let r = g.add_term(&Term::var("x"), "input");
    assert!(r.is_err());
    let t = Term::op("f", vec![leaf("x")], [attr_meta("dim", "d")]);
    assert!(g.add_term(&t, "input").is_err());
}

#[test]
fn congruence_closure_merges_parents() {
    let mut g = EGraph::new();
    let a = g.add_term(&leaf("a"), "input").unwrap();
    let b = g.add_term(&leaf("b"), "input").unwrap();
    let fa = g.add_term(&op("f", vec![leaf("a")]), "input").unwrap();
    let fb = g.add_term(&op("f", vec![leaf("b")]), "input").unwrap();
    assert_ne!(fa, fb);
    assert!(g.union(a, b));
    // Rebuild closes congruence: f(a) and f(b) re-key identically.
    g.rebuild(None);
    assert_eq!(g.find(fa), g.find(fb));
}

#[test]
fn attr_identity_strict_match_lenient() {
    let mut g = EGraph::new();
    // `dim=0` and `dim=0.0` are DISTINCT enodes (spelling-strict
    // identity — the spec's repr-keyed _sig port).
    let i = g
        .add_term(
            &Term::op("f", vec![leaf("x")], [attr("dim", AttrValue::Int(0))]),
            "input",
        )
        .unwrap();
    let f = g
        .add_term(
            &Term::op("f", vec![leaf("x")], [attr("dim", AttrValue::Float(0.0))]),
            "input",
        )
        .unwrap();
    assert_ne!(i, f);
    // …but the match is numerically lenient: an `Int(0)` pattern attr
    // matches the `Float(0.0)` enode.
    let pat = Term::op("f", vec![Term::var("x")], [attr("dim", AttrValue::Int(0))]);
    assert_eq!(g.matches(&pat, f, None).len(), 1);
    assert_eq!(g.matches(&pat, i, None).len(), 1);
    // Bool↔int coercion (the Python tower's `True == 1`).
    let b = g
        .add_term(
            &Term::op("g", vec![leaf("x")], [attr("dim", AttrValue::Bool(true))]),
            "input",
        )
        .unwrap();
    let patg = Term::op("g", vec![Term::var("x")], [attr("dim", AttrValue::Int(1))]);
    assert_eq!(g.matches(&patg, b, None).len(), 1);
}

#[test]
fn match_shared_metavar_consistency() {
    let mut g = EGraph::new();
    // eq(x, x) vs eq(x, y): the shared metavar must bind the same class.
    let exx = g
        .add_term(&op("eq", vec![leaf("x"), leaf("x")]), "input")
        .unwrap();
    let exy = g
        .add_term(&op("eq", vec![leaf("x"), leaf("y")]), "input")
        .unwrap();
    let pat = op("eq", vec![Term::var("v"), Term::var("v")]);
    assert_eq!(g.matches(&pat, exx, None).len(), 1);
    assert_eq!(g.matches(&pat, exy, None).len(), 0);
}

#[test]
fn match_attr_metavar_binds() {
    let mut g = EGraph::new();
    let e = g
        .add_term(
            &Term::op("proj", vec![leaf("x")], [attr("axis", AttrValue::Int(2))]),
            "input",
        )
        .unwrap();
    let pat = Term::op("proj", vec![Term::var("v")], [attr_meta("axis", "d")]);
    let ms = g.matches(&pat, e, None);
    assert_eq!(ms.len(), 1);
    assert_eq!(ms[0].attrs.get("d"), Some(&AttrValue::Int(2)));
}

#[test]
fn bounded_enumeration_caps() {
    let mut g = EGraph::new();
    let aa = g
        .add_term(&op("f", vec![leaf("a"), leaf("a")]), "input")
        .unwrap();
    let ab = g
        .add_term(&op("f", vec![leaf("a"), leaf("b")]), "input")
        .unwrap();
    let bb = g
        .add_term(&op("f", vec![leaf("b"), leaf("b")]), "input")
        .unwrap();
    g.rebuild(None);
    let pat = op("f", vec![Term::var("x"), Term::var("y")]);
    // Each op class matches its own member(s) — arity 2 with distinct
    // leaf bindings.
    let total: usize = [aa, ab, bb]
        .into_iter()
        .map(|e| g.matches(&pat, e, None).len())
        .sum();
    assert!(total >= 3);
    // The bounded path honours the cap.
    let capped = g.matches(&pat, aa, Some(1));
    assert!(capped.len() <= 1);
}

#[test]
fn any_term_prefers_leaf_and_is_deterministic() {
    let mut g = EGraph::new();
    let x = g.add_term(&leaf("x"), "input").unwrap();
    let fx = g.add_term(&op("f", vec![leaf("x")]), "input").unwrap();
    g.union(x, fx);
    g.rebuild(None);
    let root = g.find(x);
    // A class holding both a leaf and an op member resolves to the leaf.
    assert_eq!(g.any_term(root), Some(leaf("x")));
}

#[test]
fn locate_pins_the_member_enode() {
    let mut g = EGraph::new();
    let t = op("f", vec![leaf("x")]);
    let e = g.add_term(&t, "input").unwrap();
    let (eid, en) = g.locate(&t, None);
    assert_eq!(eid, Some(g.find(e)));
    let en = en.expect("member enode");
    assert_eq!(&*en.op, "f");
}
