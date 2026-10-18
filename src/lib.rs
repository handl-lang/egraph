//! # handl-egraph
//!
//! The generic e-graph / equality-saturation substrate over the kernel's
//! `Term`/`Value` — the named Rust port of the proven Python spec in
//! `catopt-core` (`catopt_core.egraph`: `EGraph`/`Rewrite`, the compiled
//! matcher, deterministic extraction, and the applications/provenance
//! machinery).
//!
//! The port is **by contract, not by translation**: saturation
//! determinism, budget-exhaustion semantics, the bounded-match cap
//! behaviour, and the extraction policy mirror the Python spec; the data
//! layout is idiomatic Rust (ordered sets instead of set+`_member_key`
//! rescans, structural ordering instead of `repr`-keyed signatures).
//! Divergences from the spec are deliberate and named — see
//! `docs` on each item and the crate README.
//!
//! ## What is generic vs. domain
//!
//! The crate ships the substrate only: e-classes of `(op, children,
//! attrs)` nodes, union-find + congruence closure, bounded fixpoint
//! application of [`Rewrite`] rules, deterministic extraction, and the
//! provenance records (`applications`, `enode_app`, `merge_log`) a
//! downstream gauntlet consumes. Domain alphabets — op names, cost
//! models, fold policies — arrive as *data* ([`Term`] trees and
//! `cost_fn` closures), never baked in. The tensor-specific cost
//! alphabets, `dag_cost` policies, and shape domains of the Python
//! package stay in Python.
//!
//! ## Quick start
//!
//! ```
//! use handl_egraph::{EGraph, Rewrite, RunOptions, Term, TermAttr};
//!
//! let mut g = EGraph::new();
//! let x = Term::leaf("x");
//! let zero = Term::leaf("0");
//! let term = Term::opl("add", vec![x.clone(), zero.clone()]);
//! let root = g.add_term(&term, "input").unwrap();
//!
//! // rule: add(?a, 0) -> ?a
//! let rule = Rewrite::new(
//!     "add_zero",
//!     Term::opl("add", vec![Term::var("a"), Term::leaf("0")]),
//!     Term::var("a"),
//! );
//! let stats = g.run(&[rule], root, &mut RunOptions::default()).unwrap();
//! assert_eq!(stats.stop, handl_egraph::StopReason::FixedPoint);
//!
//! let best = g
//!     .extract_best(root, &mut |t: &Term| t.size() as f64, None, None)
//!     .unwrap();
//! assert_eq!(best, x);
//! ```

mod egraph;
mod extract;
mod node;
mod pattern;
mod rewrite;
mod subst;
mod term;
mod term_bridge;
mod union_find;
mod value;

pub use egraph::{
    AddTermError, EGraph, MergeInfo, Offer, RunError, RunOptions, SaturationStats, Stop, StopReason,
};
pub use extract::dag_cost;
pub use node::{ClassId, EClass, ENode};
pub use rewrite::{Application, BoundEnv, Check, Derive, Derived, ProofEdge, Rewrite};
pub use subst::Subst;
pub use term::{Op, Term, TermAttr, attr, attr_meta};
pub use term_bridge::{from_kernel, to_kernel};
pub use union_find::UnionFind;
pub use value::AttrValue;

/// The kernel's `Term` (`hnl_engine::Term`, via `handl_language`) —
/// re-exported so consumers can name it without re-declaring the dep.
pub use hnl_engine::Term as KernelTerm;
