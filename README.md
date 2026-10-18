# egraph

`handl-egraph` — the generic e-graph / equality-saturation substrate
over the kernel's `Term`/`Value`. The named Rust port of the proven
Python spec in `catopt-core` (`catopt_core.egraph`: `EGraph`/`Rewrite`,
the compiled matcher, deterministic extraction, and the
applications/provenance machinery). The port is **by contract, not by
translation** — the Python is the spec; this crate is the composable
substrate any domain kit can use.

Sibling-repo deps are git dependencies (`branch = "main"`); the
`[patch]` tables (regenerate with `scripts/dev-link.sh`) resolve them
from sibling checkouts for local development — or
`source ~/.cache/devin/handl_deps.env` for the git-insteadOf map.

## What it is

An `EGraph` is a union-find over hash-consed `(op, children, attrs)`
enodes, partitioned into e-classes of semantically-equal terms:

- **Interning** — `add_term` / `add_enode` / `add_leaf` hash-cons every
  node; identical structures share a class.
- **Congruence closure** — `rebuild` re-canonicalizes children and
  merges classes whose canonical members coincide (incremental
  `_cong_owner`/`_cong_pend` worklist, drained in canonical order).
- **Matching** — `matches(pattern, eid)` enumerates `Subst`s: term
  metavariables (`Term::Var`) bind e-class ids, attribute
  metavariables (`TermAttr::Meta`) bind `AttrValue`s. Patterns compile
  once per graph (`(op, arity)` targeted eligibility + child-op
  existence checks).
- **Saturation** — `run(rules, root, opts)` is bounded fixpoint
  application over the dirty frontier: `max_iterations`, `max_nodes`,
  per-rule `rule_budgets` (bounded saturation for explosive rules like
  comm/assoc), `Stop::FixedPoint` or lazy `Stop::Improving` with
  `patience` + a `cost_fn`.
- **Extraction** — `extract_best(eid, cost_fn, overrides, bans)` picks
  the minimum-cost member, DAG-aware (each class billed once), with
  `nops` tie-break and canonical member order. `extract_min_depth`,
  `extract_alternatives`, `diverse_classes`, `dag_cost` alongside.
- **Provenance** — every merge records a `ProofEdge`; every
  graph-changing firing records an `Application`; `enode_app` maps a
  produced enode to the application that created it; `enode_origin` /
  `enode_birth` tag introductions. `EGraph::offer` is the non-local
  pass ritual: offer a member under a synthesized pointwise witness so
  the merge replays like an ordinary rule step. `EGraph::quotient()`
  drops all tracking (truncation level 1).

## The boundary — generic vs. domain

The crate ships **substrate only**. Domains inject their alphabets as
data:

- op names and term shapes — `Term::op("your_op", …)`;
- cost models — `cost_fn: FnMut(&Term) -> f64` closures;
- side conditions — `Rewrite::with_check` / `with_derive` hooks over
  the resolved `BoundEnv`.

Deliberately *not* ported (they are domain, not substrate): the
tensor-specific `FOLD_OPS` alphabet and the param-only compile-time
discount it enables, `dag_cost` pricing policies, the fusion
tie-break, `JOINT_SHAPES`-style domain data, and the certificate
reconstruction layer (`proof.py`) — the level-2 provenance record this
crate ships is exactly what that layer replays.

## Kernel bridge

`from_kernel` / `to_kernel` lift and lower `hnl_engine::Term`:

- every `Term` variant maps to an `Op` node keyed by variant tag with
  `Term`-fields as children in declaration order (a `Term::Op`'s enode
  op is the domain `name`, `dim` rides child slot 0);
- `Const`/`Opaque` terms become leaves whose keys are their own
  serialized `Term` — **self-describing**, replacing the spec's global
  `_LeafRegistry` (a named wart);
- unknown enode shapes lower back to native `Term::Op`s or `Opaque`
  markers — `to_kernel` is total.

## Spec divergences (named, deliberate)

- **Structural ordering** — `ENode: Ord` is the canonical member order
  (the `_member_key` contract: a total, process-independent order for
  every decision-reaching scan). The spec computes it as
  `(op, children, repr(attrs))`; structural `Ord` keeps the invariant
  without reprs or hash-order risk.
- **Eager per-class match enumeration** — the spec streams matches
  through frozen-read `_Epoch` overlays; the observable semantics are
  the pre-streaming eager list, which we enumerate directly (bounded
  per class by `MATCH_CAP`, `_m_bounded` cap quirk and all).
- **Typed `Subst`** — `terms`/`attrs` maps replace the spec's
  `"$attr:"` key-mangling.
- **`add_term` rejects metavariables** — a `Var`/`Meta` in a concrete
  term errors (`AddTermError`) where the spec leaf-interns a `str`.
- **Attr two-tier semantics, exactly** — identity is spelling-strict
  (`0` ≠ `0.0`, `0.0` ≠ `-0.0`); match-time is numerically lenient
  (`match_eq`, bool↔int coercion included). Divergence noted: NaN
  payloads compare bit-strict where `repr` collapsed them.

## Usage

```rust
use handl_egraph::{EGraph, Rewrite, RunOptions, Term};

let mut g = EGraph::new();
let t = Term::opl("add", vec![Term::leaf("x"), Term::leaf("0")]);
let root = g.add_term(&t, "input")?;

// add(?a, 0) -> ?a
let r = Rewrite::new(
    "add_zero",
    Term::opl("add", vec![Term::var("a"), Term::leaf("0")]),
    Term::var("a"),
);
let stats = g.run(&[r], root, &mut RunOptions::default())?;
let best = g.extract_best(root, &mut |t: &Term| t.size() as f64, None, None);
assert_eq!(best, Some(Term::leaf("x")));
```

A domain kit consumes the crate as a plain lib: intern its terms
(`from_kernel` for `Term`-shaped programs or `Term::op` directly),
run its law bank under `RunOptions { rule_budgets, .. }`, extract with
its own `cost_fn`, and read `applications()`/`merge_log()`/`enode_app`
for downstream proof/gauntlet work. There is no `Kernel::Host`/`Plugin`
seam — the substrate is data-driven by construction; a domain wraps it
however its kit needs.

## Verification

```sh
cargo test        # unit + saturation fixtures
cargo fmt --check
cargo clippy --all-targets
```

The recursion-heavy walks carry `RUST_MIN_STACK=32MiB` for test
threads (`.cargo/config.toml`), matching the org convention.
