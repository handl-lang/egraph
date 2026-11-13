# egraph

The generic e-graph / equality-saturation substrate.

## What it is

`handl-egraph` is the reusable e-graph beneath the research stack: `EGraph`,
`Rewrite`, the compiled matcher, deterministic extraction, and the
applications/provenance machinery. It is a **by-contract** port of the proven
`catopt_core.egraph` Python spec — the Python is the specification, this crate
is the composable Rust substrate.

## Modules
- `egraph` — `EGraph`, `Rewrite`, the saturation loop (the compiled
  matcher lives here — there is no separate `matcher` module), extraction
- `extract` — deterministic extraction (`dag_cost`)
- `node` — `EClass`/`ENode`/`ClassId` and the `op -> members` index
- `pattern` — pattern compilation for the matcher
- `rewrite` — `Rewrite`, `Application`/`Derived` provenance, checks/derivations
- `subst` — `Subst`, the match substitution
- `term` — `Term`, `Op`, `TermAttr` and attribute plumbing
- `term_bridge` — `from_kernel`/`to_kernel` bridges to the kernel `Term`/`Value`
- `union_find` — the e-class union-find
- `value` — `AttrValue`


## Start here

- **Reference** — [public API](/egraph/reference/)
- **How-to** — [task recipes](/egraph/how-to/)
- **Explanation** — [design and rationale](/egraph/explanation/)

No tutorials: this repo is a building block used from Rust. End-to-end
walkthroughs live with the product that composes it — see the
[Handl platform](/handl/).
