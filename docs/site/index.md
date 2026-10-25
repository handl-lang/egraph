# egraph

The generic e-graph / equality-saturation substrate.

## What it is

`handl-egraph` is the reusable e-graph beneath the research stack: `EGraph`,
`Rewrite`, the compiled matcher, deterministic extraction, and the
applications/provenance machinery. It is a **by-contract** port of the proven
`catopt_core.egraph` Python spec — the Python is the specification, this crate
is the composable Rust substrate.

## Modules
- `egraph` — `EGraph`, `Rewrite`, saturation loop, extraction
- `matcher` — the compiled pattern matcher
- `term` — `Term`, `TermAttr` and `from_kernel`/`to_kernel` bridges to the kernel


## Start here

- **Reference** — [public API](/egraph/reference/)
- **How-to** — [task recipes](/egraph/how-to/)
- **Explanation** — [design and rationale](/egraph/explanation/)

No tutorials: this repo is a building block used from Rust. End-to-end
walkthroughs live with the product that composes it — see the
[Handl platform](/handl/).
