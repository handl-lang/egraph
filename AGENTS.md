# egraph

`handl-egraph` — the generic e-graph / equality-saturation substrate
over the kernel's `Term`/`Value`. The named Rust port of the proven
Python spec in `catopt-core` (`catopt_core.egraph`). The port is **by
contract, not by translation** — the Python is the spec; this crate is
the composable substrate any domain kit can use.

## Layout

| path | role |
| --- | --- |
| `src/{egraph,extract,node,pattern,rewrite,subst,term_bridge}.rs` | union-find e-graph, congruence closure, compiled matcher, deterministic extraction, term bridge |
| `tests/` | substrate tests |
| `scripts/dev-link.sh` | regenerates `[patch]` tables for sibling checkouts |
| `project/`, `docs/` | project docs worktree + engine docs |
| `xtask/` | vendored gate crate (`fmt`, `clippy`, `test`, `doc`, `gate`) |
| `workflows/gate.yaml` | per-push gate — `handl-gates` rust campaign via bupha |

## Contract

- An `EGraph` is a union-find over hash-consed `(op, children, attrs)`
  enodes partitioned into e-classes: `add_term`/`add_enode`/`add_leaf`
  intern, `rebuild` does incremental congruence closure,
  `matches(pattern, eid)` enumerates `Subst`s (`Term::Var` binds
  e-class ids, `TermAttr::Meta` binds `AttrValue`s).
- Sibling deps are git deps (`branch = "main"`); `[patch]` tables
  resolve them locally — regenerate with `scripts/dev-link.sh`, or
  `source ~/.cache/devin/handl_deps.env` for the git-insteadOf map.

## Verification

```bash
cargo xtask gate        # fmt → clippy → test → doc
```

<!-- myco:agent-awareness -->

## Agent awareness

- Session start / any work discussion: run `myco status --prompt`
  before proposing next steps — know the board first.
- User describes new work → offer to capture it (`myco todo add`,
  `issue new`, `proposal new`). Don't wait to be asked.
- Picking up a task: `myco resume <ID>` is the briefing.
- Wrapping up: `myco handoff <ID>` anything resumable; keep statuses
  honest (claimed → in-progress → blocked/done).

<!-- /myco:agent-awareness -->
