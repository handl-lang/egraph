+++
id = "I-001"
title = "Release build panics: uf.make() inside debug_assert"
status = "done"
created = "2026-11-08"
priority = "high"
+++

handl-egraph @ 231172f: cargo build --release produced a binary that panicked on every spec — union_find.rs:25 index OOB (len 0, index 0), exit 101. Root cause: insert_enode wrapped the mutating uf.make() call in debug_assert_eq!, so release compiled the allocation out and the union-find stayed empty; first find() indexed an empty parent Vec. Fixed in abc0294 (hoist the call, keep the id check as debug_assert) + regression test interned_ids_resolve_in_union_find; lock refresh 71d9535. Verified: cargo test --release green (11+14+1), debug green; consumer mlopt-kit egraph-run still pinned to 231172f in graphopt Cargo.lock — needs cargo update -p handl-egraph to pick up the fix.

## Resolution

Fixed on main: abc0294 (src/egraph.rs insert_enode — uf.make() hoisted out of debug_assert_eq!) + tests/core.rs regression test; 71d9535 lock refresh. cargo test green in debug and --release. Downstream: graphopt mlopt-kit pins handl-egraph@231172f — run cargo update -p handl-egraph there to pick up the fix.
