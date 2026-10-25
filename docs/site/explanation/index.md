# Explanation

## Why this crate exists

Equality saturation is the workhorse of the optimisation research: it searches
all equivalent programs at once instead of commuting rewrites. Keeping it generic
— and contract-ported from a proven spec rather than re-invented — means the
research stack and the compiler can share one substrate whose behaviour is
checkable against the Python reference.

## Where it sits

This crate belongs to the `engine-*` family. Plugins, kits and hosts reach it
through the kit's operation slot, so the engine can be swapped without touching a
language definition.

See the [reference](/egraph/reference/) for the API and the
[how-to guides](/egraph/how-to/) for tasks.
