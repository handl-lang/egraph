# Explanation

## Why this crate exists

Equality saturation is the workhorse of the optimisation research: it searches
all equivalent programs at once instead of commuting rewrites. Keeping it generic
— and contract-ported from a proven spec rather than re-invented — means the
research stack and the compiler can share one substrate whose behaviour is
checkable against the Python reference.

## Where it sits

This crate belongs to the research layer of the org — it is not one of the
`engine`/`engine-eqsat`, `tool-*` or `exec-*` repos.

See the [reference](/egraph/reference/) for the API and the
[how-to guides](/egraph/how-to/) for tasks.
