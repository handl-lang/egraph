# How-to guides

Task recipes. Each assumes sibling checkouts of this repo and of the platform
repos it patches.

## Run a saturation

Build an `EGraph`, add rewrite `Rewrite`s, run until `Stop`, then extract; `StopReason` tells you whether it saturated or hit a limit, so a bounded run is never mistaken for a proof.

## Carry kernel terms in

Use `from_kernel` so provenance keys stay comparable with the rest of the platform; `to_kernel` converts back at the boundary.
