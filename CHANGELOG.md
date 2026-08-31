# Changelog

All notable changes to this crate are documented here.

## 0.2.0 - 2026-08-31

- Replaces the invariant-breaking root `Buffer`, `Counter`, and `Marker` proof carriers with
  checked, encapsulated facades. Proof carriers remain available through `proof-api`.
- Exposes the carrier and relation modules through the opt-in `proof-api` feature for
  verified downstream crates.
- Aligns the Cargo `vstd` dependency with the checksum-pinned Verus release used by formal CI.
- Adds a packaged-artifact Cargo consumer gate and an external Verus consumer gate.
- Reconciles named compositions with their declared parts and imports the retained
  catalog relations required by verified consumers.
- Preserves the published `Accumulator` API while moving its state and transitions into the
  connective owner.
- Adds complete read-only observations and iterators without exposing mutable invariant-bearing
  state.
- Implements standard `Debug`, `Display`, and `Error` contracts across the public API and compiles
  an example for every checked public structure.
- Documents the complete checked and proof APIs, composition model, ownership map, feature model,
  compatibility policy, and formal boundary.
- Dual-licenses the crate under MIT OR Apache-2.0.
- Makes the publication archive contents explicit and adds the reusable crate-quality policy.
- Adds automated public API compatibility, dependency policy, archive-consumer, and documentation
  gates.

## 0.1.1 - 2026-08-31

- Publishes the initial crate and applies the first dependency-automation updates.

## 0.1.0 - 2026-08-30

- Introduces the initial Automation Structure primitives, connective roles, named compositions,
  and execution carriers.
- Provides checked public entry points for the complete current catalog of primitives, connective
  roles, named compositions, and execution modalities.
- Keeps proof carriers private so their internal state and Verus preconditions are not accidental
  consumer API.
- Computes convergence-window averages inside `ConvergenceGovernor` rather than trusting a
  caller-supplied derived value.
- Uses the same Rust source for ordinary Cargo builds and Verus contracts maintained with the
  Automation Structures research project.
- Provides a runnable downstream-style catalog example that constructs and exercises every public
  structure.
- Adds cross-platform MSRV and stable-Rust CI, strict documentation and Clippy gates, package
  verification, dependency review, Dependabot maintenance, and checksum-pinned Verus CI.
- Uses Rust 2024 edition with Rust 1.95.0 as the minimum supported Rust version.
