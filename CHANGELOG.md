# Changelog

All notable changes to this crate are documented here.

## 0.2.2 - 2026-09-02

- Defines ownership relative to a trusted frame and separates Rust state ownership, accountable
  obligation ownership, delegation, assurance, guarantee, and ownership transfer. Documents how
  check/act separation creates a trust and time-of-check/time-of-use boundary unless one owner or
  an explicit protocol binds the observation to the transition.
- Adds precise proof-facing predicates for recorded-leaf validity, sequential history-position
  agreement, stream count conservation, and the governed-commit bridge contract. The prior names
  remain compatibility aliases with explicit semantic ceilings.
- Strengthens `TraversalEngine` and `TraversalBudgetComposition` with exact accepted-node cost
  accounting and exposes committed accepted cost through the checked API.
- Adds state-level `StreamGraph` enabledness and a checked observation while keeping scheduler
  progress and fairness outside the claim.
- Clarifies that the default `AuditSink` hash is a collision-prone model function, `ActuationPass`
  records effects rather than proving external execution, `Sampler` does not establish randomness
  quality, and the public `RelationshipGraph` is the selected irreflexive profile.
- Presents the primitive catalog as nine families, with four public selection carriers under the
  single `CompetitiveSelection` family.

## 0.2.1 - 2026-08-31

- Strengthens proof-facing constructors, observers, transitions, and batch operations from
  invariant-only results to exact input/state effects, rejection stutter, and untouched-owner
  frames.
- Makes `Buffer` removal and `ResourceRegistry` replacement/removal preserve deterministic
  survivor order and exposes that order in their Verus contracts.
- Binds allocation capture, absent binary-search results, union results, traversal frontiers,
  signal history, soft-selection batch construction, and governed-commit recovery steps to their
  complete executable outcomes.
- Adds adversarial controls for order corruption, incomplete folds, false success, wrong-owner
  updates, history replacement, constructor substitution, tie-breaking drift, and crash/restart
  durable-state mutation.
- Expands checked-facade tests across sampler admission/rejection, traversal skipping, four-stage
  streaming, deterministic registry/buffer ordering, constructor origins, and owner frames.

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
