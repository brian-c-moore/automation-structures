# automation-structures

[![CI](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml)
[![Formal verification](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml)
[![crates.io](https://img.shields.io/crates/v/automation-structures.svg)](https://crates.io/crates/automation-structures)
[![docs.rs](https://docs.rs/automation-structures/badge.svg)](https://docs.rs/automation-structures)

`automation-structures` is a Rust library of reusable structural building blocks for automation
systems. It supplies state machines for admission, bounded resources, traversal, selection,
propagation, coordination, and execution flow so applications can assemble these roles instead of
implementing them repeatedly.

The library separates structure from domain policy. A structure owns its state, admissible
transitions, and preserved obligations. Callers supply the identifiers, values, scores, costs, and
effects that give those transitions meaning in a particular system.

## Composition

Composition means mechanical assembly of existing structures through explicit connective roles.
Those roles include retained cursors, bounded buffers, counters, markers, accumulated results,
projections, and ordering passes. Named compositions package an assembly that has its own reusable
contract.

## Catalog

The crate exposes the complete current catalog through checked root-level APIs:

- Primitives: `Budget`, `QualityHierarchy`, `ResourceRegistry`, `CompetitiveSelection`,
  `ActuationPass`, `PropagationPass`, `ConvergenceGovernor`, `AuditSink`, and
  `BacktrackingTraversal`.
- Named compositions: `AllocationSnapshot`, `FederatedBudget`, `Bisection`,
  `EquivalenceClass`, `RateLimit`, `Reduction`, `RelationshipGraph`, `Sampler`, `Signal`, and
  `TraversalEngine`.
- Execution modalities: `Sequential`, `ForkJoin`, `StepGraph`, and `StreamGraph`.
- Connective roles: `Projection`, `Cursor`, `Accumulator`, `Marker`, `Counter`, `Buffer`, and
  `OrderingPass`, represented by small state types or root-level relation functions as appropriate.

`CompetitiveSelection` is exposed through its hard, hard-exclusive, soft, and ranked forms. The
connective functions are `projection_consistent` and `strictly_before`; the other connective roles
are state types.

## Example

The checked API rejects transitions that are not currently enabled:

```rust
use automation_structures::Budget;

let mut budget = Budget::new(8);
assert!(budget.try_reserve(3));
assert_eq!(budget.commit_reservation(3), Ok(()));
assert_eq!(budget.available(), 5);
```

Public types encapsulate their state and expose observations plus checked transitions. Rejected
transitions are returned as values.

The runnable [`catalog` example](examples/catalog.rs) constructs and exercises every advertised
primitive, named composition, execution modality, and connective role through the public API:

```text
cargo run --example catalog
```

## Formal basis

The structures are implemented in Rust with Verus contracts over their state, transitions, and
preserved invariants. Formal definitions, refinement mappings, correspondence checks, and the
theory behind the catalog are maintained in the
[automation-structures-research](https://github.com/brian-c-moore/automation-structures-research)
repository.

The crate's formal workflow verifies those contracts directly against the same source distributed
to Rust users.

## Toolchain

The minimum supported Rust version is 1.95. Ordinary development checks are:

```text
cargo check --locked --all-targets
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets --all-features
cargo test --locked --doc --all-features
cargo run --locked --example catalog
RUSTDOCFLAGS="-D warnings" cargo doc --locked --no-deps --all-features
```

GitHub Actions applies those checks on Rust 1.95.0 and current stable Rust across Linux, Windows,
and macOS. A separate workflow verifies `src/verification.rs` with a checksum-pinned Verus
release. See [verification/README.md](verification/README.md) for reproducible verification
details.

## Contributing and security

See [CONTRIBUTING.md](CONTRIBUTING.md) for development expectations. Report suspected
vulnerabilities using the private process in [SECURITY.md](SECURITY.md).

## License

Licensed under the MIT License. See [LICENSE](LICENSE).
