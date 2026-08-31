# automation-structures

[![CI](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml)
[![Formal verification](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml)
[![crates.io](https://img.shields.io/crates/v/automation-structures.svg)](https://crates.io/crates/automation-structures)
[![docs.rs](https://docs.rs/automation-structures/badge.svg)](https://docs.rs/automation-structures)
[![license](https://img.shields.io/crates/l/automation-structures.svg)](https://github.com/brian-c-moore/automation-structures#license)

`automation-structures` is a Rust library of reusable structural building blocks for automation
systems. It supplies checked state machines for admission, bounded resources, traversal,
selection, propagation, coordination, and execution flow so applications can assemble these roles
instead of implementing them repeatedly.

A structure owns its state, admissible transitions, and preserved obligations. Applications supply
the identifiers, values, scores, costs, policies, and effects that give those transitions domain
meaning.

## Install

```text
cargo add automation-structures
```

The default feature set exposes the checked runtime API at the crate root.

## Quick start

```rust
use automation_structures::Budget;

let mut budget = Budget::new(8);
assert!(budget.try_reserve(3));
budget.commit_reservation(3)?;
assert_eq!(budget.allocated(), 3);
assert_eq!(budget.available(), 5);

# Ok::<(), automation_structures::BudgetError>(())
```

Disabled transitions are explicit. Methods that can distinguish invalid input from disabled state
return `Result`; conditional transitions named `try_*` return `bool`; indexed observations return
`Option`.

## What composition means

Composition is the mechanical assembly of existing owners through explicit connective roles. A
composition contains the structure owners, configuration, and only the coupling state needed
to make their transitions commit together. It does not reimplement the component state machines.

For example, `SelectThenActuate` owns hard selection for each seat and one shared `ActuationPass`.
Selection determines the allocation; actuation records the corresponding effect; the composition
closes only after every selected allocation has been applied.

```rust
use automation_structures::SelectThenActuate;

let mut pass = SelectThenActuate::new(1, 2)?;
pass.update_score(0, 0, 4)?;
pass.update_score(0, 1, 9)?;
assert_eq!(pass.evaluate(0)?, 1);
pass.actuate(0)?;
pass.finish()?;
assert!(pass.is_complete());

# Ok::<(), Box<dyn std::error::Error>>(())
```

Named compositions package recurring assemblies behind one checked contract. Applications can also
compose the root types directly.

## Choose a structure

### Primitives

| Need | Type | Structural guarantee |
| --- | --- | --- |
| Own finite capacity through allocation, reservation, and eviction | `Budget` | Every capacity unit has one accounted lifecycle |
| Map unique resource identifiers to values | `ResourceRegistry` | At most one live value per key |
| Retain an append-only operation chain | `AuditSink` | Every entry names its predecessor and derived chain value |
| Run snapshot-local graph updates | `PropagationPass` | Each node updates once per round from the same snapshot |
| Separate allocation from effect commitment | `ActuationPass` | Each allocated seat actuates at most once before closure |
| Maintain ordered parent-child quality and cost constraints | `QualityHierarchy` | Single parent plus level and cost ordering |
| Traverse choices with exact undo | `BacktrackingTraversal` | Every descent records the inverse used by ascent |
| Select one highest-scoring candidate | `CompetitiveSelectionHard` | Argmax with deterministic lowest-index ties |
| Allocate unique winners across several seats | `CompetitiveSelectionHardExclusive` | Hard selection plus cross-seat mutual exclusion |
| Distribute a fixed weight total | `CompetitiveSelectionSoft` | Reserved-floor sequential Webster allocation |
| Select the top `k` candidates | `CompetitiveSelectionRanked` | Bounded multiplicity with score ordering |
| Settle and reawaken from a bounded delta history | `ConvergenceGovernor` | Phase-aware convergence and reawakening |

### Connective forms

| Need | Type or function | Structural guarantee |
| --- | --- | --- |
| Preserve monotone progress | `Cursor` | Position never regresses |
| Move values from pending to retained history | `Accumulator<T>` | Order and membership are preserved across the boundary |
| Retain bounded FIFO state | `Buffer<T>` | Capacity, order, and head removal are owned once |
| Retain monotone numeric progress | `Counter` | Counter state and increment transition |
| Retain a binary fact | `Marker` | Marked/unmarked state |
| Relate an owner to a derived view | `projection_consistent` | The projection equals the owner-derived observation |
| Relate two ordered passes | `strictly_before` | The first position strictly precedes the second |

### Named compositions

| Need | Type | Assembly |
| --- | --- | --- |
| Admit nodes while charging their costs | `AllocationSnapshot` | `ResourceRegistry + Budget` |
| Delegate master capacity to sub-pools | `FederatedBudget` | One master `Budget` plus one `Budget` per pool |
| Find a monotone boundary | `Bisection` | Probe `Budget` plus interval cursor relation |
| Maintain a merge-bounded partition | `EquivalenceClass` | Parent/rank registries plus operation `Budget` |
| Enforce a fixed logical-clock window | `RateLimit` | Operation `Budget` plus clock and window configuration |
| Incrementally reduce an ordered input | `Reduction` | `AuditSink` instantiated with the reduction operation |
| Store weighted edges and derive adjacency | `RelationshipGraph` | Edge `ResourceRegistry` plus projection relation |
| Select a bounded sample without replacement | `Sampler` | `ActuationPass + Budget` |
| Notify listeners after real value changes | `Signal` | Value-change `AuditSink` plus one `Cursor` per listener |
| Traverse queued graph work under a budget | `TraversalEngine` | Graph, budget, marker, accumulator, and buffer owners |
| Select allocations and commit their effects | `SelectThenActuate` | Hard selection owners plus one `ActuationPass` |

### Execution modalities

| Need | Type | Structural guarantee |
| --- | --- | --- |
| Execute a fixed sequence | `Sequential` | One active step and ordered committed history |
| Run workers behind a join barrier | `ForkJoin` | Worker lifecycle, barrier, and stable output snapshot |
| Execute dependency-governed steps | `StepGraph` | A step becomes ready only after its predecessors complete |
| Move bounded records through FIFO stages | `StreamGraph` | Backpressure, FIFO order, and exact progress counters |

The runnable [catalog example](https://github.com/brian-c-moore/automation-structures/blob/main/examples/catalog.rs)
constructs and exercises every checked root type:

```text
cargo run --example catalog
```

## Observation and ownership

Public checked types encapsulate their state owner. They expose scalar observations, borrowed
slices, and iterators without returning mutable access to invariant-bearing state. Small value-like
connectives implement the standard traits their semantics support, including `Debug`, `Default`,
equality, conversions, and iteration.

Authority-bearing state machines are not `Clone`. Cloning one would duplicate the apparent owner of
a budget, allocation pass, audit chain, or execution lifecycle. Transfer them by move or place them
behind the application’s chosen shared-ownership and synchronization policy.

Every public error enum implements `Debug`, `Display`, `std::error::Error`, equality, and copy
semantics. Error enums are non-exhaustive so new diagnostic distinctions can be added without
breaking downstream matches.

## Features

| Feature | Contents |
| --- | --- |
| default | Checked runtime types and relations at the crate root |
| `proof-api` | Verus carriers, specifications, and proof relations under `primitives`, `connectives`, `compositions`, `modalities`, and `integration` |

Verified downstream crates can enable the proof API directly:

```toml
[dependencies]
automation-structures = { version = "0.2", features = ["proof-api"] }
```

The checked API remains available when `proof-api` is enabled. docs.rs builds all features.

## Formal basis

The distributed Rust source contains Verus contracts for the carrier state, enabled transitions,
and preserved invariants. The formal workflow verifies the real crate root and an external proof
consumer against the unpacked `.crate` archive. Known-answer executables and ordinary downstream
consumers exercise the same archive.

Formal definitions, refinement mappings, correspondence checks, and the theory behind the catalog
are maintained in
[automation-structures-research](https://github.com/brian-c-moore/automation-structures-research).
Changes to structure definitions, transition semantics, or preserved obligations originate there
and flow downstream into this crate.

The [verification guide](https://github.com/brian-c-moore/automation-structures/blob/main/verification/README.md)
records the exact verifier identity, package boundary, and reproducible commands.

## Compatibility

The minimum supported Rust version is 1.95.0. CI tests Rust 1.95.0 and current stable Rust on Linux,
Windows, and macOS. Public API compatibility is checked against the latest crates.io release.

The crate follows Cargo semantic versioning. Before 1.0, a change from `0.x` to `0.(x + 1)` may
contain API changes; patch releases preserve the public API. Changes to formal semantics are called
out independently of Rust API compatibility.

## Contributing and security

The [contribution guide](https://github.com/brian-c-moore/automation-structures/blob/main/CONTRIBUTING.md)
defines the downstream implementation and evidence workflow. State ownership and composition
are mapped in
[MAINTAINER_ARCHITECTURE.md](https://github.com/brian-c-moore/automation-structures/blob/main/MAINTAINER_ARCHITECTURE.md).

Report suspected vulnerabilities through the private process in the
[security policy](https://github.com/brian-c-moore/automation-structures/blob/main/SECURITY.md).

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](https://github.com/brian-c-moore/automation-structures/blob/main/LICENSE-APACHE)
  or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
  ([LICENSE-MIT](https://github.com/brian-c-moore/automation-structures/blob/main/LICENSE-MIT)
  or <https://opensource.org/licenses/MIT>)

at your option.
