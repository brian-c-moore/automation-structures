# automation-structures

[![CI](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml)
[![Formal verification](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml)
[![crates.io](https://img.shields.io/crates/v/automation-structures.svg)](https://crates.io/crates/automation-structures)
[![docs.rs](https://docs.rs/automation-structures/badge.svg)](https://docs.rs/automation-structures)
[![license](https://img.shields.io/crates/l/automation-structures.svg)](https://github.com/brian-c-moore/automation-structures#license)

`automation-structures` provides checked state machines. Its reusable types track resource budgets,
select candidates, traverse graphs with cost limits, and coordinate execution steps through
operations that check whether the requested state change is allowed before applying it.

Your application runs external work. It supplies inputs and calls the transition methods; the
execution types track state without starting threads, while the tables below specify each type's
supported inputs and its limits on graph shapes or resource costs.

## Install

```text
cargo add automation-structures
```

The default feature set exposes the checked runtime API at the crate root.
Requires Rust 1.95 or later.

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

Check each method's return type. For example, `try_reserve` returns `false` when capacity is
unavailable, whereas `commit_reservation` returns an error if the amount exceeds the reservation;
methods that distinguish errors use `Result`, and observations that may be absent use `Option`.

## What composition means

Compositions reuse the same state machines. Each supplied composition stores its component state
machines and exposes their combined operation through one API, so callers use that operation to
coordinate the state changes required by the composition's contract.

Your application performs external effects. `SelectThenActuate` selects a candidate for each seat
and records modeled effects through one shared `ActuationPass`; the pass can finish only after
every allocation selected for a seat has a corresponding recorded effect.

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

## Choose a structure

### Resource and processing types

| Need | Type | Behavior and limits |
| --- | --- | --- |
| Track capacity through allocation, reservation, and eviction | `Budget` | Allocated, reserved, and pending-eviction charges together stay within capacity |
| Map unique resource identifiers to values | `ResourceRegistry` | At most one live value per key |
| Retain an append-only operation chain | `AuditSink` | Entries link to their predecessors using a recomputed chain value; this type does not provide cryptographic hashing, durable storage, or tamper detection |
| Run snapshot-local graph updates | `PropagationPass` | Each node updates once per round from the same snapshot |
| Track completion after allocation | `ActuationPass` | Each allocated seat records at most one corresponding effect before closure; the application performs external effects |
| Maintain ordered parent-child quality and cost constraints | `QualityHierarchy` | Single parent plus level and cost ordering |
| Traverse choices with exact undo | `BacktrackingTraversal` | Descent records the inverse used by ascent; recorded visits are valid full-depth leaves, but need not cover every leaf |
| Select one winner, exclusive winners, weighted shares, or a ranked subset | `CompetitiveSelectionHard`, `CompetitiveSelectionHardExclusive`, `CompetitiveSelectionSoft`, `CompetitiveSelectionRanked` | Each type enforces its documented allocation and tie rules |
| Track convergence and resume after changes | `ConvergenceGovernor` | Uses a bounded delta history and explicit phases; window length and maximum delta are each limited to one billion |

### Small state helpers

| Need | Type or function | Behavior and limits |
| --- | --- | --- |
| Preserve monotone progress | `Cursor` | Position never regresses |
| Move values from pending to retained history | `Accumulator<T>` | Order and membership are preserved across the boundary |
| Retain bounded FIFO state | `Buffer<T>` | Enforces capacity and removes items from the head in insertion order |
| Retain a nonnegative count | `Counter` | Checked increment and decrement within the `u64` range |
| Retain a binary fact | `Marker` | Marked/unmarked state |
| Compare projected and source membership flags | `projection_consistent` | Reports whether the two supplied Boolean values agree |
| Relate two ordered passes | `strictly_before` | The first position strictly precedes the second |

### Combined state machines

| Need | Type | Behavior and limits |
| --- | --- | --- |
| Admit nodes while charging their costs | `AllocationSnapshot` | `ResourceRegistry + Budget` |
| Delegate master capacity to sub-pools | `FederatedBudget` | One master `Budget` plus one `Budget` per pool |
| Model bisection around a known threshold | `Bisection` | Probe `Budget` plus interval cursor relation; the caller supplies the threshold, with no external predicate interface |
| Merge disjoint sets within an operation budget | `EquivalenceClass` | Parent/rank registries plus operation `Budget` |
| Enforce a positive-duration logical-clock window | `RateLimit` | Operation `Budget` plus caller-driven clock and window configuration; the checked constructor rejects zero duration |
| Incrementally sum an ordered `u64` input | `Reduction` | Sums values in order through `AuditSink`; at most one billion items, each at most one billion |
| Store weighted edges and derive adjacency | `RelationshipGraph` | Stores edges in a `ResourceRegistry` and rejects self-loops |
| Select a bounded weighted sample without replacement | `Sampler` | `ActuationPass + Budget`; caller choices must be in support, but no randomness-quality claim is made |
| Notify listeners after real value changes | `Signal` | Value-change `AuditSink` plus one `Cursor` per listener |
| Traverse a star graph under a fixed-cost budget | `TraversalEngine` | `RelationshipGraph + Budget + Marker + Accumulator + Buffer`; every accepted node costs two units |
| Select allocations and commit their effects | `SelectThenActuate` | One hard selection per seat plus one `ActuationPass` |

### Execution state

| Need | Type | Behavior and limits |
| --- | --- | --- |
| Track a fixed sequence | `Sequential` | One active step; the completed-history length equals the current position |
| Track workers behind a join barrier | `ForkJoin` | Worker lifecycle, barrier, and stable output snapshot |
| Track steps with predecessor dependencies | `StepGraph` | A step becomes ready only after its predecessors complete |
| Move bounded records through a three- or four-stage FIFO chain | `StreamGraph` | Tracks backpressure, FIFO order, and record counts; your runtime must schedule and advance the stages |

The runnable [catalog example](https://github.com/brian-c-moore/automation-structures/blob/main/examples/catalog.rs)
constructs and exercises every checked root type:

```text
cargo run --example catalog
```

## State access and errors

State changes go through checked methods. Public types expose read-only observations as values
or borrowed views such as slices and iterators, while the small state helpers provide the
applicable standard traits for debugging, default values, equality, conversions, and iteration.

Move state machines to transfer ownership. Types that track budgets, allocations, audit chains,
and execution lifecycles do not implement `Clone`, because a copy would create two independent
accounts of the same work or capacity while leaving the application responsible for the resource.
If callers share an instance, synchronize access and route resource changes through that same
accounting. Reading available capacity does not reserve it; use an admission method before
charging work to it.

Match error enums non-exhaustively. Each public error enum implements `Debug`, `Display`,
`std::error::Error`, equality, and copy semantics, with the non-exhaustive restriction so that a
later release can add an error variant without breaking downstream matches.

## Features

| Feature | Contents |
| --- | --- |
| default | Checked runtime types and relations at the crate root |
| `proof-api` | Verus carriers, specifications, and proof relations under `primitives`, `connectives`, `compositions`, `modalities`, and `integration` |

Verified downstream crates can enable the proof API directly:

```toml
[dependencies]
automation-structures = { version = "0.2.3", features = ["proof-api"] }
```

Use crate-root types in application code. Enabling `proof-api` keeps the checked API available
and exposes lower-level proof types whose preconditions are checked by Verus but may not be
enforced at runtime by an ordinary Rust build. docs.rs builds all features.

## Verification and limits

Verus checks the encoded contracts. CI verifies `src/lib.rs` and an external proof consumer
against the extracted `.crate` archive; known-answer executables and ordinary Rust consumers
exercise the packaged code through concrete calls and check their expected results.
The [verification guide](https://github.com/brian-c-moore/automation-structures/blob/main/verification/README.md)
lists the verifier version and commands.

Propose structural changes in research first.
[automation-structures-research](https://github.com/brian-c-moore/automation-structures-research)
maintains the formal definitions, refinement mappings, correspondence checks, and theory behind
the catalog; accepted changes to transition rules and preserved contract clauses are then
implemented in this crate's Rust types.

## Compatibility

Rust 1.95.0 is the minimum. CI tests that version on Linux and current stable Rust
on Linux, Windows, and macOS. Public API compatibility is checked against the latest crates.io release.

Patch releases preserve the public API. Under Cargo semantic versioning, a pre-1.0 update from
`0.x` to `0.(x + 1)` may change the API, and any changes to formal semantics are documented
separately from Rust API compatibility.

## Contributing and security

Report suspected vulnerabilities privately. The
[security policy](https://github.com/brian-c-moore/automation-structures/blob/main/SECURITY.md)
gives the reporting process, the
[contribution guide](https://github.com/brian-c-moore/automation-structures/blob/main/CONTRIBUTING.md)
lists the checks required for code changes, and
[MAINTAINER_ARCHITECTURE.md](https://github.com/brian-c-moore/automation-structures/blob/main/MAINTAINER_ARCHITECTURE.md)
maps each structure's state to its implementation.

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](https://github.com/brian-c-moore/automation-structures/blob/main/LICENSE-APACHE)
  or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
  ([LICENSE-MIT](https://github.com/brian-c-moore/automation-structures/blob/main/LICENSE-MIT)
  or <https://opensource.org/licenses/MIT>)

at your option.
