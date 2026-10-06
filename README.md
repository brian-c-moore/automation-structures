# automation-structures

[![CI](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/ci.yml)
[![Formal verification](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/brian-c-moore/automation-structures/actions/workflows/formal-verification.yml)
[![crates.io](https://img.shields.io/crates/v/automation-structures.svg)](https://crates.io/crates/automation-structures)
[![docs.rs](https://docs.rs/automation-structures/badge.svg)](https://docs.rs/automation-structures)
[![license](https://img.shields.io/crates/l/automation-structures.svg)](https://github.com/brian-c-moore/automation-structures#license)

`automation-structures` is a Rust library of reusable state-machine implementations, organized
around behavioral obligations, with explicit contracts and conditions for composition.

Use a `Budget` to reserve capacity before admitting work, or a `StepGraph` to track which steps
are ready after their dependencies complete. Each type holds the relevant state and exposes
permitted transitions. The checked operations test whether a requested state change is allowed
before applying it. Compositions bind those operations to preserve the
contracts of the parts and the required agreement between them.

[Automation Structures Research](https://github.com/brian-c-moore/automation-structures-research)
explains why these abstractions were selected and records their contracts and formal evidence.
`alk-core` is being built as an automation kernel composed from this library. It uses the same
parts for its execution machinery and the components developers assemble into flows.

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
| Map unique resource identifiers to values | `ResourceRegistry` | At most one live value per key; unique insertion refuses duplicates, upsert replaces them, and owner queries count pure predicate matches |
| Retain an append-only operation chain | `AuditSink` | Entries link to their predecessors using a recomputed chain value; this type does not provide cryptographic hashing, durable storage, or tamper detection |
| Publish typed latest values to dynamic listeners | `SummarySignal<T>` | Coalesces changes under the same AuditSink head; issues generations, refuses removed/foreign-scope tokens, and bounds live listeners separately from the lifetime change ceiling; each instance requires a distinct caller-owned scope |
| Run snapshot-local graph updates | `PropagationPass` | Each node updates once per round from the same snapshot |
| Track completion after allocation | `ActuationPass` | Each allocated seat records at most one corresponding effect before closure; the application performs external effects |
| Maintain ordered parent-child quality and cost constraints | `QualityHierarchy` | Single parent plus level and cost ordering |
| Traverse choices with exact undo | `BacktrackingTraversal` | Descent records the inverse used by ascent; recorded visits are valid full-depth leaves, but need not cover every leaf |
| Select one winner, exclusive winners, weighted shares, or a ranked subset | `CompetitiveSelectionHard`, `CompetitiveSelectionHardExclusive`, `CompetitiveSelectionSoft`, `CompetitiveSelectionRanked` | Each type enforces its documented allocation and tie rules |
| Retain every equal minimum in a finite immutable domain | `CompetitiveSelectionMinimum<C>` | Uses the domain's total preorder and canonical arrangement; retains all ties in authored order, without a winner quota; reservation refusal returns the original comparator |
| Track convergence and resume after changes | `ConvergenceGovernor` | Uses a bounded delta history and explicit phases; window length and maximum delta are each limited to one billion |

### Small state helpers

These connective forms supply state or relations for compositions. Their local contracts support
the selected structure obligations; they do not add independent obligation schemas to the
research catalog.

| Need | Type or function | Behavior and limits |
| --- | --- | --- |
| Preserve monotone progress | `Cursor` | Position never regresses |
| Move values from pending to retained history | `Accumulator<T>` | Order and membership are preserved across the boundary |
| Retain bounded FIFO state | `Buffer<T>` | Enforces capacity, removes items from the head in insertion order, and sums pure size projections through Reduction with checked overflow |
| Retain a nonnegative count | `Counter` | Checked increment and decrement within the `u64` range |
| Retain a binary fact | `Marker` | Marked/unmarked state |
| Compare projected and source membership flags | `projection_consistent` | Reports whether the two supplied Boolean values agree |
| Relate two ordered passes | `strictly_before` | The first position strictly precedes the second |
| Arrange immutable positions and resolve their ranks | `IndexArrangement`, `PositionOrder`, `SignedRowOrder` | One finite sort with deterministic original-position ties; immutable forward/inverse views and foreign-position refusal |

### Combined state machines

| Need | Type | Behavior and limits |
| --- | --- | --- |
| Admit nodes while charging their costs | `AllocationSnapshot` | `ResourceRegistry + Budget`; consuming seal and capture return immutable membership and cost observations |
| Admit owned payloads with optional resource dimensions | `TypedAllocation<K,V,P>` | Unique Registry plus scoped Budgets; budgeted dimension zero charges one membership unit and other charges use domain units, including zero cost; `unbudgeted` has no quota and requires empty charges; entry or whole-batch preparation checks every guard before allocation-free commit; refusal returns all original input and seal fixes membership/costs |
| Delegate master capacity to sub-pools | `FederatedBudget` | One master `Budget` plus one `Budget` per pool |
| Model bisection around a known threshold | `Bisection` | Probe `Budget` plus interval cursor relation; the caller supplies the threshold, with no external predicate interface |
| Merge disjoint sets within an operation budget | `EquivalenceClass` | Parent/rank registries plus operation `Budget` |
| Enforce a positive-duration logical-clock window | `RateLimit` | Operation `Budget` plus caller-driven clock and window configuration; the checked constructor rejects zero duration |
| Incrementally sum an ordered `u64` input | `Reduction` | Sums values in order through `AuditSink`; at most one billion items, each at most one billion |
| Fold typed inputs as they are admitted | `IncrementalReduction<O>` | AuditSink summary storage owns the prefix count and carry; preparation checks capacity and the domain operation, and one-use commit publishes the admitted result |
| Fold unsigned maxima | `MaximumU64` with `IncrementalReduction` | Pure comparison content over the same accepted-prefix owner; supports the complete `u64` domain |
| Publish an entire typed row to fixed columns | `ReductionColumns<O>` | Registry owns the schema and each column retains its Reduction; all guards are prepared before any Record, then one-use commit updates every column without allocation or a callback; width, storage or a column refusal leaves all columns unchanged |
| Fold owned non-Copy content | `VersionedReduction` | Registry retains immutable input/result versions; named Reduction owns prefix and carried version; preparation returns the original input on refusal or cancellation, and commit performs no allocation or domain callback |
| Store weighted edges and derive adjacency | `RelationshipGraph` | Registry-owned membership and filtered incident counts; `FrozenAdjacency` borrows authored records; consuming `materialize` retains typed outgoing/incoming spans, authored ties and inverse ranks without mutable owner access; rejects self-loops |
| Select a bounded weighted sample without replacement | `Sampler` | `ActuationPass + Budget`; caller choices must be in support, but no randomness-quality claim is made |
| Notify listeners after real value changes | `Signal` | Value-change `AuditSink` plus one `Cursor` per listener |
| Traverse a star graph under a fixed-cost budget | `TraversalEngine` | `RelationshipGraph + Budget + Marker + Accumulator + Buffer`; every accepted node costs two units |
| Discover typed candidates with repeated extensions | `CandidateTraversal<C, T>` → `DiscoveredCandidates<C, T>` | Registry retains original payloads; QualityHierarchy admits children of visited parents; OrderingPass gives stable level order; TraversalEngine owns discovery; declared storage pressure refuses explicitly; completion requires closure and no unresolved registered work |
| Discover a finite refinement forest, including multiple roots and chains | `QualityHierarchy::try_traversal` → `RootedTraversal` → `DiscoveredHierarchy` | Consumes the unchanged hierarchy; OrderingPass provides stable parent-before-child order; the existing TraversalEngine owns work, visited state and progress under a checked nonbinding account; sealing requires actual frontier exhaustion |
| Select allocations and commit their effects | `SelectThenActuate` | One hard selection per seat plus one `ActuationPass` |

### Execution state

| Need | Type | Behavior and limits |
| --- | --- | --- |
| Track a fixed sequence | `Sequential` | One active step; the completed-history length equals the current position |
| Track workers behind a join barrier | `ForkJoin` | Worker lifecycle, barrier, and stable output snapshot |
| Track steps with predecessor dependencies | `StepGraph` | A step becomes ready only after its predecessors complete |
| Move bounded records through a three- or four-stage FIFO chain | `StreamGraph` | Tracks backpressure, FIFO order, and record counts; your runtime must schedule and advance the stages |
| Retain and transfer original typed values through a persistent FIFO | `TypedStream<T>` | Registry owns non-Copy payloads; Buffer owns FIFO identities; slot and caller-declared encoded-byte Budgets bound content retained here; closure preserves drainable values; receipt transfers payload custody and its further accounting to the caller |
| Share one original typed value between two FIFO branches | `TypedFanout<T>` | The existing fanout owns both branches; Registry retains one payload and reference Counter; the declared encoded-byte charge remains until both governed branches consume it; borrowed observations and scoped tokens refuse stale consumption; domain aliases and total physical memory require their own binding |

The runnable [catalog example](https://github.com/brian-c-moore/automation-structures/blob/main/examples/catalog.rs)
constructs and exercises every checked root type:

```text
cargo run --example catalog
```

## State access and errors

Prepare an owned batch before publishing any member or charge:

```rust
use automation_structures::{TypedAllocation, UnrestrictedAllocation};
fn main() -> Result<(), Box<dyn std::error::Error>> {
let mut allocation = TypedAllocation::try_new(&vec![2, 8], UnrestrictedAllocation)?;
allocation.prepare_batch(vec![
    (7u64, (vec![1u8, 2], vec![1, 2])),
    (8u64, (vec![3u8], vec![1, 1])),
])?.commit();
assert_eq!(allocation.budget(1), Some((8, 3)));
assert_eq!(allocation.seal().get(&8), Some(&vec![3u8]));
Ok(())
}
```

Batch preparation returns the complete original vector on refusal or cancellation.
It checks authored entries in order, including duplicates within the batch and
existing membership. Commit consumes the preparation without allocation or a
domain callback. Charges declare logical domain quantities; standard allocator
spare capacity is a separate physical binding.

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
automation-structures = { version = "0.3.0", features = ["proof-api"] }
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
