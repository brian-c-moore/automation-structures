# Maintainer architecture

This document governs the implementation of the `automation-structures` crate. The public API
describes reusable capabilities. Applications that use the crate choose their own architecture.

## Ownership model

Each catalog structure, connective state type, named composition, and execution modality has one
claim-bearing Rust owner. Checked public types contain that owner in an `inner` field and delegate
transitions to it. They do not maintain a parallel state machine.

A projection derives an observation from an owner without storing a second copy. Configuration,
domain policy, and strategy parameters may remain beside the owners they configure. Intrinsic
state belongs to the structure whose transition contract defines it.

Connective forms have two representations:

- state owners: `Cursor`, `Accumulator`, `Marker`, `Counter`, and `Buffer`;
- stateless relations: `Projection` and `OrderingPass`, plus the relation functions supplied with
  state owners.

When a composition needs concrete connective state, it stores and calls that state owner. When it
needs only a relation, its contract calls the shared relation function.

## Primitive owners

| Structure | State owner |
| --- | --- |
| `Budget` | `src/primitives/budget.rs` |
| `QualityHierarchy` | `src/primitives/quality_hierarchy.rs` |
| `ResourceRegistry` | `src/primitives/resource_registry.rs` |
| `CompetitiveSelection` | `src/primitives/competitive_selection.rs` |
| `ActuationPass` | `src/primitives/actuation_pass.rs` |
| `PropagationPass` | `src/primitives/propagation_pass.rs` |
| `ConvergenceGovernor` | `src/primitives/convergence_governor_phase_aware.rs` |
| `AuditSink` | `src/primitives/audit_sink.rs` |
| `BacktrackingTraversal` | `src/primitives/backtracking_traversal.rs` |

The supported hard, hard-exclusive, soft, and ranked selection forms live together under the
single `CompetitiveSelection` primitive owner module.

## Connective owners

| Connective | State owner or relation |
| --- | --- |
| `Projection` | `src/connectives/projection.rs` |
| `Cursor` | `src/connectives/cursor.rs` |
| `Accumulator` | `src/connectives/accumulator.rs` |
| `Marker` | `src/connectives/marker.rs` |
| `Counter` | `src/connectives/counter.rs` |
| `Buffer` | `src/connectives/buffer.rs` |
| `OrderingPass` | `src/connectives/ordering_pass.rs` |

## Named compositions

| Composition | Reused parts and added coupling |
| --- | --- |
| `AllocationSnapshot` | `ResourceRegistry + Budget`; accepted membership and charged cost commit together |
| `FederatedBudget` | one master `Budget` plus one `Budget` per sub-pool; delegated capacity is conserved |
| `Bisection` | `Budget<Probes>` plus interval endpoints governed by the cursor relation; probes contract the threshold-containing interval |
| `EquivalenceClass` | parent and rank `ResourceRegistry` owners plus an operation `Budget`; union updates the owners atomically |
| `RateLimit` | `Budget<Operations>` plus runtime clock and window configuration; rollover releases and reallocates through `Budget` |
| `Reduction` | `AuditSink` instantiated with the reduction operation; the audit log is the consumed prefix and its carry is the result |
| `RelationshipGraph` | edge `ResourceRegistry` plus the projection relation; adjacency is derived rather than stored twice |
| `Sampler` | `ActuationPass + Budget`; selection couples one actuation with one budget allocation |
| `Signal` | `AuditSink<Value>` plus one `Cursor` per listener; pending and notified states are projections |
| `TraversalEngine` | `RelationshipGraph + Budget + Marker + Accumulator + Buffer`; public sets, counts, and remaining capacity are projections |
| `SelectThenActuate` | one hard `CompetitiveSelection` owner per seat plus one `ActuationPass`; selected allocations and applied effects share one lifecycle |

The composition owners are the files under `src/compositions/`. The checked wrappers in
`src/composition_api.rs` contain only those owners.

## Execution modalities and retained assemblies

| Carrier | Ownership disposition |
| --- | --- |
| `Sequential` | ordered single-locus execution owner |
| `ForkJoin` | bounded fork, worker, barrier, and output owner |
| `StepGraph` | dependency-ordered node-state owner |
| `StreamGraph` | stream execution owner; each edge is a `Buffer` and progress is retained by `Counter` owners |
| `StreamGraphFanout` | retained fan-out verification profile using the same `Buffer` and `Counter` owners |
| `TraversalBudgetComposition` | zero-additional-state theorem facade over `TraversalEngine` |
| `GovernedCommit` | bounded integration witness over `ResourceRegistry`, two `Budget` owners, `PropagationPass`, `ActuationPass`, `AuditSink`, and `Sequential` |

## Adding or changing implementation

Before adding claim-bearing state or a transition:

1. Identify its existing owner in this document and delegate to that owner.
2. If no owner supplies the required role, record the missing role before writing implementation
   code. Determine whether the need is a new reusable structure, a new connective form, a named
   composition, or a correction to the decomposition.
3. Route a new catalog or semantic proposal through the Automation Structures research repository.
4. Keep a facade state-free apart from its `inner` owner.
5. Update the affected known-answer executable, public API test, Verus proof, mutation control, and
   publication consumer boundary.

An optimized or fused representation is a separate refinement task. It needs an explicit mapping
to the structure owner and evidence that every claimed transition and obligation is preserved.

## Release gate

A crates.io release is ready only after the exact candidate passes all of these boundaries:

The repeatable entry point is `cargo crate-quality --profile release`; this repository's
`.crate-quality.toml` defines the required package-specific commands. The GitHub workflows run the
same underlying boundaries on hosted Linux, Windows, and macOS environments.

1. Workflow and shell-script static analysis, formatting, strict Clippy, tests for all targets and
   features, doctests, strict rustdoc, and the complete public catalog example on Rust 1.95.0.
2. Public API compatibility against the latest published crates.io version.
3. Dependency advisory, license, duplicate-version, wildcard, and source policy checks from
   `deny.toml`.
4. Every known-answer executable.
5. Cargo tests and the external checked consumer against the unpacked `.crate` archive, using only
   fixtures and scripts present in that archive.
6. Verus verification of `src/lib.rs` and the external proof consumer against that same unpacked
   archive, again using only packaged inputs and the checksum-pinned verifier.
7. A package inventory check for metadata, required documentation, test and verification sources,
   and absence of build or verifier residue.
8. A final source audit confirming that checked facades contain one state owner and named
   compositions contain only their declared owners, configuration, and genuine coupling state.
