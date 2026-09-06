# Maintainer architecture

These rules govern crate implementation. The public API supplies reusable state machines whose
ownership and composition rules are described here; applications choose their own architecture
and remain responsible for the deployment obligations they attach to those state machines.

## Ownership model

State the frame explicitly. Ownership depends on the trusted boundary and abstraction level as
well as the state, transitions, assumptions, and property under discussion; the same component
can own a primitive transition in one frame and perform delegated work in another.

| Term | Meaning in this crate |
| --- | --- |
| Frame | The perspective that fixes the trusted boundary, abstraction level, state, transitions, assumptions, and property under discussion |
| Contract clause | A predicate or transition consequence proved for a carrier under stated preconditions; its form comes from the structure being modeled rather than a uniform template |
| State owner | The single Rust value or protocol that has authority to change a particular invariant-bearing state within the frame |
| Obligation owner | The single principal or named protocol that has the authority, control, and evidence needed to be accountable for one framed obligation |
| Delegation | Authorization to perform work across a trust boundary; delegation alone does not create or transfer obligation ownership |
| Assurance | Evidence or a bounded statement supplied across a trust boundary by a delegate, custodian, checker, or other non-owner |
| Guarantee | A bounded commitment issued by the obligation owner from the owner's authority, assumptions, controls, and evidence |
| Ownership transfer | An explicit change of obligation owner; after transfer, the new owner can issue the guarantee and the former owner can supply assurances about its part |

Composition preserves these distinctions. For a given frame, an obligation has one owner or none;
a collaborative system can divide work into separate obligations with their own owners, but
composition alone cannot assign an owner to the combined obligation.

Checked wrappers reuse the carrier. Each catalog structure, connective state type, named
composition, and execution modality has one Rust value that owns its state; the checked public
wrapper stores that value in `inner` and calls its transitions instead of storing a second state
machine. This supports proof of the carrier contract. Accountability for a deployment obligation
still depends on the authority assigned within the deployment frame.

Derive observations from the owner. A projection reads the existing owner without storing a
second copy of its state; configuration, domain policy, and strategy parameters may sit beside
that owner, while intrinsic state stays with the structure whose contract defines its transitions.

Connective forms have two representations:

- state owners: `Cursor`, `Accumulator`, `Marker`, `Counter`, and `Buffer`;
- stateless relations: `Projection` and `OrderingPass`, plus the relation functions supplied with
  state owners.

Store connective state in its owner. When a composition needs only a relation, such as
`Projection` or `OrderingPass`, its contract calls the shared relation function without adding
mutable state or copying state that another owner already stores.

## Check and act

An observation can become stale. A check tests whether a predicate holds at the observed
state and time, but a checker without authority over the later act can provide only an assurance
about that observation, not a guarantee of the later effect.
The actor's guarantee covers the transition consequences within its own frame.

Check the allowed interference. A predicate can justify a later act while it remains stable under
the interference admitted by the claim, whether through immutable state, monotone updates that
preserve it, a fused check and commit, or a protocol that binds the observation to the act.
If interference can invalidate the predicate, the owner must prevent that change or obtain fresh,
bound evidence before committing. Identify what can change before the act, who controls those
changes, which evidence crosses the boundary, and what remains outside the carrier contract.

The checked methods enforce this locally. They combine the guard and state change where the
contract requires it, and their `bool` or `Result` reports the bounded transition outcome without
establishing that an external delegate performed a later side effect.

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

| Carrier | State and role |
| --- | --- |
| `Sequential` | one active step in an ordered sequence |
| `ForkJoin` | bounded fork, worker, barrier, and output owner |
| `StepGraph` | dependency-ordered node-state owner |
| `StreamGraph` | stream execution owner; each edge is a `Buffer` and progress is retained by `Counter` owners |
| `StreamGraphFanout` | retained fan-out verification profile using the same `Buffer` and `Counter` owners |
| `TraversalBudgetComposition` | `TraversalEngine` wrapper with no additional state and a composition theorem |
| `GovernedCommit` | bounded integration witness over `ResourceRegistry`, two `Budget` owners, `PropagationPass`, `ActuationPass`, `AuditSink`, and `Sequential` |

## Adding or changing implementation

Before adding state or a transition:

1. Identify its existing owner in this document and delegate to that owner.
2. If no owner supplies the required role, record the missing role before writing implementation
   code. Determine whether the need is a new reusable structure, a new connective form, a named
   composition, or a correction to the decomposition.
3. Route a new catalog or semantic proposal through the Automation Structures research repository.
4. Keep a facade state-free apart from its `inner` owner.
5. Update the affected known-answer executable, public API test, Verus proof, mutation control, and
   publication consumer boundary.

Document the refinement mapping. Treat a compact or fused representation as a separate refinement
task, with an explicit mapping to the structure owner and evidence that every claimed transition
and contract clause is preserved under that mapping.

## Release gate

Run `cargo crate-quality --profile release`. The crate's `.crate-quality.toml` defines the required
commands, while CI runs the Rust tests across its supported operating systems and runs the
remaining verification jobs on Linux; a release candidate must pass every check listed here.

1. Workflow and shell-script static analysis, formatting, strict Clippy, tests for all targets and
   features, doctests, strict rustdoc, and the complete public catalog example on Rust 1.95.0.
2. Public API compatibility against the latest published crates.io version.
3. Dependency advisory, license, duplicate-version, wildcard, and source policy checks from
   `deny.toml`.
4. Every known-answer executable.
5. Cargo tests and the external checked consumer against the extracted `.crate` archive, using only
   fixtures and scripts present in that archive.
6. Verus verification of `src/lib.rs` and the external proof consumer against that same extracted
   archive, again using only packaged inputs and the checksum-pinned verifier.
7. A package inventory check for metadata, required documentation, test and verification sources,
   and absence of build or verifier residue.
8. A source review confirming that checked wrappers contain one state owner and named
   compositions contain only their declared owners, configuration, and state needed to coordinate
   their transitions.
