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

ResourceRegistry instantiates logical keys through immutable data projections. `KeyIdentity`
projects a retained representation; `RegistryQuery` projects a borrowed probe into that same key
universe. `ByteKey` stores encoded bytes, while the one Registry entry vector remains the mapping
owner. Its generic identity actions and exact-key compatibility methods share one search,
positional removal and append path. Existing exact-key proof contracts remain intact.

Byte-slice equality is a standard-library data leaf. The named `byte_slices_equal` external-body
adapter calls safe Rust slice equality and states its content/length contract; the structural
proof assumes that contract. Native controls expose a false premise. This does not prove Rust's
comparison implementation, domain-encoding injectivity or indexed lookup cost. An arbitrary trait
implementation is not sufficient evidence that its callback contains only domain computation;
consumer admission must bind the actual implementation and account for any retained automation.

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

The proof-facing `AuditSink<O, S>` keeps the published full-history default. `S` is a sealed
physical representation: the original Vec of records or `SummaryHistory` containing Counter,
latest input and a ghost sequence. Storage appends an already-computed entry and has no domain
operator, chain carry or admission authority. The one `record_typed` body owns admission and
carry commit; legacy `record` delegates with its original contract. Typed operators are pure data
parameters, not permission to conceal an automation implementation in a trait callback.

For either representation, count equals logical history length, carry is the admitted genesis
or last result, adjacent records agree, and each result equals an admitted ordered combination.
Summary history is erased and cannot satisfy runtime evidence, replay, validation or durability.
There is no reset or counter wrap. The checked signed and nullable sum/count witnesses exercise
arithmetic refusal and distinguish consumed input count from nonnull contribution count.
The small nullable data module suppresses missing-doc lint only because the pinned verifier
emits undocumented proof accessors; its handwritten public enum and variants are documented.

`ResourceRegistry<K,V,S>` retains one `entries` field. Sealed, zero-state layout tags select its
published Vec representation or `IndexMap<ByteKey,V>`; the library's hash index is derived container
storage. Parameter-specific private layout/search supertraits prevent downstream generic-argument
implementations from substituting an indexed query or representation. Byte equality, hashing and
Borrow all use the retained byte slice. No consumer map, interner or duplicate value owner exists.

Register still removes an existing position and appends the new binding; positional Deregister
preserves all other entries' order and values. Indexed library calls supply storage/lookup/borrow
premises, while the shared Registry body proves uniqueness and exact logical transition frames.
`lookup_query_mut` lends the actual retained value, with its key and other entries fixed. The caller
can borrow an AuditSink and call its Record without taking or replacing that owner. Fallible indexed
admission reserves before invoking the same Register body and returns unconsumed data on refusal.

IndexMap 2.14.0, hashbrown 0.17.0, equivalent 1.0.2 and Rust's standard library remain explicit
algorithm/allocator relies, not proved implementations. A deliberately false library lookup passes
proof but fails native tests; it receives no structural proof-sensitivity credit. Address/capacity
continuity is tested for 100,000 updates across 64 retained summary owners. The cost witness covers
25,000 probes at 32/1,024/16,384 keys; it makes no whole-kernel or analytical-performance claim.
Schema encoding, logical group budgets/IDs, selected operator admission and stream coupling belong
to the admitting composition. No benchmark readiness or production dependency cutover follows.

OrderingPass finite arrangement uses `try_arrange_indices` and immutable `PositionOrder` data.
The connective owns the returned permutation and its domain/coverage/order/refusal contracts.
The implementation calls standard Vec reservation/range extension and slice sort, with input
position ties. Those algorithms are named data-library relies, not new automation owners.
The checked nullable signed witness does not establish arbitrary Arrow or float comparators.

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

Sequential retains its scalar data domain. Its fallible constructor reserves the existing
history; both constructors share initialization and the existing completion action. Consumers
can retain owned results in ResourceRegistry and pass admitted IDs through that modality.
General stream connections, topology and multi-channel transactions are consumer compositions
of Buffer, Budget, Counter and Marker. The library does not need every possible assembly.

PropagationPass retains one graph, snapshot, update set and round counter. `PropagationDomain<T>`
supplies membership, snapshot-only eligibility/result and executable/specification correspondence;
`ValueEq` supplies exact data equality. `try_update_node` is the shared commit and refuses without
changing state. `try_new` reserves both node-sized work arrays, and StartRound reuses them.
Copy values may be application data or admitted IDs; owned data remains in its appropriate owner.

BacktrackingTraversal retains one path, saved-value/delta ledger and visited set.
`TraversalDomain<T>` supplies pure value/delta membership, mutation, inverse and a proved inverse
law. Descent and ascent remain the single structural implementations. `try_new` reserves depth
storage. `try_reserve_visits` and `try_visit` prepare retained-entry/path-copy storage before Visit;
the consumer supplies visit-count and byte-budget policy. The default modulo-three and generic
parametric Verus claims remain distinct from eventual or exhaustive search.

These immutable domain interfaces cannot supply a second scheduler, snapshot, queue or undo
stack. The mathematical data operation is a parameter of the existing action. Neither the
Copy bound nor the absence of a mutable receiver proves arbitrary native callback purity;
verified concrete domain implementations and admitted consumer wiring carry that obligation.

RateLimit's `advance_clock_to` changes only its bounded clock. Its explicit sequence witness
refines zero or more exact Tick actions. Budget, window anchor and configuration are framed;
the method neither samples an OS clock nor supplies a timer or synchronization protocol.

Storage proofs frame all logical fields and preserve original inputs on failure. Vec capacity,
allocator behavior and IndexMap internals remain library premises. The standalone allocation
known-answer program forces the listed constructor/audit/visit allocations to fail and checks
admitted action reuse. It does not extend the earlier Buffer/Registry/arrangement allocation claims.

## Adding or changing implementation

A proposed part API must satisfy all seven checks: a concrete required behavior; an exact
mismatch in existing callable parts; responsibility local to the owner; domain-neutral semantics;
one shared implementation; a minimal interface; and a verifiable contract with decisive controls.
A missing convenience composition is insufficient. Unknown checks block that proposed change.
This is a review rule, not a proof that no composition is possible.

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
   `deny.toml`. Its only duplicate-version exceptions are the exact IndexMap 1.9.3 / Hashbrown
   0.12.3 pair required by the pinned Verus proc-macro closure. The packaged dependency-boundary
   gate rejects either old version in any runtime target and rejects every runtime duplicate.
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
