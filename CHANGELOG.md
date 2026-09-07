# Changelog

## 0.2.4

- Routes the root proof gate through the checksum-pinned Cargo-Verus so the locked
  data-library dependency is resolved for the same crate-root verification.

- Adds fallible storage admission to the existing Buffer, CompetitiveSelectionHard, StepGraph,
  ActuationPass, scalar Sequential, ForkJoin, FederatedBudget and phase-aware governor owners.
  Legacy and fallible constructors share initialization. Full-history AuditSink can reserve
  records without changing its logical chain, operator or lifetime ceiling.
- Reuses ForkJoin output storage and PropagationPass round arrays after admission. Allocation
  failure is injected at the new constructor, full-audit and visit-preparation sites listed in
  the standalone harness. Earlier Buffer, Registry and arrangement repairs retain their separate
  controls; allocator behavior remains a standard-library premise.
- Parameterizes the existing PropagationPass over Copy data, exact ValueEq and a pure snapshot
  operation. Undefined updates refuse unchanged. The default decrement-neighbor profile and
  its public API remain available through the same round/update actions.
- Parameterizes the existing BacktrackingTraversal over Copy auxiliary/delta data and a pure
  mutation/inverse domain with a required inverse proof. Shared descent/ascent retain token/path
  pairing and exact restoration; fallible depth/visit admission prepares storage before commit.
  The default modulo-three profile remains available. Neither generic interface establishes
  eventual convergence or exhaustive search.
- Adds bounded monotonic clock observation to RateLimit, with an explicit finite Tick-path proof.
  Repeated time accepts a stutter; regression or an out-of-range observation refuses unchanged.
- Keeps general stream topology/transactions in consumer compositions. The unpublished relocation
  of StreamGraphConnection and optional owned-value Sequential extension are excluded from this
  candidate; scalar Sequential history admission remains included.

- Adds fallible finite arrangement to the canonical OrderingPass connective, with exact position
  coverage, uniqueness and order. A verified nullable signed domain handles direction/nulls;
  original input position breaks ties. Standard range extension and slice sorting are explicit
  library premises, with separate native false-premise controls.

- Adds a sealed indexed byte-key representation to the existing ResourceRegistry. The default
  remains Vec storage; IndexedStorage uses IndexMap 2.14.0 with exact byte equality and borrowed
  probes. Register/Deregister retain one shared implementation and the original order/value frames.
- Adds direct mutable borrowing of retained values and fallible entry reservation before Register.
  A failed reservation returns the unconsumed key/value and preserves the logical mapping. IndexMap
  layout/search adapters are explicit data-library premises. Forced collisions, reservation refusal,
  per-group owner updates, false library premises and downstream sealing attempts have controls.

- Generalizes the existing proof-facing AuditSink over typed Item/Carry domain operations and
  two sealed record representations. The full-history default preserves its four public fields
  and legacy Record/validation contracts. Summary retention uses Counter, one latest input and
  proof-only history inside that same owner; both profiles execute one checked Record body.
- Adds checked signed and nullable sum/count domain witnesses. Capacity and arithmetic refusal
  preserve the complete owner. Summary retention supplies no runtime log, replay or validation;
  its lifetime ceiling allocates no per-record storage. Generic typed genesis/partial-operation
  contracts are proved directly, separately from the Nat/zero-only research model instances.

- Adds logical key identity and borrowed-query adapters to the same proof-facing Registry
  owner. `ByteKey` retains encoded bytes and compares by content; `lookup_query` borrows
  the retained value using a byte-slice probe. Equal bytes from different allocations
  replace one binding through the shared canonical removal/append actions.
- Preserves the existing exact-key API and proof contracts through checked equivalence
  delegates. Byte-schema correctness remains a consumer obligation; the indexed/fallible binding is above.
  Byte-slice comparison uses Rust's standard-library equality through an explicit trusted
  data-leaf contract; the structural proof does not verify the standard-library body.

- Removes the `Copy` requirement from the proof-facing `ResourceRegistry<K, V>` owner.
  Keys still require the existing exact `RegistryKey` equality contract. `lookup_ref`
  borrows retained values; `lookup` remains available when the value is `Copy`.
- Routes registry replacement and key removal through its existing positional
  `Deregister` action. Replacements retain backing storage and preserve the contract:
  unchanged entries retain their order and values, and the replaced key moves to the end.
  The default representation retains linear lookup; the indexed binding above shares these actions.

## 0.2.3

- Rejects zero-duration windows in the checked `RateLimit` constructor with
  `RateLimitBuildError::ZeroWindowDuration`. Previously, each acquisition reset the
  window and succeeded without advancing the clock. The proof-facing carrier retains
  its broader model domain and documents that zero duration provides no throttling.
- States the checked Bisection, TraversalEngine, Reduction, and StreamGraph profile
  limits in the selection guide: the known threshold, fixed star topology and node
  cost, additive reduction, and supported chain lengths.
- Corrects Counter's increment/decrement description and documents the
  ConvergenceGovernor parameter ceilings and corresponding error.
- States check/act safety in terms of predicate stability under admitted interference,
  with fusion and protocol binding as ways to obtain the required stability.
- Reorganizes the README around choosing and using the Rust types, with supported
  inputs, error handling, execution limits, and links to the verification details.

## 0.2.2

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

## 0.2.1

- Strengthens the contracts for proof-facing constructors, observers, transitions, and batch
  operations. They specify exact results and state changes, preserve state on rejection, and
  preserve unrelated owners' state in addition to maintaining invariants.
- Makes `Buffer` removal and `ResourceRegistry` replacement/removal preserve deterministic
  survivor order and exposes that order in their Verus contracts.
- Binds allocation capture, absent binary-search results, union results, traversal frontiers,
  signal history, soft-selection batch construction, and governed-commit recovery steps to their
  returned results and resulting state.
- Adds adversarial controls for order corruption, incomplete folds, false success, wrong-owner
  updates, history replacement, constructor substitution, tie-breaking drift, and crash/restart
  durable-state mutation.
- Expands checked-facade tests across sampler admission/rejection, traversal skipping, four-stage
  streaming, deterministic registry/buffer ordering, initial state from constructors, and
  preservation of unrelated owners' state.

## 0.2.0

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

## 0.1.1

Publishes the initial crate and applies the first dependency-automation updates.

## 0.1.0

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
