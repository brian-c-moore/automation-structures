# Changelog

## 0.3.1

- Install Clippy and rustfmt in the known-answer and package CI jobs so standalone fixtures and packaged consumers can run their required lint and formatting checks.
- Update the pinned indexmap dependency from 2.14.0 to 2.14.2.

## 0.3.0

- Add dynamic typed candidate traversal through the existing Registry, QualityHierarchy, OrderingPass and TraversalEngine, preserving original context and payload custody.
- Enforce discovered-parent extension, stable level order, explicit storage refusal, scoped identities and closure before complete candidate publication.
- Check dynamic constructor and ordering allocation failures, original-value return, private owner boundaries and traversal/completion omissions in native and external consumers.
- Document typed resource admission and staged local effect coupling, with allocator and external target requirements for peak-memory and exactly-once recovery.
- Align dependency policy with the pinned Verus macro's exact hashbrown/indexmap versions while retaining the separate runtime-duplicate check.
- Enforce strict compiler and Clippy rules for checked access, arithmetic and conversions, typed error handling, resource cleanup and guards across await points.
- Add owning typed graph materialization with outgoing and incoming spans, authored tie order, inverse ranks and original input return on refusal.
- Return typed optional outcomes from Registry physical access and ordered removal, preserving retained mappings for invalid positions.
- Retain lossless `usize` count bounds in Sampler and StreamGraph public observations.
- Replace unwrap/expect test and documentation setup with typed error propagation while retaining the same ownership, refusal and ordering checks.
- Implement standard error formatting and propagation for arrangement refusals.
- Delegate ranked-selection cardinality to its retained membership owner through the named Reduction.
- Exercise all nine owning-adjacency storage-refusal sites and allocation-free span, rank and handle queries in the existing allocator harness.
- Export exact typed-handle identity for downstream proofs and add owning-adjacency misuse and semantic omission controls to package qualification.
- Add owned-value Reduction preparation over immutable Registry versions and the existing AuditSink prefix, with exact input return and historical version preservation.
- Check owned version lifetime, mutation, one-use commit and both decisive owner actions through native and packaged consumer controls.
- Exercise owned Reduction storage refusals and allocation-free admitted commit in the existing allocator harness.
- Clear package-specific shared-target artifacts before release checks so results bind the selected source root.
- Add an explicit unbudgeted typed allocation profile using the same membership Registry, without a route-slot quota or resource dimensions.
- Share single and batch identity, domain, custody and seal checks across budgeted and unbudgeted allocation; retain zero domain costs in the budgeted profile.
- Apply the canonical lint policy to standalone known-answer fixtures and external consumers; verify every fixture is covered and reject injected violations.
- Replace unchecked fixture access, arithmetic and count conversions with checked outcomes while preserving known-answer and mutation expectations.
- Add complete finite minimum selection through OrderingPass, Cursor and Buffer, retaining every equal minimum in authored order without a winner quota.
- Export minimum-membership proofs and check empty domains, tie completeness, comparator policies, original context return and all three storage refusals.
- Add allocation-free owned Registry removal through the existing identity search and Deregister action, returning the original payload and preserving other bindings.
- Delegate checked Registry removal to that same transfer and expose Counter generation admission without advancing it.
- Add a typed summary Signal using AuditSink, Registry-owned listener Cursors, Counter generations and a live-listener Budget.
- Check latest-value catch-up, repeated wakes, removed and foreign-scope tokens, unchanged-value and lifetime-capacity refusal, listener storage refusal and allocation-free admitted actions.
- Add a persistent typed linear StreamGraph profile using Registry payload custody, Buffer FIFO identities, slot and encoded-byte Budgets, Counter publication and Cursor receipt.
- Return original non-Copy payloads on pressure or closure, preserve queued values after producer closure, and release owner-retained charges at FIFO ownership transfer.
- Verify downstream typed stream admission and custody, both construction storage refusals, allocation-free admitted actions and repeated storage reuse.
- Add typed shared fanout through the existing two-branch StreamGraph owner, retaining one original payload and its declared encoded-byte charge until the last governed reference is consumed.
- Check all-branch publication, slow-branch pressure, scoped observations, stale-token refusal, original backing lifetime, storage refusal and allocation-free admitted consumption.
- Export the existing Buffer capacity bound for composition proofs without exposing a second queue implementation.
- Add fallible TraversalEngine storage admission and share initialization with the existing constructor.
- Reserve QualityHierarchy property and edge storage through shared initialization and export the reachable parent-to-edge correspondence needed for complete traversal proofs.
- Add finite forest discovery through the existing TraversalEngine with a checked nonbinding work account, stable parent-before-child OrderingPass, owner-projected progress and exhaustion-only sealing.

- Add whole-batch typed allocation preparation using Registry for pending identity checks and Reduction columns for dimension totals, returning every original payload on refusal or cancellation.
- Commit admitted batches through the existing single-entry Budget/Register actions without allocation, callbacks, cloning or repeated vector shifts.
- Add overflow-safe Budget previews for two projected additional charges against the unchanged resource owner.

- Add allocation-free Buffer adoption and owned FIFO transfer through the existing standard-library iterator binding, moving non-Copy values once without suffix shifts.
- Add borrowed identity queries to mutable and sealed typed allocations through the existing Registry query path, preserving payload custody without allocating probe keys.

- Return a read-only captured allocation from `capture` and add a consuming `seal` operation so accepted membership and costs cannot change after capture.
- Expose ForkJoin completion and StepGraph predecessor completion through their existing owner queries so consumers can inspect admission guards without reconstructing them.
- Add typed incremental Reduction over AuditSink summary storage so the canonical owner retains prefix counts and carried results without a separate cursor or accumulator.
- Add unique Registry insertion with duplicate refusal and unconsumed payload return, preserving the existing upsert operation.
- Add Registry-owned count, any and all queries using named Reduction and pure domain predicates, avoiding caller-owned aggregate scans.
- Add borrow-scoped Reduction preparation with unchanged cancellation and refusal, followed by a one-use summary commit without allocation or a domain callback.
- Add Buffer-owned projected-size queries using named Reduction, with exact totals and overflow refusal without changing retained contents.
- Export the existing Buffer push/refusal and pop-result guarantees through the checked facade so downstream proofs can use them.
- Centralize immutable projected-fold traversal in named Reduction and delegate Registry and Buffer queries to it, retaining the exact admitted prefix on domain refusal.
- Delegate RelationshipGraph membership and filtered incident counts to Registry-owned queries, counting distinct weighted edges separately.
- Add a borrowed authored-order adjacency view and export the checked graph's insertion, refusal and observation contracts for downstream proofs.
- Exercise sealed allocations, prepared typed Reduction and borrowed adjacency in the public catalog example.
- Add fixed-column Reduction row preparation so every capacity and domain check completes before any column Record, with unchanged refusal and cancellation and allocation-free one-use commit.
- Expose the existing nullable signed sum/count witness through the checked public catalog for typed column use.
- Delegate borrowed sum and max entry points to the existing projected Reduction, preserving their bounds and fold contracts without a separate cursor, accumulator or allocation.
- Add an unsigned maximum domain witness for typed Reduction and verify borrowed fold contracts in the external proof consumer.
- Add an immutable OrderingPass arrangement with jointly verified forward and inverse position views, reusing the existing sorting binding and canonical Cursor.
- Add typed AllocationSnapshot entry preparation over unique owned payloads and fixed scoped Budgets, with exact input return and unchanged logical charges on refusal or cancellation.
- Add a consuming typed allocation seal that fixes membership and charges while retaining the original owners.
- Export ordering and key adapters at the crate root and exercise the new profiles in the default-feature Cargo consumer.
- Accept absolute Windows drive paths in the package verification script so it can share the configured Cargo target.
- Give the shipped Cargo and Verus consumer templates explicit standalone workspace boundaries so qualification works inside a parent Cargo workspace.

## 0.2.5

- Fixes two minor typos in the README.

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
- Excludes StreamGraphConnection and the optional owned-value Sequential extension from 0.2.4;
  scalar Sequential history admission remains included.
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
