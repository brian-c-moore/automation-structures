# Formal verification

Verification starts at `src/lib.rs`. With `proof-api` enabled, Verus checks the public wrappers and
their underlying state machines; the separate proof crate in `verification/downstream-verus/`
checks that the published proof modules and relations can be used by another crate built against
the extracted publication archive.

Run `run_dependency_boundary.sh` to enforce that the pinned Verus macro-only IndexMap 1.9.3 /
Hashbrown 0.12.3 pair does not enter any runtime target and that runtime dependencies have no
duplicate versions. This accompanies the two exact compiler-only exceptions in `deny.toml`.

Run `run_known_answer.sh` for concrete examples. It first runs that dependency check. It compiles and runs each standalone source in
`verification/known-answer/`, which exercises every retained executable carrier, and also runs the
catalog witness that exercises the carriers together in one program.

Check the package with `run_packaged_consumer.sh`. It builds the crates.io archive and checks its
extracted contents with tests, doctests, a documentation build that rejects warnings, known-answer
programs, the catalog example, and a separate consumer of the checked public API.
Set `PACKAGE_ALLOW_DIRTY=1` only when checking an intentionally uncommitted release candidate.

The consumer manifests are templates. The `Cargo.toml.template` filenames let Cargo include the
fixtures in the publication archive, and the preparation script creates each temporary consumer's
manifest and lockfile before the consumer is built against the extracted crate.

CI pins the verifier version. The GitHub `Formal verification` workflow downloads Verus
`0.2026.05.24.ecee80a`, checks its release archive against the pinned SHA-256 digest, verifies the
crate from its root module through the bundled Cargo-Verus, and verifies the separate proof
consumer against the publication archive. Cargo resolves the locked IndexMap data-library
dependency; its implementation remains an explicit library premise, not a verified dependency.
The gate retains its optional output-directory argument and accepts the same vendor config
as the downstream gate for offline reproduction.

For a local run on x86-64 Linux, obtain that Verus release, verify the digest recorded in
`.github/workflows/formal-verification.yml`, and run:

```text
VERUS_BIN=/path/to/verus sh verification/run_verus_gate.sh
PATH=/path/to/verus-directory:$PATH sh verification/run_packaged_verus_consumer.sh
```

The 0.2.4 local part candidate includes external non-default data domains in
`downstream-verus/src/domains.rs`. Their proofs exercise snapshot isolation, refused updates and
mutation/inverse restoration. Their native consumers also check retained backing storage.
`known-answer/allocation_refusal_kat.rs` is a standalone, single-threaded System-allocator fault
harness. Its unsafe forwarding is test-only and is not part of the library; the library continues
to forbid unsafe code. Its 16 valid-input failure cases cover CompetitiveSelectionHard, StepGraph,
ActuationPass, scalar Sequential, ForkJoin, FederatedBudget, the phase-aware governor, full AuditSink,
PropagationPass and BacktrackingTraversal (including both Visit preparation sites). It checks
original inputs/logical state and rejects array allocation during the selected admitted actions.
Buffer, Registry and arrangement retain their separately recorded allocation controls.

These checks establish the stated parametric Verus contracts and native witnesses. They do not
verify Rust's allocator, prove arbitrary native domain callbacks, extend the fixed-domain TLA+
profiles, or accept a downstream kernel composition. Version 0.2.4 remains unpublished until a
separate publication action is authorized.
