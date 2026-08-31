# Formal verification

The crate's checked public facades and proof-oriented carriers are verified from the real crate
root, `src/lib.rs`, with the `proof-api` feature enabled. The separate downstream proof crate under
`verification/downstream-verus/` consumes the unpacked publication archive and confirms that the
public proof modules and relations remain usable across a crate boundary.

Known-answer sources under `verification/known-answer/` exercise every retained executable
carrier. `run_known_answer.sh` compiles and runs each standalone source, including the aggregate
catalog witness.

`run_packaged_consumer.sh` builds the crates.io archive, then runs its tests, doctest, strict
documentation build, known-answer programs, complete catalog example, and a separate checked-API
consumer from the unpacked archive. Set `PACKAGE_ALLOW_DIRTY=1` only when checking an
intentionally uncommitted release candidate.

The downstream fixtures use `Cargo.toml.template` files so Cargo includes them in the publication
archive. The preparation script materializes each temporary consumer manifest and lockfile before
the consumer is built.

The GitHub `Formal verification` workflow downloads Verus `0.2026.05.24.ecee80a`, checks the
release archive against the pinned SHA-256 digest, verifies the complete crate root, and verifies
the external proof consumer. The workflow file is the executable source for the exact verifier
identity and invocation.

For a local run on x86-64 Linux, obtain that exact Verus release, verify the digest recorded in
`.github/workflows/formal-verification.yml`, and run:

```text
VERUS_BIN=/path/to/verus sh verification/run_verus_gate.sh
PATH=/path/to/verus-directory:$PATH sh verification/run_packaged_verus_consumer.sh
```

The automated layers are complementary: Verus checks the encoded state and transition contracts,
the downstream proof crate checks cross-crate proof imports from the publication archive, public
integration tests check consumer-visible behavior, known-answer executables check concrete carrier
traces, the Cargo package consumer checks the same archive, and the catalog example constructs and
exercises the advertised public objects together.
