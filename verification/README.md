# Formal verification

Verification starts at `src/lib.rs`. With `proof-api` enabled, Verus checks the public wrappers and
their underlying state machines; the separate proof crate in `verification/downstream-verus/`
checks that the published proof modules and relations can be used by another crate built against
the extracted publication archive.

Run `run_known_answer.sh` for concrete examples. It checks formatting and applies the manifest's
Rust and Clippy policy to the 24 standalone entrypoints in `verification/known-answer/`, then runs
the 23 known-answer programs. The registry cost probe is compiled and linted; its measurement run
is separate. The runner also checks the catalog witness that exercises the carriers together.
For a focused development check, set `KNOWN_ANSWER_CASE=allocation_refusal_kat` (or another
listed entrypoint) when calling the same runner. Package qualification always runs the full set.

Check the package with `run_packaged_consumer.sh`. It builds the crates.io archive and checks its
extracted contents with tests, doctests, a documentation build that rejects warnings, known-answer
programs, the catalog example, and a separate consumer of the checked public API. Both external
Cargo and Verus consumers inherit the exact manifest lint policy for their executable bindings.
Set `PACKAGE_ALLOW_DIRTY=1` only when checking an intentionally uncommitted release candidate.

The consumer manifests are templates. The `Cargo.toml.template` filenames let Cargo include the
fixtures in the publication archive, and the preparation script creates each temporary consumer's
manifest and lockfile before the consumer is built against the extracted crate.

CI pins the verifier version. The GitHub `Formal verification` workflow downloads Verus
`0.2026.05.24.ecee80a`, checks its release archive against the pinned SHA-256 digest, verifies the
crate from its root module, and verifies the separate proof consumer against the publication archive.

For a local run on x86-64 Linux, obtain that Verus release, verify the digest recorded in
`.github/workflows/formal-verification.yml`, and run:

```text
VERUS_BIN=/path/to/verus sh verification/run_verus_gate.sh
PATH=/path/to/verus-directory:$PATH sh verification/run_packaged_verus_consumer.sh
```

The downstream proof fixture includes typed audit summaries, indexed registry storage,
fallible preparation and nondefault execution parameters. The known-answer programs cover
allocation refusal and unchanged state after rejected actions. `run_dependency_boundary.sh`
checks the extracted dependency boundary. These checks establish their recorded contracts;
an expected negative case must fail for its declared diagnostic, not for an unrelated build error.
