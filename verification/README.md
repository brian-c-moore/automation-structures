# Formal verification

The crate's proof-oriented carriers and checked public facades are assembled by
`src/verification.rs`. Known-answer sources under `verification/known-answer/` are retained for
the broader correspondence and mutation-control suite maintained by the Automation Structures
research project.

The GitHub `Formal verification` workflow downloads Verus
`0.2026.05.24.ecee80a`, checks the release archive against the pinned SHA-256 digest, and verifies
the complete crate entrypoint. The workflow file is the executable source for the exact verifier
identity and invocation.

For a local run on x86-64 Linux, obtain that exact Verus release, verify the digest recorded in
`.github/workflows/formal-verification.yml`, and run:

```text
verus src/verification.rs --crate-type=lib --triggers-mode silent --multiple-errors 24
```

The three automated layers are complementary: Verus checks the encoded state and transition
contracts, public integration tests check consumer-visible behavior, and the catalog example
checks that every advertised structure can be constructed and exercised together.
