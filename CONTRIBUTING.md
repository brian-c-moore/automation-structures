# Contributing

Thank you for helping improve `automation-structures`.

## Before opening a change

The catalog, structure definitions, transition semantics, and preserved contract clauses originate in
the [Automation Structures research repository](https://github.com/brian-c-moore/automation-structures-research).
Propose changes to those foundations there first. Accepted research changes flow downstream into
this Rust crate.

Use this repository for issues and pull requests concerning the published Rust API, its
implementation, tests, documentation, packaging, and automation. A change that alters the
underlying structure or contract must reference its accepted research change.

Repository implementation ownership and composition are recorded in
[MAINTAINER_ARCHITECTURE.md](MAINTAINER_ARCHITECTURE.md).

## Development checks

Use Rust 1.95.0 or newer. Before opening a pull request, run:

```text
cargo fmt --all -- --check
actionlint -no-color
shellcheck verification/*.sh
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets --all-features
cargo test --locked --doc --all-features
cargo run --locked --example catalog
sh verification/run_known_answer.sh
sh verification/run_packaged_consumer.sh
RUSTDOCFLAGS="-D warnings" cargo doc --locked --no-deps --all-features
cargo deny --all-features check
```

CI downloads checksum-pinned actionlint and ShellCheck releases before running these static
checks.

Changes to a verified carrier or its checked facade must also pass the formal verification
workflow described in [verification/README.md](verification/README.md). Add or update public API
tests for every behavior visible to a downstream consumer.

Patch releases must pass `cargo semver-checks check-release --all-features` against the latest
published version. The pinned GitHub workflow runs this comparison automatically.

## Pull requests

Keep changes focused. Explain the structural role, the behavior or obligation that changed, and
the evidence used to check it. Update `CHANGELOG.md` for a user-visible change.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
the work by you, as defined in the Apache-2.0 license, is dual-licensed under MIT OR Apache-2.0,
without additional terms or conditions.
