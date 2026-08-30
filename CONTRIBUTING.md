# Contributing

Thank you for helping improve `automation-structures`.

## Before opening a change

The catalog, structure definitions, transition semantics, and preserved obligations originate in
the [Automation Structures research repository](https://github.com/brian-c-moore/automation-structures-research).
Propose changes to those foundations there first. Accepted research changes flow downstream into
this Rust crate.

Use this repository for issues and pull requests concerning the published Rust API, its
implementation, tests, documentation, packaging, and automation. A change that alters the
underlying structure or contract must reference its accepted research change.

## Development checks

Use Rust 1.95.0 or newer. Before opening a pull request, run:

```text
cargo fmt --all -- --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets --all-features
cargo test --locked --doc --all-features
cargo run --locked --example catalog
RUSTDOCFLAGS="-D warnings" cargo doc --locked --no-deps --all-features
cargo package --locked
```

Changes to a verified carrier or its checked facade must also pass the formal verification
workflow described in [verification/README.md](verification/README.md). Add or update public API
tests for every behavior visible to a downstream consumer.

## Pull requests

Keep changes focused. Explain the structural role, the behavior or obligation that changed, and
the evidence used to check it. Update `CHANGELOG.md` for a user-visible change.

By contributing, you agree that your contribution is licensed under the repository's MIT License.
