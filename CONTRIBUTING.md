# Contributing

## Before opening a change

Propose structure or contract changes upstream. The
[Automation Structures research repository](https://github.com/brian-c-moore/automation-structures-research)
defines the catalog, structure behavior, and preserved contract clauses; changes to those definitions
need to be accepted there before they are implemented in this crate.

File crate issues here. Use this repository for changes to the published Rust API, its implementation,
tests, documentation, packaging, and automation; if a change also alters a structure or its contract,
link to the accepted research change.

See [MAINTAINER_ARCHITECTURE.md](MAINTAINER_ARCHITECTURE.md) for rules on state ownership and composition.

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

CI checks actionlint and ShellCheck downloads against pinned checksums before running them.

`Cargo.toml` declares the compiler and Clippy policy. Run Clippy explicitly: ordinary
`cargo build` does not execute it. Production failures use typed outcomes. Source and tests
must not use `unwrap` or `expect`; indexing, arithmetic and conversions need checked bounds.
A scoped lint exception must explain the applicable guard or verified contract. Keep the
exception narrow and rerun the affected source proof and public tests.

Test changes through the public API. Changes to a verified carrier or its checked facade must also
pass the formal verification workflow in [verification/README.md](verification/README.md), so update
the public API tests for each changed behavior that a downstream consumer can observe.

Patch releases must pass `cargo semver-checks check-release --all-features` against the latest
published version. The pinned GitHub workflow runs this comparison automatically.

## Pull requests

Keep changes focused. Explain which behavior or contract changed, why the change is needed, and how
you checked it; add an entry to `CHANGELOG.md` when the change affects users of the crate.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
the work by you, as defined in the Apache-2.0 license, is dual-licensed under MIT OR Apache-2.0,
without additional terms or conditions.
