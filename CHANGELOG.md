# Changelog

All notable changes to this crate are documented here.

## 0.1.1 - Prepublication Release
- Dependabot dependency updates 

## 0.1.0 - Unreleased

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
