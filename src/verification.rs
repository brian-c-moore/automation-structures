//! Verification-only crate root for the Automation Structures research harness.
//!
//! Ordinary Cargo consumers compile `lib.rs`, which exposes only checked public
//! entry points. The research verifier compiles this root so carrier modules and
//! their proof contracts remain available to mutation controls and known-answer
//! checks without becoming accidental crates.io API.

pub mod api;
pub mod composition_api;
pub mod connective_api;
pub mod execution_api;
pub mod compositions;
pub mod connectives;
pub mod integration;
pub mod modalities;
pub mod primitives;
