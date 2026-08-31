#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::all)]

macro_rules! impl_public_error {
    ($type:ty, { $($variant:path => $message:literal),+ $(,)? }) => {
        impl core::fmt::Display for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str(match self { $($variant => $message),+ })
            }
        }

        impl std::error::Error for $type {}
    };
}

macro_rules! impl_observational_debug {
    ($type:ty, $name:literal, $($field:literal => $method:ident),+ $(,)?) => {
        impl core::fmt::Debug for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut state = formatter.debug_struct($name);
                $(state.field($field, &self.$method());)+
                state.finish()
            }
        }
    };
}

mod api;
mod composition_api;
mod connective_api;
mod execution_api;

/// Equality adapter for generic proof-facing carriers.
pub mod value_eq;

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
/// Named-composition carriers and proof relations for verified consumers.
pub mod compositions;
#[cfg(not(feature = "proof-api"))]
#[allow(dead_code)]
mod compositions;

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
/// Connective owners and relations for verified consumers.
pub mod connectives;
#[cfg(not(feature = "proof-api"))]
#[allow(dead_code)]
mod connectives;

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
/// Retained cross-structure verification assemblies.
pub mod integration;
#[cfg(not(feature = "proof-api"))]
#[allow(dead_code)]
mod integration;

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
/// Execution-modality carriers and proof relations for verified consumers.
pub mod modalities;
#[cfg(not(feature = "proof-api"))]
#[allow(dead_code)]
mod modalities;

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
/// Primitive carriers and proof relations for verified consumers.
pub mod primitives;
#[cfg(not(feature = "proof-api"))]
#[allow(dead_code)]
mod primitives;

pub use api::{
    ActuationError, ActuationPass, AuditRecord, AuditSink, BacktrackingBuildError,
    BacktrackingError, BacktrackingTraversal, Budget, BudgetError, CompetitiveSelectionError,
    CompetitiveSelectionHard, CompetitiveSelectionHardExclusive, CompetitiveSelectionRanked,
    CompetitiveSelectionSoft, ConvergenceBuildError, ConvergenceError, ConvergenceGovernor,
    ConvergencePhase, ConvergenceState, Cursor, CursorError, PropagationBuildError,
    PropagationError, PropagationPass, PropagationRound, QualityHierarchy, QualityHierarchyError,
    ResourceRegistry,
};
pub use composition_api::{
    AllocationSnapshot, AllocationSnapshotError, Bisection, BisectionBuildError, BisectionError,
    EquivalenceClass, EquivalenceClassError, FederatedBudget, RateLimit, RateLimitBuildError,
    RateLimitError, Reduction, ReductionBuildError, ReductionError, RelationshipGraph,
    RelationshipGraphError, Sampler, SamplerError, SelectThenActuate, SelectThenActuateBuildError,
    SelectThenActuateError, Signal, SignalBuildError, SignalError, TraversalBuildError,
    TraversalEngine, TraversalError,
};
pub use connective_api::{
    Accumulator, Buffer, Counter, Marker, projection_consistent, strictly_before,
};
pub use execution_api::{
    ForkJoin, ForkJoinBuildError, ForkJoinPhase, Sequential, SequentialBuildError, StepGraph,
    StepGraphBuildError, StepState, StreamGraph, StreamGraphBuildError, WorkerState,
};
