//! Verified Rust objects for composing automation structures.
//!
//! The checked root API is intended for ordinary consumers. The catalog modules
//! retain the proof-oriented carriers used by the formal correspondence suite.
//!
//! # Example
//!
//! ```rust
//! use automation_structures::Budget;
//!
//! let mut budget = Budget::new(8);
//! assert!(budget.try_reserve(3));
//! budget.commit_reservation(3)?;
//! assert_eq!(budget.available(), 5);
//! # Ok::<(), automation_structures::BudgetError>(())
//! ```

#![deny(missing_docs)]

mod api;
mod composition_api;
#[allow(dead_code, missing_docs)]
mod compositions;
mod connective_api;
#[allow(dead_code, missing_docs)]
mod connectives;
mod execution_api;
#[allow(dead_code, missing_docs)]
mod integration;
#[allow(dead_code, missing_docs)]
mod modalities;
#[allow(dead_code, missing_docs)]
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
    RelationshipGraphError, Sampler, SamplerError, Signal, SignalBuildError, SignalError,
    TraversalBuildError, TraversalEngine, TraversalError,
};
pub use connective_api::{
    Accumulator, Buffer, Counter, Marker, projection_consistent, strictly_before,
};
pub use execution_api::{
    ForkJoin, ForkJoinBuildError, ForkJoinPhase, Sequential, SequentialBuildError, StepGraph,
    StepGraphBuildError, StepState, StreamGraph, StreamGraphBuildError, WorkerState,
};
