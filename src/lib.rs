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
    CapturedAllocationSnapshot, EquivalenceClass, EquivalenceClassError, FederatedBudget,
    FrozenAdjacency, RateLimit, RateLimitBuildError, RateLimitError, Reduction,
    ReductionBuildError, ReductionError, RelationshipGraph, RelationshipGraphError, Sampler,
    SamplerError, SelectThenActuate, SelectThenActuateBuildError, SelectThenActuateError, Signal,
    SignalBuildError, SignalError, TraversalBuildError, TraversalEngine, TraversalError,
};
pub use compositions::allocation_snapshot::{
    AllocationDomain, PreparedTypedAdmission, PreparedTypedBatch, RefusedTypedAdmission,
    RefusedTypedBatch, SealedTypedAllocation, TypedAllocation, TypedAllocationError,
    UnrestrictedAllocation,
};
pub use compositions::reduction::{
    IncrementalReduction, MaximumU64, OwnedReductionError, OwnedReductionOperation,
    PreparedOwnedReduction, PreparedReductionRecord, PreparedReductionRow, ReductionColumns,
    ReductionProjection, ReductionRowError, VersionedReduction,
};
pub use compositions::relationship_graph::{
    AdjacencyBuildError, AllEdges, EdgeDirection, EdgeHandleDomain, MaterializationResult,
    MaterializedAdjacency, PositionalEdgeHandles,
};
pub use compositions::signal::{
    SignalListener, SignalObservation, SignalProfileError, SummarySignal,
};
pub use compositions::traversal_engine::{
    CandidateId, CandidateTraversal, CandidateTraversalError, DiscoveredCandidates,
    DiscoveredHierarchy, RootedTraversal,
};
pub use connective_api::{
    Accumulator, Buffer, Counter, Marker, projection_consistent, strictly_before,
};
pub use connectives::buffer::{BufferSizeError, BufferSizeProjection};
pub use connectives::ordering_pass::{
    ArrangementError, IndexArrangement, PositionOrder, SignedRowOrder,
};
pub use execution_api::{
    ForkJoin, ForkJoinBuildError, ForkJoinPhase, Sequential, SequentialBuildError, StepGraph,
    StepGraphBuildError, StepState, StreamGraph, StreamGraphBuildError, WorkerState,
};
pub use modalities::stream_graph::{
    ReceivedStreamValue, TypedPublishRefusal, TypedStream, TypedStreamError,
};
pub use modalities::stream_graph_fanout::{
    FanoutBranch, FanoutObservation, FanoutObservationToken, TypedFanout, TypedFanoutError,
};

impl_public_error!(TypedFanoutError, {
    TypedFanoutError::ZeroCapacity => "Fanout branch capacity must be positive",
    TypedFanoutError::StorageUnavailable => "Fanout backing reservation failed",
    TypedFanoutError::BranchCapacity => "Fanout branch Buffer is full",
    TypedFanoutError::ByteCapacity => "Fanout retained encoded-byte Budget is exhausted",
    TypedFanoutError::SequenceExhausted => "Fanout publication identity is exhausted",
    TypedFanoutError::Closed => "Fanout producer is closed",
    TypedFanoutError::Empty => "Open fanout branch has no available observation",
    TypedFanoutError::ForeignScope => "Fanout observation belongs to another scope",
    TypedFanoutError::StaleObservation => "Fanout observation no longer identifies the branch head",
});
pub use primitives::audit_sink::{
    CheckedSignedAdd, CheckedSignedSumCount, NullableSigned, RecordRefusal, SignedSumCount,
    TypedChainOperation,
};
pub use primitives::competitive_selection::CompetitiveSelectionMinimum;
pub use primitives::resource_registry::{
    ByteKey, KeyIdentity, RegistryInsertError, RegistryKey, RegistryPredicate, RegistryQuery,
};
pub use value_eq::ValueEq;

impl_public_error!(TypedStreamError, {
    TypedStreamError::StorageUnavailable => "Stream backing reservation failed",
    TypedStreamError::SlotCapacity => "Stream retained-slot Budget is exhausted",
    TypedStreamError::ByteCapacity => "Stream retained encoded-byte Budget is exhausted",
    TypedStreamError::SequenceExhausted => "Stream FIFO identity is exhausted",
    TypedStreamError::Closed => "Stream producer is closed",
    TypedStreamError::Empty => "Open stream has no available value",
});

impl_public_error!(RegistryInsertError, {
    RegistryInsertError::DuplicateKey => "Registry key already exists",
    RegistryInsertError::StorageUnavailable => "Registry storage reservation failed",
});
impl_public_error!(SignalProfileError, {
    SignalProfileError::ListenerCapacity => "Signal live-listener Budget is exhausted",
    SignalProfileError::GenerationExhausted => "Signal generation Counter is exhausted",
    SignalProfileError::StorageUnavailable => "Signal listener storage reservation failed",
    SignalProfileError::ForeignScope => "Signal token belongs to another scope",
    SignalProfileError::UnknownListener => "Signal listener is absent or removed",
    SignalProfileError::ChangeCapacity => "Signal lifetime change ceiling is exhausted",
});
impl_public_error!(OwnedReductionError, {
    OwnedReductionError::Capacity => "Reduction record capacity is exhausted",
    OwnedReductionError::Domain => "Reduction content combination is undefined",
    OwnedReductionError::StorageUnavailable => "Reduction staging storage reservation failed",
    OwnedReductionError::VersionExhausted => "Reduction retained version representation is exhausted",
});
impl_public_error!(RecordRefusal, {
    RecordRefusal::Capacity => "Reduction record capacity is exhausted",
    RecordRefusal::Domain => "Reduction operation is undefined for this carry and item",
});
impl_public_error!(AdjacencyBuildError, {
    AdjacencyBuildError::HandleDomain => "Typed handle domain does not cover the authored edges",
    AdjacencyBuildError::NodeOffsetOverflow => "Node offset length cannot be represented",
    AdjacencyBuildError::StorageUnavailable => "Adjacency storage reservation failed",
});
impl_public_error!(ArrangementError, {
    ArrangementError::OutsideDomain => "Arrangement count exceeds the admitted comparison domain",
    ArrangementError::Allocation => "Arrangement storage reservation failed",
});
