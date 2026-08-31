//! Execution-modality carriers.

/// Barriered fork-join execution.
pub mod fork_join;
/// Totally ordered sequential execution.
pub mod sequential;
/// Dependency-governed graph execution.
pub mod step_graph;
/// Bounded linear stream execution.
pub mod stream_graph;
/// Bounded fan-out stream verification profile.
pub mod stream_graph_fanout;
