//! Primitive carriers.

/// Allocation-to-effect lifecycle primitive.
pub mod actuation_pass;
/// Hash-linked audit history primitive.
pub mod audit_sink;
/// Reversible depth-first traversal primitive.
pub mod backtracking_traversal;
/// Capacity ownership primitive.
pub mod budget;
/// Hard, exclusive, soft, and ranked selection primitive family.
pub mod competitive_selection;
/// Phase-aware convergence control primitive.
pub mod convergence_governor_phase_aware;
/// Snapshot-local propagation primitive.
pub mod propagation_pass;
/// Parent-child quality hierarchy primitive.
pub mod quality_hierarchy;
/// Unique-key resource registry primitive.
pub mod resource_registry;
