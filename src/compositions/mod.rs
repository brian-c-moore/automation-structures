// Executable modules for the Signal and RateLimit compositions and for the
// SelectThenActuate and TraversalBudgetComposition theorems. Each TLA+ action
// maps to one exclusive mutable method. Concurrent realizations must provide
// an equivalent atomic commit boundary.
//
//   signal              — Signal (named composition, Coordination family):
//                         change-detecting notification channel;
//                         PendingNotifiedDisjointness.
//   rate_limit          — RateLimit (named composition, Coordination family):
//                         per-window operation bound; WindowCountBound,
//                         WindowStartNotFuture.
//   select_then_actuate — SelectThenActuate composition theorem: argmax
//                         selection coupled with actuation;
//                         TypeInvariant, ActuationScope, WinnerOptimality,
//                         CompositionInvariant.
//   traversal_budget_composition — TraversalBudgetComposition theorem:
//                         budgeted traversal with a
//                         shared budget; TypeInvariant, CompositionInvariant
//                         (total_cost + budget_remaining = MaxBudget),
//                         AcceptedSubsetVisited.

//! Named-composition carriers and their proof relations.

/// Budget-coupled accepted-node snapshots.
pub mod allocation_snapshot;
/// Monotone-boundary bisection.
pub mod bisection;
/// Budgeted union-find equivalence classes.
pub mod equivalence_class;
/// Master and sub-pool budget federation.
pub mod federated_budget;
/// Fixed-window rate limiting.
pub mod rate_limit;
/// Ordered additive and maximum reductions.
pub mod reduction;
/// Registry-backed weighted relationship graphs.
pub mod relationship_graph;
/// Budgeted supported sampling.
pub mod sampler;
/// Selection coupled to governed actuation.
pub mod select_then_actuate;
/// Change notification with per-listener cursors.
pub mod signal;
/// Proof facade for traversal and budget coupling.
pub mod traversal_budget_composition;
/// Graph traversal assembled from shared structure owners.
pub mod traversal_engine;
