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

pub mod allocation_snapshot;
pub mod bisection;
pub mod equivalence_class;
pub mod federated_budget;
pub mod rate_limit;
pub mod reduction;
pub mod relationship_graph;
pub mod sampler;
pub mod select_then_actuate;
pub mod signal;
pub mod traversal_budget_composition;
pub mod traversal_engine;
