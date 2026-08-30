//! Reusable Projection connective contract.
//!
//! Projection owns agreement between a retained source relation and a derived read relation. It
//! carries no freshness, persistence, or update obligation; a materialized view supplies those.

use vstd::prelude::*;

verus! {

/// One projected membership answer agrees with its retained source.
pub open spec fn membership_consistent(projected: bool, source: bool) -> bool {
    projected == source
}

/// A projected answer that differs from its source is not a valid projection.
pub proof fn disagreement_rejected(projected: bool, source: bool)
    requires projected != source,
    ensures !membership_consistent(projected, source),
{
}

}
