//! External Verus consumer used by the cross-crate proof API gate.

use automation_structures::connectives::{counter, ordering_pass};
use automation_structures::primitives::{budget, resource_registry};
use automation_structures::Buffer;
use vstd::prelude::*;

verus! {

/// Connective and primitive relations remain usable across the crate boundary.
pub proof fn structure_relations_are_importable()
    ensures
        counter::nonnegative(0),
        ordering_pass::strictly_before(0, 1),
        budget::budget_safety(1, 0, 0, 0),
        resource_registry::unique_keys(Seq::<u64>::empty()),
{
}

/// A downstream proof crate can instantiate the registry with a composition key.
pub fn typed_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<(usize, usize, u64), ()>)
    ensures registry.entries@.len() == 0,
{
    resource_registry::ResourceRegistry::new()
}

/// A downstream proof crate can construct and update the checked Buffer facade.
pub fn checked_buffer_is_constructible() -> (buffer: Buffer<u64>)
    ensures buffer.well_formed(), buffer.distinct(),
{
    let mut buffer = Buffer::new(2);
    let accepted = buffer.push_unique(7);
    assert(accepted);
    buffer
}

}
