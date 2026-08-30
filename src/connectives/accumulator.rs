//! Canonical Accumulator connective relations for partial results carried between steps.

use vstd::prelude::*;

verus! {

/// The accumulated prefix and pending suffix reconstruct the complete value sequence.
pub open spec fn carries<T>(
    complete: Seq<T>,
    accumulated: Seq<T>,
    pending: Seq<T>,
) -> bool {
    complete == accumulated.add(pending)
}

/// Segments that do not reconstruct the complete sequence are not a valid accumulation.
pub proof fn mismatched_partition_rejected<T>(
    complete: Seq<T>,
    accumulated: Seq<T>,
    pending: Seq<T>,
)
    requires complete != accumulated.add(pending),
    ensures !carries(complete, accumulated, pending),
{
}

/// One step appends a value to the carried partial result.
pub open spec fn append<T>(before: Seq<T>, after: Seq<T>, value: T) -> bool {
    after == before.push(value)
}

/// An unselected step preserves the carried partial result.
pub open spec fn stutter<T>(before: Seq<T>, after: Seq<T>) -> bool {
    after == before
}

/// Appending to a pending suffix preserves its accumulated prefix.
pub proof fn append_pending<T>(prefix: Seq<T>, pending: Seq<T>, value: T)
    ensures
        prefix.add(pending).push(value) == prefix.add(pending.push(value)),
{
    Seq::push_distributes_over_add(prefix, pending, value);
}

/// Moving one pending head into the accumulator preserves the reconstructed complete sequence.
pub proof fn consume_pending_head<T>(accumulated: Seq<T>, pending: Seq<T>)
    requires pending.len() > 0,
    ensures
        accumulated.add(pending)
            == accumulated.push(pending[0]).add(pending.skip(1)),
{
    assert(pending =~= seq![pending[0]].add(pending.skip(1)));
    assert(accumulated.push(pending[0]) =~= accumulated.add(seq![pending[0]]));
    assert(accumulated.add(pending)
        =~= accumulated.push(pending[0]).add(pending.skip(1)));
}

/// Moving one head between adjacent pending segments preserves the reconstructed sequence.
pub proof fn move_pending_head<T>(
    prefix: Seq<T>,
    destination: Seq<T>,
    source: Seq<T>,
)
    requires source.len() > 0,
    ensures
        prefix.add(destination).add(source)
            == prefix.add(destination.push(source[0])).add(source.skip(1)),
{
    assert(source =~= seq![source[0]].add(source.skip(1)));
    assert(destination.push(source[0]) =~= destination.add(seq![source[0]]));
    assert(prefix.add(destination).add(source)
        =~= prefix.add(destination.push(source[0])).add(source.skip(1)));
}

/// Moving one head between adjacent pending segments preserves any pending prefix and suffix.
pub proof fn move_pending_head_with_suffix<T>(
    prefix: Seq<T>,
    destination: Seq<T>,
    source: Seq<T>,
    suffix: Seq<T>,
)
    requires source.len() > 0,
    ensures
        prefix.add(destination).add(source).add(suffix)
            == prefix
                .add(destination.push(source[0]))
                .add(source.skip(1))
                .add(suffix),
{
    move_pending_head(prefix, destination, source);
}

/// Folding the first pending segment head preserves any later pending suffix.
pub proof fn consume_pending_head_with_suffix<T>(
    accumulated: Seq<T>,
    source: Seq<T>,
    suffix: Seq<T>,
)
    requires source.len() > 0,
    ensures
        accumulated.add(source.add(suffix))
            == accumulated.push(source[0]).add(source.skip(1).add(suffix)),
{
    consume_pending_head(accumulated, source);
    assert(accumulated.add(source.add(suffix))
        =~= accumulated.add(source).add(suffix));
    assert(accumulated.push(source[0]).add(source.skip(1).add(suffix))
        =~= accumulated.push(source[0]).add(source.skip(1)).add(suffix));
}

/// Skipping a present head commutes with appending a later pending suffix.
pub proof fn skip_pending_head_with_suffix<T>(source: Seq<T>, suffix: Seq<T>)
    requires source.len() > 0,
    ensures
        source.add(suffix).skip(1) == source.skip(1).add(suffix),
{
    assert(source.add(suffix).skip(1) =~= source.skip(1).add(suffix));
}

}
