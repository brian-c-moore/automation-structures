// Executable carrier for the bounded one-source/two-sink StreamGraph fan-out
// profile. A source commit broadcasts one value to both queues. Rejected calls
// stutter, and conservation is stated independently for each branch.

use vstd::prelude::*;

use crate::connectives::buffer::Buffer;
use crate::connectives::counter::Counter;

verus! {

/// Retained verification profile for a source fanning out to two FIFO sinks.
pub struct StreamGraphFanout {
    /// Maximum records admitted by the source.
    pub max_inputs: usize,
    /// Exclusive upper bound of record values.
    pub record_domain_size: u64,
    /// Left-branch FIFO owner.
    pub left_queue: Buffer<u64>,
    /// Right-branch FIFO owner.
    pub right_queue: Buffer<u64>,
    /// Source-admission counter.
    pub ingested: Counter,
    /// Left-sink emission counter.
    pub left_emitted: Counter,
    /// Right-sink emission counter.
    pub right_emitted: Counter,
}

impl StreamGraphFanout {
    /// Whether every queued value lies within `domain`.
    pub open spec fn values_valid(q: Seq<u64>, domain: u64) -> bool {
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] < domain
    }

    /// Whether counters, queues, and configuration values have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.left_queue.capacity > 0
        &&& self.right_queue.capacity == self.left_queue.capacity
        &&& self.record_domain_size > 0
        &&& Self::values_valid(self.left_queue.values@, self.record_domain_size)
        &&& Self::values_valid(self.right_queue.values@, self.record_domain_size)
        &&& self.ingested.value_spec() <= self.max_inputs as nat
        &&& self.left_emitted.value_spec() <= self.max_inputs as nat
        &&& self.right_emitted.value_spec() <= self.max_inputs as nat
    }

    /// Whether either full branch prevents another broadcast.
    pub open spec fn backpressure_correct(&self) -> bool {
        self.left_queue.well_formed() && self.right_queue.well_formed()
    }

    /// Whether each branch independently conserves admitted records.
    pub open spec fn per_branch_conservation(&self) -> bool {
        &&& self.ingested.value_spec()
            == self.left_queue.values@.len() + self.left_emitted.value_spec()
        &&& self.ingested.value_spec()
            == self.right_queue.values@.len() + self.right_emitted.value_spec()
    }

    /// Whether all fan-out stream contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.backpressure_correct()
            && self.per_branch_conservation()
    }

    /// Test whether the shared queue capacity and value domain are valid.
    pub fn valid_config(capacity: usize, record_domain_size: u64) -> (valid: bool)
        ensures valid == (capacity > 0 && record_domain_size > 0),
    {
        capacity > 0 && record_domain_size > 0
    }

    /// Construct an empty valid fan-out execution.
    pub fn new(
        capacity: usize,
        max_inputs: usize,
        record_domain_size: u64,
    ) -> (s: StreamGraphFanout)
        requires capacity > 0, record_domain_size > 0,
        ensures
            s.left_queue.capacity == capacity,
            s.right_queue.capacity == capacity,
            s.max_inputs == max_inputs,
            s.record_domain_size == record_domain_size,
            s.left_queue.values@.len() == 0,
            s.right_queue.values@.len() == 0,
            s.ingested.value_spec() == 0,
            s.left_emitted.value_spec() == 0,
            s.right_emitted.value_spec() == 0,
            s.inv(),
    {
        StreamGraphFanout {
            max_inputs,
            record_domain_size,
            left_queue: Buffer::new(capacity),
            right_queue: Buffer::new(capacity),
            ingested: Counter::new(0),
            left_emitted: Counter::new(0),
            right_emitted: Counter::new(0),
        }
    }

    /// Replicate one source record into both branch queues.
    pub fn source_ingest(&mut self, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (value < old(self).record_domain_size
                && old(self).ingested.value_spec() < old(self).max_inputs as nat
                && old(self).left_queue.values@.len() < old(self).left_queue.capacity
                && old(self).right_queue.values@.len() < old(self).right_queue.capacity),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == if accepted {
                old(self).left_queue.values@.push(value)
            } else { old(self).left_queue.values@ },
            final(self).right_queue.values@ == if accepted {
                old(self).right_queue.values@.push(value)
            } else { old(self).right_queue.values@ },
            accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec() + 1,
            !accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec(),
            final(self).left_emitted.value_spec() == old(self).left_emitted.value_spec(),
            final(self).right_emitted.value_spec() == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if value < self.record_domain_size
            && self.ingested.value() < self.max_inputs as u64
            && self.left_queue.len() < self.left_queue.capacity
            && self.right_queue.len() < self.right_queue.capacity
        {
            let ghost old_left = self.left_queue.values@;
            let ghost old_right = self.right_queue.values@;
            let _left_pushed = self.left_queue.push(value);
            let _right_pushed = self.right_queue.push(value);
            let _counted = self.ingested.try_increment();
            assert(_counted);
            assert forall|i: int| 0 <= i < self.left_queue.values@.len()
                implies #[trigger] self.left_queue.values@[i] < self.record_domain_size by {
                if i < old_left.len() {
                    assert(self.left_queue.values@[i] == old_left[i]);
                }
            }
            assert forall|i: int| 0 <= i < self.right_queue.values@.len()
                implies #[trigger] self.right_queue.values@[i] < self.record_domain_size by {
                if i < old_right.len() {
                    assert(self.right_queue.values@[i] == old_right[i]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Consume one record from the left FIFO branch.
    pub fn consume_left(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).left_queue.values@.len() > 0),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == if accepted {
                old(self).left_queue.values@.subrange(1, old(self).left_queue.values@.len() as int)
            } else { old(self).left_queue.values@ },
            final(self).right_queue.values@ == old(self).right_queue.values@,
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            accepted ==> final(self).left_emitted.value_spec()
                == old(self).left_emitted.value_spec() + 1,
            !accepted ==> final(self).left_emitted.value_spec()
                == old(self).left_emitted.value_spec(),
            final(self).right_emitted.value_spec() == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if self.left_queue.len() > 0 {
            let ghost old_left = self.left_queue.values@;
            let _popped = self.left_queue.pop();
            let _counted = self.left_emitted.try_increment();
            assert(_counted);
            assert(self.left_queue.values@ =~=
                old_left.subrange(1, old_left.len() as int));
            true
        } else {
            false
        }
    }

    /// Consume one record from the right FIFO branch.
    pub fn consume_right(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).right_queue.values@.len() > 0),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == old(self).left_queue.values@,
            final(self).right_queue.values@ == if accepted {
                old(self).right_queue.values@.subrange(1, old(self).right_queue.values@.len() as int)
            } else { old(self).right_queue.values@ },
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            final(self).left_emitted.value_spec() == old(self).left_emitted.value_spec(),
            accepted ==> final(self).right_emitted.value_spec()
                == old(self).right_emitted.value_spec() + 1,
            !accepted ==> final(self).right_emitted.value_spec()
                == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if self.right_queue.len() > 0 {
            let ghost old_right = self.right_queue.values@;
            let _popped = self.right_queue.pop();
            let _counted = self.right_emitted.try_increment();
            assert(_counted);
            assert(self.right_queue.values@ =~=
                old_right.subrange(1, old_right.len() as int));
            true
        } else {
            false
        }
    }

    /// Whether bounded input was admitted and both branches are drained.
    pub fn terminal(&self) -> (terminal: bool)
        requires self.inv(),
        ensures terminal == (self.ingested.value_spec() == self.max_inputs as nat
            && self.left_queue.values@.len() == 0
            && self.right_queue.values@.len() == 0),
    {
        self.ingested.value() == self.max_inputs as u64
            && self.left_queue.len() == 0
            && self.right_queue.len() == 0
    }
}

}
