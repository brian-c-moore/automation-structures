// Executable carrier for the bounded one-source/two-sink StreamGraph fan-out
// profile. A source commit broadcasts one value to both queues. Rejected calls
// stutter, and conservation is stated independently for each branch.

use vstd::prelude::*;

verus! {

pub struct StreamGraphFanout {
    pub capacity: usize,
    pub max_inputs: usize,
    pub record_domain_size: u64,
    pub left_queue: Vec<u64>,
    pub right_queue: Vec<u64>,
    pub ingested: usize,
    pub left_emitted: usize,
    pub right_emitted: usize,
}

impl StreamGraphFanout {
    pub open spec fn values_valid(q: Seq<u64>, domain: u64) -> bool {
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] < domain
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& self.capacity > 0
        &&& self.record_domain_size > 0
        &&& Self::values_valid(self.left_queue@, self.record_domain_size)
        &&& Self::values_valid(self.right_queue@, self.record_domain_size)
        &&& self.ingested <= self.max_inputs
        &&& self.left_emitted <= self.max_inputs
        &&& self.right_emitted <= self.max_inputs
    }

    pub open spec fn backpressure_correct(&self) -> bool {
        self.left_queue@.len() <= self.capacity
            && self.right_queue@.len() <= self.capacity
    }

    pub open spec fn per_branch_conservation(&self) -> bool {
        &&& self.ingested as nat
            == self.left_queue@.len() + self.left_emitted as nat
        &&& self.ingested as nat
            == self.right_queue@.len() + self.right_emitted as nat
    }

    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.backpressure_correct()
            && self.per_branch_conservation()
    }

    pub fn valid_config(capacity: usize, record_domain_size: u64) -> (valid: bool)
        ensures valid == (capacity > 0 && record_domain_size > 0),
    {
        capacity > 0 && record_domain_size > 0
    }

    pub fn new(
        capacity: usize,
        max_inputs: usize,
        record_domain_size: u64,
    ) -> (s: StreamGraphFanout)
        requires capacity > 0, record_domain_size > 0,
        ensures
            s.capacity == capacity,
            s.max_inputs == max_inputs,
            s.record_domain_size == record_domain_size,
            s.left_queue@.len() == 0,
            s.right_queue@.len() == 0,
            s.ingested == 0,
            s.left_emitted == 0,
            s.right_emitted == 0,
            s.inv(),
    {
        StreamGraphFanout {
            capacity,
            max_inputs,
            record_domain_size,
            left_queue: Vec::new(),
            right_queue: Vec::new(),
            ingested: 0,
            left_emitted: 0,
            right_emitted: 0,
        }
    }

    pub fn source_ingest(&mut self, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (value < old(self).record_domain_size
                && old(self).ingested < old(self).max_inputs
                && old(self).left_queue@.len() < old(self).capacity
                && old(self).right_queue@.len() < old(self).capacity),
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue@ == if accepted {
                old(self).left_queue@.push(value)
            } else { old(self).left_queue@ },
            final(self).right_queue@ == if accepted {
                old(self).right_queue@.push(value)
            } else { old(self).right_queue@ },
            accepted ==> final(self).ingested == old(self).ingested + 1,
            !accepted ==> final(self).ingested == old(self).ingested,
            final(self).left_emitted == old(self).left_emitted,
            final(self).right_emitted == old(self).right_emitted,
            final(self).inv(),
    {
        if value < self.record_domain_size
            && self.ingested < self.max_inputs
            && self.left_queue.len() < self.capacity
            && self.right_queue.len() < self.capacity
        {
            let ghost old_left = self.left_queue@;
            let ghost old_right = self.right_queue@;
            self.left_queue.push(value);
            self.right_queue.push(value);
            self.ingested = self.ingested + 1;
            assert forall|i: int| 0 <= i < self.left_queue@.len()
                implies #[trigger] self.left_queue@[i] < self.record_domain_size by {
                if i < old_left.len() {
                    assert(self.left_queue@[i] == old_left[i]);
                }
            }
            assert forall|i: int| 0 <= i < self.right_queue@.len()
                implies #[trigger] self.right_queue@[i] < self.record_domain_size by {
                if i < old_right.len() {
                    assert(self.right_queue@[i] == old_right[i]);
                }
            }
            true
        } else {
            false
        }
    }

    pub fn consume_left(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).left_queue@.len() > 0),
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue@ == if accepted {
                old(self).left_queue@.subrange(1, old(self).left_queue@.len() as int)
            } else { old(self).left_queue@ },
            final(self).right_queue@ == old(self).right_queue@,
            final(self).ingested == old(self).ingested,
            accepted ==> final(self).left_emitted == old(self).left_emitted + 1,
            !accepted ==> final(self).left_emitted == old(self).left_emitted,
            final(self).right_emitted == old(self).right_emitted,
            final(self).inv(),
    {
        if self.left_queue.len() > 0 {
            let ghost old_left = self.left_queue@;
            self.left_queue.remove(0);
            self.left_emitted = self.left_emitted + 1;
            assert(self.left_queue@ =~=
                old_left.subrange(1, old_left.len() as int));
            true
        } else {
            false
        }
    }

    pub fn consume_right(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).right_queue@.len() > 0),
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue@ == old(self).left_queue@,
            final(self).right_queue@ == if accepted {
                old(self).right_queue@.subrange(1, old(self).right_queue@.len() as int)
            } else { old(self).right_queue@ },
            final(self).ingested == old(self).ingested,
            final(self).left_emitted == old(self).left_emitted,
            accepted ==> final(self).right_emitted == old(self).right_emitted + 1,
            !accepted ==> final(self).right_emitted == old(self).right_emitted,
            final(self).inv(),
    {
        if self.right_queue.len() > 0 {
            let ghost old_right = self.right_queue@;
            self.right_queue.remove(0);
            self.right_emitted = self.right_emitted + 1;
            assert(self.right_queue@ =~=
                old_right.subrange(1, old_right.len() as int));
            true
        } else {
            false
        }
    }

    pub fn terminal(&self) -> (terminal: bool)
        requires self.inv(),
        ensures terminal == (self.ingested == self.max_inputs
            && self.left_queue@.len() == 0
            && self.right_queue@.len() == 0),
    {
        self.ingested == self.max_inputs
            && self.left_queue.len() == 0
            && self.right_queue.len() == 0
    }
}

}
