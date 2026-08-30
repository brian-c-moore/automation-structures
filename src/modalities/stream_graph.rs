// Faithful executable carrier for the specified three- and four-node StreamGraph chains.
// q1, q2, and q3 correspond exactly to the named TLA+ edge queues; q3 is
// empty for a three-node chain. Rejected calls stutter.

use vstd::prelude::*;

verus! {

pub struct StreamGraph {
    pub chain_length: usize,
    pub capacity: usize,
    pub max_inputs: usize,
    pub record_domain_size: u64,
    pub q1: Vec<u64>,
    pub q2: Vec<u64>,
    pub q3: Vec<u64>,
    pub ingested: usize,
    pub emitted: usize,
}

impl StreamGraph {
    pub open spec fn valid_config_spec(
        chain_length: usize,
        capacity: usize,
        record_domain_size: u64,
    ) -> bool {
        (chain_length == 3 || chain_length == 4)
            && capacity > 0
            && record_domain_size > 0
    }

    pub open spec fn values_valid(q: Seq<u64>, domain: u64) -> bool {
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] < domain
    }

    pub open spec fn queue_depth(&self) -> nat {
        if self.chain_length == 3 {
            self.q1@.len() + self.q2@.len()
        } else {
            self.q1@.len() + self.q2@.len() + self.q3@.len()
        }
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& Self::valid_config_spec(
            self.chain_length, self.capacity, self.record_domain_size)
        &&& Self::values_valid(self.q1@, self.record_domain_size)
        &&& Self::values_valid(self.q2@, self.record_domain_size)
        &&& Self::values_valid(self.q3@, self.record_domain_size)
        &&& (self.chain_length == 3 ==> self.q3@.len() == 0)
        &&& self.ingested <= self.max_inputs
        &&& self.emitted <= self.max_inputs
    }

    pub open spec fn backpressure_correct(&self) -> bool {
        &&& crate::connectives::buffer::buffer_bounded(self.q1@, self.capacity as nat)
        &&& crate::connectives::buffer::buffer_bounded(self.q2@, self.capacity as nat)
        &&& (self.chain_length == 4 ==>
            crate::connectives::buffer::buffer_bounded(self.q3@, self.capacity as nat))
    }

    pub open spec fn no_record_loss(&self) -> bool {
        self.ingested as nat == self.queue_depth() + self.emitted as nat
    }

    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.backpressure_correct() && self.no_record_loss()
    }

    pub fn valid_config(
        chain_length: usize,
        capacity: usize,
        record_domain_size: u64,
    ) -> (valid: bool)
        ensures valid == Self::valid_config_spec(
            chain_length, capacity, record_domain_size),
    {
        (chain_length == 3 || chain_length == 4)
            && capacity > 0
            && record_domain_size > 0
    }

    pub fn new(
        chain_length: usize,
        capacity: usize,
        max_inputs: usize,
        record_domain_size: u64,
    ) -> (s: StreamGraph)
        requires Self::valid_config_spec(chain_length, capacity, record_domain_size),
        ensures
            s.chain_length == chain_length,
            s.capacity == capacity,
            s.max_inputs == max_inputs,
            s.record_domain_size == record_domain_size,
            s.q1@.len() == 0,
            s.q2@.len() == 0,
            s.q3@.len() == 0,
            s.ingested == 0,
            s.emitted == 0,
            s.inv(),
    {
        StreamGraph {
            chain_length,
            capacity,
            max_inputs,
            record_domain_size,
            q1: Vec::new(),
            q2: Vec::new(),
            q3: Vec::new(),
            ingested: 0,
            emitted: 0,
        }
    }

    pub fn source_ingest(&mut self, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (value < old(self).record_domain_size
                && old(self).ingested < old(self).max_inputs
                && old(self).q1@.len() < old(self).capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1@ == if accepted {
                old(self).q1@.push(value)
            } else { old(self).q1@ },
            final(self).q2@ == old(self).q2@,
            final(self).q3@ == old(self).q3@,
            accepted ==> final(self).ingested == old(self).ingested + 1,
            !accepted ==> final(self).ingested == old(self).ingested,
            final(self).emitted == old(self).emitted,
            final(self).inv(),
    {
        if value < self.record_domain_size
            && self.ingested < self.max_inputs
            && self.q1.len() < self.capacity
        {
            self.q1.push(value);
            self.ingested = self.ingested + 1;
            assert forall|i: int| 0 <= i < self.q1@.len()
                implies #[trigger] self.q1@[i] < self.record_domain_size by {
                if i < old(self).q1@.len() {
                    assert(self.q1@[i] == old(self).q1@[i]);
                }
            }
            true
        } else {
            false
        }
    }

    pub fn middle2_fire(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).q1@.len() > 0
                && old(self).q2@.len() < old(self).capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1@ == if accepted {
                old(self).q1@.subrange(1, old(self).q1@.len() as int)
            } else { old(self).q1@ },
            final(self).q2@ == if accepted {
                old(self).q2@.push(old(self).q1@[0])
            } else { old(self).q2@ },
            final(self).q3@ == old(self).q3@,
            final(self).ingested == old(self).ingested,
            final(self).emitted == old(self).emitted,
            final(self).inv(),
    {
        if self.q1.len() > 0 && self.q2.len() < self.capacity {
            let ghost old_q1 = self.q1@;
            let ghost old_q2 = self.q2@;
            let value = self.q1[0];
            self.q1.remove(0);
            self.q2.push(value);
            assert(self.q1@ =~= old_q1.subrange(1, old_q1.len() as int));
            assert(self.q2@ =~= old_q2.push(old_q1[0]));
            assert forall|i: int| 0 <= i < self.q2@.len()
                implies #[trigger] self.q2@[i] < self.record_domain_size by {
                if i < old_q2.len() {
                    assert(self.q2@[i] == old_q2[i]);
                } else {
                    assert(self.q2@[i] == old_q1[0]);
                }
            }
            true
        } else {
            false
        }
    }

    pub fn middle3_fire(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).chain_length == 4
                && old(self).q2@.len() > 0
                && old(self).q3@.len() < old(self).capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1@ == old(self).q1@,
            final(self).q2@ == if accepted {
                old(self).q2@.subrange(1, old(self).q2@.len() as int)
            } else { old(self).q2@ },
            final(self).q3@ == if accepted {
                old(self).q3@.push(old(self).q2@[0])
            } else { old(self).q3@ },
            final(self).ingested == old(self).ingested,
            final(self).emitted == old(self).emitted,
            final(self).inv(),
    {
        if self.chain_length == 4 && self.q2.len() > 0
            && self.q3.len() < self.capacity
        {
            let ghost old_q2 = self.q2@;
            let ghost old_q3 = self.q3@;
            let value = self.q2[0];
            self.q2.remove(0);
            self.q3.push(value);
            assert(self.q2@ =~= old_q2.subrange(1, old_q2.len() as int));
            assert(self.q3@ =~= old_q3.push(old_q2[0]));
            assert forall|i: int| 0 <= i < self.q3@.len()
                implies #[trigger] self.q3@[i] < self.record_domain_size by {
                if i < old_q3.len() {
                    assert(self.q3@[i] == old_q3[i]);
                } else {
                    assert(self.q3@[i] == old_q2[0]);
                }
            }
            true
        } else {
            false
        }
    }

    pub fn sink_consume(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == if old(self).chain_length == 3 {
                old(self).q2@.len() > 0
            } else {
                old(self).q3@.len() > 0
            },
            final(self).chain_length == old(self).chain_length,
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1@ == old(self).q1@,
            final(self).q2@ == if accepted && old(self).chain_length == 3 {
                old(self).q2@.subrange(1, old(self).q2@.len() as int)
            } else { old(self).q2@ },
            final(self).q3@ == if accepted && old(self).chain_length == 4 {
                old(self).q3@.subrange(1, old(self).q3@.len() as int)
            } else { old(self).q3@ },
            final(self).ingested == old(self).ingested,
            accepted ==> final(self).emitted == old(self).emitted + 1,
            !accepted ==> final(self).emitted == old(self).emitted,
            final(self).inv(),
    {
        if self.chain_length == 3 {
            if self.q2.len() > 0 {
                let ghost old_q2 = self.q2@;
                self.q2.remove(0);
                self.emitted = self.emitted + 1;
                assert(self.q2@ =~= old_q2.subrange(1, old_q2.len() as int));
                true
            } else {
                false
            }
        } else {
            if self.q3.len() > 0 {
                let ghost old_q3 = self.q3@;
                self.q3.remove(0);
                self.emitted = self.emitted + 1;
                assert(self.q3@ =~= old_q3.subrange(1, old_q3.len() as int));
                true
            } else {
                false
            }
        }
    }

    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (old(self).ingested == old(self).max_inputs
                && old(self).q1@.len() == 0
                && old(self).q2@.len() == 0
                && old(self).q3@.len() == 0),
            final(self).chain_length == old(self).chain_length,
            final(self).capacity == old(self).capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1@ == old(self).q1@,
            final(self).q2@ == old(self).q2@,
            final(self).q3@ == old(self).q3@,
            final(self).ingested == old(self).ingested,
            final(self).emitted == old(self).emitted,
            final(self).inv(),
    {
        self.ingested == self.max_inputs
            && self.q1.len() == 0
            && self.q2.len() == 0
            && self.q3.len() == 0
    }
}

}
