// Faithful finite-index executable carrier for ForkJoin.tla.
// State tags: 0=ready, 1=running, 2=complete. Phase tags:
// 0=fork, 1=join, 2=done.

use vstd::prelude::*;

verus! {

pub struct ForkJoin {
    pub value_domain_size: u64,
    pub wstate: Vec<u8>,
    pub wvalue: Vec<u64>,
    pub phase: u8,
    pub output_ready: bool,
    pub output_snapshot: Vec<u64>,
}

impl ForkJoin {
    pub open spec fn all_complete(&self) -> bool {
        forall|i: int| 0 <= i < self.wstate@.len()
            ==> #[trigger] self.wstate@[i] == 2
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& self.value_domain_size > 0
        &&& self.wstate@.len() == self.wvalue@.len()
        &&& self.output_snapshot@.len() == self.wvalue@.len()
        &&& self.phase <= 2
        &&& (forall|i: int| 0 <= i < self.wstate@.len()
                ==> #[trigger] self.wstate@[i] <= 2)
        &&& (forall|i: int| 0 <= i < self.wvalue@.len()
                ==> #[trigger] self.wvalue@[i] < self.value_domain_size)
        &&& (forall|i: int| 0 <= i < self.output_snapshot@.len()
                ==> #[trigger] self.output_snapshot@[i] < self.value_domain_size)
    }

    pub open spec fn barrier_completeness(&self) -> bool {
        self.output_ready ==> self.all_complete()
    }

    pub open spec fn output_consistency(&self) -> bool {
        self.output_ready ==> self.output_snapshot@ == self.wvalue@
    }

    pub open spec fn phase_ordering(&self) -> bool {
        &&& (self.phase == 1 ==> self.all_complete())
        &&& (self.phase == 2 ==> self.output_ready)
    }

    pub open spec fn ready_only_done(&self) -> bool {
        self.output_ready ==> self.phase == 2
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.barrier_completeness()
        &&& self.output_consistency()
        &&& self.phase_ordering()
        &&& self.ready_only_done()
    }

    pub fn new(workers: usize, value_domain_size: u64, initial_value: u64) -> (s: ForkJoin)
        requires
            value_domain_size > 0,
            initial_value < value_domain_size,
        ensures
            s.value_domain_size == value_domain_size,
            s.wstate@.len() == workers,
            s.wvalue@.len() == workers,
            s.output_snapshot@.len() == workers,
            forall|i: int| 0 <= i < workers ==> s.wstate@[i] == 0,
            forall|i: int| 0 <= i < workers ==> s.wvalue@[i] == initial_value,
            forall|i: int| 0 <= i < workers ==> s.output_snapshot@[i] == initial_value,
            s.phase == 0,
            !s.output_ready,
            s.inv(),
    {
        let mut wstate = Vec::new();
        let mut wvalue = Vec::new();
        let mut snapshot = Vec::new();
        let mut i = 0;
        while i < workers
            invariant
                i <= workers,
                wstate@.len() == i,
                wvalue@.len() == i,
                snapshot@.len() == i,
                forall|k: int| 0 <= k < i ==> wstate@[k] == 0,
                forall|k: int| 0 <= k < i ==> wvalue@[k] == initial_value,
                forall|k: int| 0 <= k < i ==> snapshot@[k] == initial_value,
            decreases workers - i,
        {
            wstate.push(0);
            wvalue.push(initial_value);
            snapshot.push(initial_value);
            i = i + 1;
        }
        ForkJoin {
            value_domain_size,
            wstate,
            wvalue,
            phase: 0,
            output_ready: false,
            output_snapshot: snapshot,
        }
    }

    fn all_complete_exec(&self) -> (b: bool)
        ensures b == self.all_complete(),
    {
        let mut i = 0;
        while i < self.wstate.len()
            invariant
                i <= self.wstate.len(),
                forall|k: int| 0 <= k < i ==> self.wstate@[k] == 2,
            decreases self.wstate.len() - i,
        {
            if self.wstate[i] != 2 {
                assert(!self.all_complete()) by {
                    assert(self.wstate@[i as int] != 2);
                }
                return false;
            }
            i = i + 1;
        }
        true
    }

    pub fn start_worker(&mut self, worker: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (worker < old(self).wstate@.len()
                && old(self).phase == 0 && old(self).wstate@[worker as int] == 0),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
            final(self).wstate@ == if accepted {
                old(self).wstate@.update(worker as int, 1)
            } else { old(self).wstate@ },
            final(self).inv(),
    {
        if worker < self.wstate.len() && self.phase == 0 && self.wstate[worker] == 0 {
            assert(!self.output_ready);
            self.wstate.set(worker, 1);
            assert(!self.all_complete()) by {
                assert(self.wstate@[worker as int] == 1);
            }
            true
        } else {
            false
        }
    }

    pub fn complete_worker(&mut self, worker: usize, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (worker < old(self).wstate@.len()
                && old(self).phase == 0 && old(self).wstate@[worker as int] == 1
                && value < old(self).value_domain_size),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
            final(self).wstate@ == if accepted {
                old(self).wstate@.update(worker as int, 2)
            } else { old(self).wstate@ },
            final(self).wvalue@ == if accepted {
                old(self).wvalue@.update(worker as int, value)
            } else { old(self).wvalue@ },
            final(self).inv(),
    {
        if worker < self.wstate.len() && self.phase == 0
            && self.wstate[worker] == 1 && value < self.value_domain_size
        {
            assert(!self.output_ready);
            self.wvalue.set(worker, value);
            self.wstate.set(worker, 2);
            assert forall|i: int| 0 <= i < self.wvalue@.len()
                implies #[trigger] self.wvalue@[i] < self.value_domain_size by {
                if i != worker as int {
                    assert(self.wvalue@[i] == old(self).wvalue@[i]);
                }
            }
            true
        } else {
            false
        }
    }

    pub fn barrier(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).phase == 0 && old(self).all_complete()),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
            final(self).phase == if accepted { 1 } else { old(self).phase },
            final(self).inv(),
    {
        if self.phase == 0 && self.all_complete_exec() {
            assert(!self.output_ready);
            self.phase = 1;
            true
        } else {
            false
        }
    }

    pub fn produce_output(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).phase == 1),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            if accepted {
                final(self).phase == 2
                    && final(self).output_ready
                    && final(self).output_snapshot@ == old(self).wvalue@
            } else {
                final(self).phase == old(self).phase
                    && final(self).output_ready == old(self).output_ready
                    && final(self).output_snapshot@ == old(self).output_snapshot@
            },
            final(self).inv(),
    {
        if self.phase == 1 {
            self.output_snapshot = self.wvalue.clone();
            self.output_ready = true;
            self.phase = 2;
            true
        } else {
            false
        }
    }

    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (old(self).phase == 2),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
            final(self).inv(),
    {
        self.phase == 2
    }
}

}
