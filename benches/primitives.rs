//! Canonical primitive workloads: retained-state scaling and complete owner actions.
use automation_structures as a;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::{hint::black_box, time::Duration};

const SIZES: [usize; 3] = [16, 256, 4096];

fn registry(n: usize) -> Option<a::ResourceRegistry> {
    let mut owner = a::ResourceRegistry::new();
    for key in 0..n {
        let key = u64::try_from(key).ok()?;
        owner.try_insert_unique(key, key.checked_add(1)?).ok()?;
    }
    Some(owner)
}

fn hierarchy(n: usize) -> Option<a::QualityHierarchy> {
    let mut owner = a::QualityHierarchy::new(n, u64::try_from(n).ok()?);
    for node in 0..n {
        owner
            .set_node_properties(
                node,
                u64::try_from(n.checked_sub(node)?).ok()?,
                u64::try_from(node).ok()?,
            )
            .ok()?;
        if let Some(parent) = node.checked_sub(1) {
            owner.add_child(parent, node).ok()?;
        }
    }
    Some(owner)
}

fn actuate(n: usize) -> Option<bool> {
    let mut owner = a::ActuationPass::new(vec![Some(1); n]);
    for seat in 0..n {
        owner.actuate(black_box(seat)).ok()?;
    }
    owner.finish().ok()?;
    Some(owner.is_complete())
}

fn propagate(n: usize, wide: bool) -> Option<u64> {
    let mut edges = Vec::new();
    for node in 1..n {
        edges.push((if wide { 0 } else { node.checked_sub(1)? }, node));
    }
    let mut owner = a::PropagationPass::new(1, 2, edges, vec![1; n]).ok()?;
    owner.start_round().ok()?;
    for node in 0..n {
        owner.update_node(black_box(node)).ok()?;
    }
    owner.end_round().ok()?;
    Some(owner.iteration())
}

fn audit(n: usize) -> Option<a::AuditSink> {
    let mut owner = a::AuditSink::new(n);
    for value in 0..n {
        if !owner.try_record(black_box(u64::try_from(value).ok()?)) {
            return None;
        }
    }
    Some(owner)
}

fn backtrack(n: usize) -> Option<usize> {
    let mut owner = a::BacktrackingTraversal::new(2, n, 0).ok()?;
    for _ in 0..n {
        owner.descend(black_box(1), black_box(1)).ok()?;
    }
    owner.visit().ok()?;
    for _ in 0..n {
        owner.ascend().ok()?;
    }
    Some(owner.visited_count())
}

fn primitives(c: &mut Criterion) {
    // Budget state is scalar: capacity sweeps would repeat the same workload.
    let mut budget = c.benchmark_group("budget");
    let mut owner = a::Budget::new(1024);
    budget.bench_function("allocate_release", |b| {
        b.iter(|| {
            let admitted = owner.try_allocate(black_box(1));
            let released = owner.release(1);
            assert!(admitted && released.is_ok());
            black_box((admitted, released))
        })
    });
    budget.bench_function("reserve_commit_release", |b| {
        b.iter(|| {
            let admitted = owner.try_reserve(black_box(1));
            let committed = owner.commit_reservation(1);
            let released = owner.release(1);
            assert!(admitted && committed.is_ok() && released.is_ok());
            black_box((admitted, committed, released))
        })
    });
    budget.bench_function("eviction", |b| {
        b.iter(|| {
            let admitted = owner.try_allocate(black_box(1));
            let marked = owner.mark_eviction(1);
            let evicted = owner.complete_eviction(1);
            assert!(admitted && marked.is_ok() && evicted.is_ok());
            black_box((admitted, marked, evicted))
        })
    });
    assert_eq!(owner.allocated(), 0);
    budget.finish();

    let mut group = c.benchmark_group("registry");
    for n in SIZES {
        let fixture = registry(n);
        assert!(fixture.is_some(), "registry fixture");
        let Some(mut owner) = fixture else {
            return;
        };
        let Ok(missing) = u64::try_from(n) else {
            return;
        };
        let Some(last) = missing.checked_sub(1) else {
            return;
        };
        assert_eq!(owner.get(last), Some(missing));
        for (name, key) in [("hit", last), ("miss", missing)] {
            group.bench_with_input(BenchmarkId::new(name, n), &key, |b, key| {
                b.iter(|| black_box(owner.get(black_box(*key))))
            });
        }
        group.bench_with_input(BenchmarkId::new("replace", n), &last, |b, key| {
            b.iter(|| black_box(owner.insert(black_box(*key), black_box(7))))
        });
        group.bench_with_input(BenchmarkId::new("insert_remove", n), &missing, |b, key| {
            b.iter(|| {
                let inserted = owner.try_insert_unique(black_box(*key), black_box(7));
                let removed = owner.remove(*key);
                assert!(inserted.is_ok());
                assert_eq!(removed, Some(7));
                black_box((inserted, removed))
            })
        });
        assert_eq!(owner.len(), n);
    }
    group.finish();

    let mut group = c.benchmark_group("selection");
    for n in SIZES {
        let Some(last) = n.checked_sub(1) else {
            return;
        };
        let Ok(mut hard) = a::CompetitiveSelectionHard::new(n) else {
            return;
        };
        assert!(hard.update_score(last, 1).is_ok());
        assert_eq!(hard.evaluate(), last);
        group.bench_with_input(BenchmarkId::new("hard_evaluate", n), &last, |b, _| {
            b.iter(|| black_box(hard.evaluate()))
        });
        group.bench_with_input(
            BenchmarkId::new("hard_update_evaluate", n),
            &last,
            |b, last| {
                b.iter(|| {
                    let changed = hard.update_score(black_box(*last), black_box(1));
                    black_box((changed, hard.evaluate()))
                })
            },
        );
        let Some(k) = n.checked_div(2) else {
            return;
        };
        let Ok(mut ranked) = a::CompetitiveSelectionRanked::new(vec![1; n], k, 1) else {
            return;
        };
        group.bench_with_input(BenchmarkId::new("ranked_select", n), &n, |b, _| {
            b.iter(|| {
                ranked.select();
                black_box(ranked.selected_len())
            })
        });
        assert_eq!(ranked.selected_len(), k);
        group.bench_with_input(BenchmarkId::new("soft_apportion", n), &n, |b, n| {
            b.iter(|| {
                let total = u64::try_from(*n).ok().and_then(|n| n.checked_mul(2));
                let result = total
                    .and_then(|total| a::CompetitiveSelectionSoft::new(vec![1; *n], total, 1).ok());
                assert!(result.is_some(), "soft selection refused");
                black_box(result)
            })
        });
    }
    for n in [8, 32, 128] {
        let run = || {
            let mut owner = a::CompetitiveSelectionHardExclusive::new(n, n, 1).ok()?;
            for seat in 0..n {
                black_box(owner.evaluate(black_box(seat)).ok()?);
            }
            Some(owner)
        };
        assert!(run().is_some());
        group.bench_with_input(BenchmarkId::new("exclusive_all_seats", n), &n, |b, n| {
            b.iter(|| {
                black_box(n);
                let result = run();
                assert!(result.is_some(), "exclusive selection refused");
                black_box(result)
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("hierarchy");
    for n in SIZES {
        assert!(hierarchy(n).is_some());
        group.bench_with_input(BenchmarkId::new("construct_chain", n), &n, |b, n| {
            b.iter(|| {
                let result = hierarchy(black_box(*n));
                assert!(result.is_some());
                black_box(result)
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("actuation");
    for n in SIZES {
        assert_eq!(actuate(n), Some(true));
        group.bench_with_input(BenchmarkId::new("all_seats_finish", n), &n, |b, n| {
            b.iter(|| {
                let result = actuate(black_box(*n));
                assert_eq!(result, Some(true));
                black_box(result)
            })
        });
        let mut owner = a::ActuationPass::new(vec![Some(1); n]);
        for seat in 0..n {
            assert!(owner.actuate(seat).is_ok());
        }
        group.bench_with_input(BenchmarkId::new("ready_after_all_seats", n), &n, |b, _| {
            b.iter(|| black_box(owner.ready_to_finish()))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("propagation");
    for n in SIZES {
        for (name, wide) in [("chain_round", false), ("star_round", true)] {
            assert_eq!(propagate(n, wide), Some(1));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, n| {
                b.iter(|| {
                    let result = propagate(black_box(*n), wide);
                    assert_eq!(result, Some(1));
                    black_box(result)
                })
            });
        }
    }
    group.finish();

    let mut group = c.benchmark_group("convergence");
    for n in [1, 16, 256, 4096] {
        let Ok(mut owner) = a::ConvergenceGovernor::new(2, 6, n, 10) else {
            return;
        };
        for _ in 0..n {
            assert_eq!(owner.update(4), Ok(4));
        }
        group.bench_with_input(BenchmarkId::new("full_window_update", n), &n, |b, _| {
            b.iter(|| {
                let result = owner.update(black_box(4));
                assert_eq!(result, Ok(4));
                black_box(result)
            })
        });
        assert_eq!(owner.history_len(), n);
    }
    group.finish();

    let mut group = c.benchmark_group("audit");
    for n in SIZES {
        let fixture = audit(n);
        assert!(fixture.is_some(), "audit fixture");
        let Some(owner) = fixture else {
            return;
        };
        assert!(owner.validate());
        group.bench_with_input(BenchmarkId::new("append_history", n), &n, |b, n| {
            b.iter(|| {
                let result = audit(black_box(*n));
                assert!(result.is_some());
                black_box(result)
            })
        });
        group.bench_with_input(BenchmarkId::new("validate_history", n), &n, |b, _| {
            b.iter(|| black_box(owner.validate()))
        });
        group.bench_with_input(BenchmarkId::new("capacity_refusal", n), &n, |b, n| {
            b.iter_batched_ref(
                || {
                    let fixture = audit(*n);
                    assert!(fixture.is_some());
                    fixture
                },
                |owner| {
                    let result = owner.as_mut().map(|owner| owner.try_record(1));
                    assert_eq!(result, Some(false));
                    black_box(result)
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();

    let mut group = c.benchmark_group("backtracking");
    for n in SIZES {
        assert_eq!(backtrack(n), Some(1));
        group.bench_with_input(BenchmarkId::new("descend_visit_unwind", n), &n, |b, n| {
            b.iter(|| {
                let result = backtrack(black_box(*n));
                assert_eq!(result, Some(1));
                black_box(result)
            })
        });
    }
    group.finish();
}

criterion_group! { name = benches; config = Criterion::default().sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(2)); targets = primitives }
criterion_main!(benches);
