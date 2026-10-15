//! Current canonical composition profiles, including indexed custody and positional Signal.
use automation_structures as a;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::{hint::black_box, time::Duration};
use vstd::prelude::*;

verus! {
    struct OwnedMaximumU64;

    impl a::OwnedReductionOperation<u64> for OwnedMaximumU64 {
        type View = u64;
        open spec fn observe(&self, value: u64) -> u64 { value }
        open spec fn accepts(&self, _previous: u64, _input: u64) -> bool { true }
        open spec fn combined(&self, previous: u64, input: u64) -> u64 {
            if previous >= input { previous } else { input }
        }
        fn try_combine(&self, previous: &u64, input: &u64)
            -> (result: Result<u64, a::OwnedReductionError>)
        {
            Ok(if *previous >= *input { *previous } else { *input })
        }
    }
}

const SIZES: [usize; 3] = [16, 256, 4096];
type IndexedAllocation = a::TypedAllocation<u64, u64, a::UnrestrictedAllocation, a::IndexedStorage>;
type Workspace =
    a::connectives::buffer::Buffer<(a::NullableSigned, a::SignedSumCount), a::FifoStorage>;

fn allocation(n: usize, dimensions: usize) -> Option<a::TypedAllocation<u64, u64>> {
    let capacity = u64::try_from(n).ok()?.checked_add(1)?;
    let mut owner =
        a::TypedAllocation::try_new(&vec![capacity; dimensions], a::UnrestrictedAllocation).ok()?;
    for key in 0..n {
        let key = u64::try_from(key).ok()?;
        owner.prepare(key, key, vec![1; dimensions]).ok()?.commit();
    }
    Some(owner)
}

fn indexed_allocation(n: usize, dimensions: usize) -> Option<IndexedAllocation> {
    indexed_allocation_with_spare(n, dimensions, 1)
}

fn indexed_allocation_with_spare(
    n: usize,
    dimensions: usize,
    spare: usize,
) -> Option<IndexedAllocation> {
    let capacity = u64::try_from(n.checked_add(spare)?).ok()?;
    let mut owner =
        a::TypedAllocation::try_new_indexed(&vec![capacity; dimensions], a::UnrestrictedAllocation)
            .ok()?;
    for key in 0..n {
        let key = u64::try_from(key).ok()?;
        owner.prepare(key, key, vec![1; dimensions]).ok()?.commit();
    }
    Some(owner)
}

fn batch(n: usize, incremental: bool) -> Option<usize> {
    let capacity = u64::try_from(n).ok()?;
    let mut owner: IndexedAllocation =
        a::TypedAllocation::try_new_indexed(&vec![capacity; 2], a::UnrestrictedAllocation).ok()?;
    if incremental {
        let mut builder = owner.prepare_batch_builder(n).ok()?;
        for key in 0..n {
            let key = u64::try_from(key).ok()?;
            builder
                .try_push(black_box(key), black_box(key), vec![1, 1])
                .ok()?;
        }
        builder.finish().commit();
    } else {
        let items = (0..n)
            .map(|key| {
                let key = u64::try_from(key).ok()?;
                Some((key, (key, vec![1, 1])))
            })
            .collect::<Option<Vec<_>>>()?;
        owner.prepare_batch(items).ok()?.commit();
    }
    Some(owner.len())
}

fn signed_columns(width: usize) -> Option<a::ReductionColumns<a::CheckedSignedSumCount>> {
    a::ReductionColumns::try_new(&vec![a::CheckedSignedSumCount; width], 2).ok()
}

fn summary_signal(n: usize) -> Option<(a::SummarySignal<u64>, a::SignalListener)> {
    let mut owner = a::SummarySignal::new(1, 0, u64::try_from(n).ok()?.checked_add(1)?, 2);
    let mut last = None;
    for _ in 0..n {
        last = Some(owner.register().ok()?);
    }
    owner.set_value(1).ok()?;
    Some((owner, last?))
}

fn graph(n: usize, wide: bool) -> Option<a::RelationshipGraph> {
    let mut owner = a::RelationshipGraph::new(n.checked_add(1)?, 1);
    for node in 0..n {
        owner
            .add_edge(if wide { 0 } else { node }, node.checked_add(1)?, 1)
            .ok()?;
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
        if let Some(parent) = node.checked_sub(2) {
            owner.add_child(parent, node).ok()?;
        }
    }
    Some(owner)
}

fn rooted(n: usize) -> Option<usize> {
    let mut owner = hierarchy(n)?.try_traversal().ok()?;
    for _ in 0..n {
        black_box(owner.step()?);
    }
    Some(owner.finish().ok()?.discovery_order().len())
}

fn candidates(n: usize) -> Option<usize> {
    let mut owner = a::CandidateTraversal::try_new(0_u64, 1, n).ok()?;
    let mut parent = None;
    for node in 0..n {
        let id = owner
            .admit(
                parent,
                black_box(u64::try_from(node).ok()?),
                u64::try_from(n.checked_sub(node)?).ok()?,
                u64::try_from(node).ok()?,
            )
            .ok()?;
        if owner.step().ok()? != Some(id) {
            return None;
        }
        parent = Some(id);
    }
    owner.close();
    Some(owner.finish().ok()?.len())
}

fn classes(n: usize) -> Option<a::EquivalenceClass> {
    let mut owner = a::EquivalenceClass::new(n, u64::try_from(n).ok()?);
    let mut width = 1_usize;
    while width < n {
        let step = width.checked_mul(2)?;
        for left in (0..n).step_by(step) {
            let right = left.checked_add(width)?;
            if right < n {
                black_box(owner.union(left, right).ok()?);
            }
        }
        width = step;
    }
    Some(owner)
}

fn sample(n: usize) -> Option<usize> {
    let mut owner = a::Sampler::new(vec![1; n], n);
    for item in 0..n {
        owner.sample(black_box(item)).ok()?;
    }
    Some(owner.selected_len())
}

fn snapshot(n: usize) -> Option<a::CapturedAllocationSnapshot> {
    let n64 = u64::try_from(n).ok()?;
    let mut owner = a::AllocationSnapshot::new(n64, n64);
    for node in 0..n64 {
        owner.accept(black_box(node), 1).ok()?;
    }
    Some(owner.seal())
}

fn select_actuate(n: usize) -> Option<bool> {
    let mut owner = a::SelectThenActuate::new(n, n).ok()?;
    for seat in 0..n {
        black_box(owner.evaluate(black_box(seat)).ok()?);
        owner.actuate(seat).ok()?;
    }
    owner.finish().ok()?;
    Some(owner.is_complete())
}

fn compositions(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocation");
    for n in SIZES {
        let Ok(key) = u64::try_from(n) else {
            return;
        };
        let Some(last) = key.checked_sub(1) else {
            return;
        };
        let linear = allocation(n, 2);
        let indexed = indexed_allocation(n, 2);
        assert!(linear.is_some() && indexed.is_some());
        group.bench_with_input(BenchmarkId::new("linear_lookup", n), &last, |b, key| {
            b.iter(|| {
                black_box(
                    linear
                        .as_ref()
                        .and_then(|owner| owner.get(black_box(key)))
                        .copied(),
                )
            })
        });
        group.bench_with_input(BenchmarkId::new("indexed_lookup", n), &last, |b, key| {
            b.iter(|| {
                black_box(
                    indexed
                        .as_ref()
                        .and_then(|owner| owner.get_query(black_box(key)))
                        .copied(),
                )
            })
        });
        let mut indexed = indexed;
        group.bench_with_input(
            BenchmarkId::new("indexed_payload_update", n),
            &last,
            |b, key| {
                b.iter(|| {
                    indexed.as_mut().and_then(|owner| {
                        let value = owner.get_query_mut(black_box(key));
                        assert!(value.is_some());
                        let value = value?;
                        *value ^= black_box(1);
                        Some(black_box(*value))
                    })
                })
            },
        );
        group.bench_with_input(BenchmarkId::new("indexed_admit", n), &key, |b, key| {
            b.iter_batched_ref(
                || {
                    let fixture = indexed_allocation(n, 2);
                    assert!(fixture.is_some());
                    fixture
                },
                |owner| {
                    let owner = owner.as_mut()?;
                    let prepared = owner.prepare(black_box(*key), black_box(7), vec![1, 1]);
                    assert!(prepared.is_ok());
                    prepared.ok()?.commit();
                    Some(black_box(owner.len()))
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_with_input(BenchmarkId::new("indexed_cancel", n), &key, |b, key| {
            b.iter(|| {
                indexed.as_mut().and_then(|owner| {
                    let prepared = owner.prepare(black_box(*key), black_box(7), vec![1, 1]);
                    assert!(prepared.is_ok());
                    let returned = prepared.ok()?.cancel();
                    Some(black_box(returned.value))
                })
            })
        });
        group.bench_with_input(
            BenchmarkId::new("indexed_duplicate_refusal", n),
            &last,
            |b, key| {
                b.iter(|| {
                    let result = indexed.as_mut().and_then(|owner| {
                        owner
                            .prepare(black_box(*key), 7, vec![1, 1])
                            .err()
                            .and_then(|refused| refused.reason)
                    });
                    assert_eq!(result, Some(a::TypedAllocationError::DuplicateKey));
                    black_box(result)
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("indexed_budget_refusal", n),
            &key,
            |b, key| {
                b.iter(|| {
                    let result = indexed.as_mut().and_then(|owner| {
                        owner
                            .prepare(black_box(*key), 7, vec![1, 2])
                            .err()
                            .and_then(|refused| refused.reason)
                    });
                    assert_eq!(result, Some(a::TypedAllocationError::Capacity));
                    black_box(result)
                })
            },
        );
        for (name, incremental) in [
            ("indexed_bulk_batch", false),
            ("indexed_incremental_batch", true),
        ] {
            assert_eq!(batch(n, incremental), Some(n));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, n| {
                b.iter(|| {
                    let result = batch(black_box(*n), incremental);
                    assert_eq!(result, Some(*n));
                    black_box(result)
                })
            });
        }
        group.bench_with_input(
            BenchmarkId::new("indexed_batch_duplicate_refusal", n),
            &last,
            |b, key| {
                b.iter_batched_ref(
                    || {
                        let owner = indexed_allocation_with_spare(n, 2, n);
                        assert!(owner.is_some());
                        let owner = owner?;
                        let mut items = (0..n)
                            .map(|offset| {
                                Some((u64::try_from(n.checked_add(offset)?).ok()?, (7, vec![1, 1])))
                            })
                            .collect::<Option<Vec<_>>>()?;
                        items.last_mut()?.0 = *key;
                        Some((owner, items))
                    },
                    |fixture| {
                        let result = fixture.as_mut().and_then(|(owner, items)| {
                            owner
                                .prepare_batch(std::mem::take(items))
                                .err()
                                .and_then(|refused| refused.reason)
                        });
                        assert_eq!(result, Some(a::TypedAllocationError::DuplicateKey));
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
    }
    // Dimension count affects every charge check independently of key count.
    for dimensions in [1, 8] {
        assert!(indexed_allocation(16, dimensions).is_some());
        group.bench_with_input(
            BenchmarkId::new("indexed_admit_dimensions", dimensions),
            &dimensions,
            |b, dimensions| {
                b.iter_batched_ref(
                    || {
                        let fixture = indexed_allocation(16, *dimensions);
                        assert!(fixture.is_some());
                        fixture
                    },
                    |owner| {
                        let owner = owner.as_mut()?;
                        let prepared =
                            owner.prepare(black_box(16), black_box(7), vec![1; *dimensions]);
                        assert!(prepared.is_ok());
                        prepared.ok()?.commit();
                        Some(black_box(owner.len()))
                    },
                    BatchSize::PerIteration,
                )
            },
        );
    }
    group.finish();

    let mut group = c.benchmark_group("reduction");
    for n in SIZES {
        let run = || {
            let mut owner = a::Reduction::new(vec![1; n]).ok()?;
            for _ in 0..n {
                owner.process_next().ok()?;
            }
            Some(owner.result())
        };
        assert_eq!(run(), u64::try_from(n).ok());
        group.bench_with_input(BenchmarkId::new("sum_lifecycle", n), &n, |b, _| {
            b.iter(|| {
                let result = run();
                assert_eq!(result, u64::try_from(n).ok());
                black_box(result)
            })
        });
        let setup = || {
            let mut owner = a::IncrementalReduction::new(n.checked_add(1)?, a::CheckedSignedAdd);
            for _ in 0..n {
                if !owner.try_record(1) {
                    return None;
                }
            }
            Some(owner)
        };
        assert!(setup().is_some());
        group.bench_with_input(BenchmarkId::new("incremental_commit", n), &n, |b, _| {
            b.iter_batched_ref(
                || {
                    let fixture = setup();
                    assert!(fixture.is_some());
                    fixture
                },
                |owner| {
                    owner.as_mut().and_then(|owner| {
                        let prepared = owner.prepare(black_box(1));
                        assert!(prepared.is_ok());
                        Some(black_box(prepared.ok()?.commit()))
                    })
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_with_input(BenchmarkId::new("incremental_cancel", n), &n, |b, _| {
            let mut owner = setup();
            assert!(owner.is_some());
            b.iter(|| {
                owner.as_mut().and_then(|owner| {
                    let prepared = owner.prepare(black_box(1));
                    assert!(prepared.is_ok());
                    Some(black_box(prepared.ok()?.cancel()))
                })
            })
        });
        let versions = || {
            let mut owner = a::VersionedReduction::try_new(0_u64, n, OwnedMaximumU64).ok()?;
            for value in 1..=n {
                owner
                    .prepare(black_box(u64::try_from(value).ok()?))
                    .ok()?
                    .commit();
            }
            Some(owner)
        };
        let checked_versions = versions();
        assert!(checked_versions.is_some());
        if let Some(owner) = checked_versions {
            assert_eq!(owner.processed_len(), n);
            for version in 0..=n {
                assert_eq!(owner.version(version).copied(), u64::try_from(version).ok());
            }
        }
        group.bench_with_input(
            BenchmarkId::new("versioned_commit_history", n),
            &n,
            |b, _| {
                b.iter(|| {
                    let result = versions();
                    assert!(result.is_some());
                    black_box(result)
                })
            },
        );
    }
    let mut overflow = a::IncrementalReduction::new(2, a::CheckedSignedAdd);
    assert!(overflow.try_record(i64::MAX));
    group.bench_function("incremental_domain_refusal", |b| {
        b.iter(|| black_box(overflow.prepare(black_box(1)).is_err()))
    });
    for width in [1, 4, 16, 64] {
        let items = vec![a::NullableSigned::Value(1); width];
        let checked = signed_columns(width).and_then(|mut owner| {
            owner.prepare_row(&items).ok()?.commit();
            owner.column_result(0)
        });
        assert_eq!(checked, Some(a::SignedSumCount { sum: 1, count: 1 }));
        group.bench_with_input(
            BenchmarkId::new("sum_count_heap_row_commit", width),
            &width,
            |b, _| {
                b.iter_batched_ref(
                    || {
                        let fixture = signed_columns(width).and_then(|mut owner| {
                            owner.prepare_row(&items).ok()?.commit();
                            Some(owner)
                        });
                        assert!(fixture.is_some());
                        fixture
                    },
                    |owner| {
                        let owner = owner.as_mut()?;
                        let prepared = owner.prepare_row(black_box(&items));
                        assert!(prepared.is_ok());
                        prepared.ok()?.commit();
                        let result = owner.column_result(0);
                        assert_eq!(result, Some(a::SignedSumCount { sum: 2, count: 2 }));
                        result.map(black_box)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        group.bench_with_input(
            BenchmarkId::new("sum_count_reusable_fifo_row_commit", width),
            &width,
            |b, _| {
                b.iter_batched_ref(
                    || {
                        let fixture = signed_columns(width);
                        assert!(fixture.is_some());
                        let mut owner = fixture?;
                        let workspace = Workspace::try_with_storage(width);
                        assert!(workspace.is_ok());
                        let mut workspace = workspace.ok()?;
                        let prepared = owner.prepare_row_in(&items, &mut workspace);
                        assert!(prepared.is_ok());
                        prepared.ok()?.commit();
                        Some((owner, workspace))
                    },
                    |fixture| {
                        let (owner, workspace) = fixture.as_mut()?;
                        // Setup committed one row; this preparation drains/reuses its workspace.
                        let prepared = owner.prepare_row_in(black_box(&items), workspace);
                        assert!(prepared.is_ok());
                        prepared.ok()?.commit();
                        let result = owner.column_result(0);
                        assert_eq!(result, Some(a::SignedSumCount { sum: 2, count: 2 }));
                        result.map(black_box)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        let mut owner = signed_columns(width);
        assert!(owner.is_some());
        group.bench_with_input(
            BenchmarkId::new("sum_count_row_cancel", width),
            &width,
            |b, _| {
                b.iter(|| {
                    let owner = owner.as_mut()?;
                    let prepared = owner.prepare_row(black_box(&items));
                    assert!(prepared.is_ok());
                    prepared.ok()?.cancel();
                    Some(black_box(owner.processed_len()))
                })
            },
        );
        let wrong = Vec::new();
        group.bench_with_input(
            BenchmarkId::new("row_width_refusal", width),
            &width,
            |b, _| {
                b.iter(|| {
                    let result = owner
                        .as_mut()
                        .map(|owner| owner.prepare_row(black_box(&wrong)).is_err());
                    assert_eq!(result, Some(true));
                    black_box(result)
                })
            },
        );
    }
    group.finish();

    let mut group = c.benchmark_group("signal");
    for n in SIZES {
        let Some(position) = n.checked_sub(1) else {
            return;
        };
        let fixture = summary_signal(n);
        assert!(fixture.is_some());
        assert!(
            fixture
                .as_ref()
                .is_some_and(|(owner, token)| owner.pending(*token) == Ok(true)
                    && owner.pending_at(*token, position) == Ok(true))
        );
        group.bench_with_input(BenchmarkId::new("summary_pending_token", n), &n, |b, _| {
            b.iter(|| black_box(fixture.as_ref().map(|(owner, token)| owner.pending(*token))))
        });
        group.bench_with_input(
            BenchmarkId::new("summary_pending_position", n),
            &position,
            |b, position| {
                b.iter(|| {
                    black_box(
                        fixture
                            .as_ref()
                            .map(|(owner, token)| owner.pending_at(*token, black_box(*position))),
                    )
                })
            },
        );
        group.bench_with_input(BenchmarkId::new("summary_notify_token", n), &n, |b, _| {
            b.iter_batched_ref(
                || summary_signal(n),
                |fixture| {
                    let result = fixture.as_mut().map(|(owner, token)| owner.notify(*token));
                    assert!(result.as_ref().is_some_and(|result| {
                        result.as_ref().is_ok_and(|observed| observed.changed)
                    }));
                    black_box(result)
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_with_input(
            BenchmarkId::new("summary_notify_position", n),
            &position,
            |b, position| {
                b.iter_batched_ref(
                    || summary_signal(n),
                    |fixture| {
                        let result = fixture
                            .as_mut()
                            .map(|(owner, token)| owner.notify_at(*token, black_box(*position)));
                        assert!(result.as_ref().is_some_and(|result| {
                            result.as_ref().is_ok_and(|observed| observed.changed)
                        }));
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("summary_publish", n), &n, |b, _| {
            b.iter_batched_ref(
                || summary_signal(n),
                |fixture| {
                    let result = fixture
                        .as_mut()
                        .map(|(owner, _)| owner.set_value(black_box(2)));
                    assert_eq!(result, Some(Ok(true)));
                    black_box(result)
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_with_input(
            BenchmarkId::new("summary_register_remove", n),
            &n,
            |b, _| {
                b.iter_batched_ref(
                    || summary_signal(n),
                    |fixture| {
                        let result = fixture.as_mut().and_then(|(owner, _)| {
                            let token = owner.register().ok()?;
                            owner.remove(token).ok()?;
                            Some(owner.listener_count())
                        });
                        assert!(result.is_some());
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        let historical = || {
            let mut owner = a::Signal::new(0, 2, n).ok()?;
            owner.set_value(1).ok()?;
            for listener in 0..n {
                owner.notify(black_box(listener)).ok()?;
            }
            Some(owner.value())
        };
        assert_eq!(historical(), Some(1));
        group.bench_with_input(
            BenchmarkId::new("retained_history_notify_all", n),
            &n,
            |b, _| {
                b.iter(|| {
                    let result = historical();
                    assert_eq!(result, Some(1));
                    black_box(result)
                })
            },
        );
    }
    group.finish();

    let mut group = c.benchmark_group("relationship");
    for n in SIZES {
        for (name, wide) in [("materialize_chain", false), ("materialize_star", true)] {
            let build = || {
                graph(n, wide)?
                    .materialize(a::PositionalEdgeHandles { count: n }, a::AllEdges)
                    .ok()
            };
            assert_eq!(build().map(|owner| owner.edge_count()), Some(n));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
                b.iter(|| {
                    let result = build();
                    assert!(result.is_some());
                    black_box(result)
                })
            });
        }
        let adjacency = graph(n, true).and_then(|graph| {
            graph
                .materialize(a::PositionalEdgeHandles { count: n }, a::AllEdges)
                .ok()
        });
        assert!(adjacency.is_some());
        group.bench_with_input(BenchmarkId::new("incident_wide_span", n), &n, |b, _| {
            b.iter(|| {
                black_box(
                    adjacency
                        .as_ref()
                        .and_then(|owner| owner.incident(black_box(0), a::EdgeDirection::Outgoing))
                        .map(<[usize]>::len),
                )
            })
        });
        let Some(last) = n.checked_sub(1) else {
            return;
        };
        group.bench_with_input(BenchmarkId::new("inverse_rank", n), &last, |b, handle| {
            b.iter(|| {
                black_box(
                    adjacency.as_ref().and_then(|owner| {
                        owner.rank_of(black_box(handle), a::EdgeDirection::Outgoing)
                    }),
                )
            })
        });
        let mut owner = graph(n, false);
        assert!(owner.is_some());
        group.bench_with_input(BenchmarkId::new("edge_add_remove", n), &n, |b, n| {
            b.iter(|| {
                let owner = owner.as_mut()?;
                let result = owner.add_edge(black_box(*n), black_box(0), 1);
                assert_eq!(result, Ok(true));
                let admitted = result.ok()?;
                owner.remove_edges(*n, 0);
                Some(black_box(admitted))
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("traversal");
    for n in SIZES {
        assert_eq!(rooted(n), Some(n));
        assert_eq!(candidates(n), Some(n));
        group.bench_with_input(
            BenchmarkId::new("rooted_forest_discovery", n),
            &n,
            |b, n| {
                b.iter(|| {
                    let result = rooted(black_box(*n));
                    assert_eq!(result, Some(*n));
                    black_box(result)
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("candidate_chain_admit_discover", n),
            &n,
            |b, n| {
                b.iter(|| {
                    let result = candidates(black_box(*n));
                    assert_eq!(result, Some(*n));
                    black_box(result)
                })
            },
        );
        for (name, visit) in [("budgeted_visit_star", true), ("budgeted_skip_star", false)] {
            let run = || {
                let mut owner =
                    a::TraversalEngine::new(n, 0, u64::try_from(n).ok()?.checked_mul(2)?).ok()?;
                owner.visit(0).ok()?;
                for node in 1..n {
                    if visit {
                        owner.visit(black_box(node)).ok()?;
                    } else {
                        owner.skip(black_box(node)).ok()?;
                    }
                }
                owner.terminate().ok()?;
                Some(owner.accepted_len())
            };
            assert_eq!(run(), Some(if visit { n } else { 1 }));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
                b.iter(|| {
                    let result = run();
                    assert_eq!(result, Some(if visit { n } else { 1 }));
                    black_box(result)
                })
            });
        }
    }
    group.finish();

    let mut group = c.benchmark_group("ordering");
    for n in SIZES {
        let Ok(n64) = i64::try_from(n) else {
            return;
        };
        for (name, values) in [
            (
                "reverse",
                (0..n64)
                    .rev()
                    .map(a::NullableSigned::Value)
                    .collect::<Vec<_>>(),
            ),
            ("ties", vec![a::NullableSigned::Value(1); n]),
        ] {
            let order = a::SignedRowOrder {
                values: &values,
                descending: false,
                nulls_first: false,
            };
            group.bench_with_input(
                BenchmarkId::new(format!("arrange_{name}"), n),
                &n,
                |b, n| {
                    b.iter(|| {
                        let result = a::IndexArrangement::try_new(black_box(*n), black_box(&order));
                        assert!(result.is_ok());
                        black_box(result)
                    })
                },
            );
            group.bench_with_input(
                BenchmarkId::new(format!("minimum_{name}"), n),
                &n,
                |b, _| {
                    b.iter(|| {
                        let result = a::CompetitiveSelectionMinimum::try_new(a::SignedRowOrder {
                            values: &values,
                            descending: false,
                            nulls_first: false,
                        });
                        assert!(result.is_ok());
                        black_box(result)
                    })
                },
            );
        }
    }
    group.finish();

    let mut group = c.benchmark_group("bounded_compositions");
    for n in SIZES {
        let Ok(n64) = u64::try_from(n) else {
            return;
        };
        let Some(pivot) = n64.checked_div(2) else {
            return;
        };
        group.bench_with_input(BenchmarkId::new("bisection_converge", n), &n, |b, _| {
            b.iter(|| {
                let result = a::Bisection::new(n64, pivot);
                assert!(result.is_ok());
                let mut owner = result.ok()?;
                owner.converge();
                assert!(owner.is_converged());
                Some(black_box(owner.probes_taken()))
            })
        });
        assert!(classes(n).is_some());
        group.bench_with_input(BenchmarkId::new("equivalence_union_tree", n), &n, |b, n| {
            b.iter(|| {
                let result = classes(black_box(*n));
                assert!(result.is_some());
                black_box(result)
            })
        });
        let owner = classes(n);
        let Some(last) = n.checked_sub(1) else {
            return;
        };
        group.bench_with_input(BenchmarkId::new("equivalence_find", n), &last, |b, node| {
            b.iter(|| {
                black_box(
                    owner
                        .as_ref()
                        .and_then(|owner| owner.representative(black_box(*node)).ok()),
                )
            })
        });
        let mut federation = a::FederatedBudget::new(n64, n);
        for pool in 0..n {
            assert!(federation.try_delegate(pool, 1));
        }
        group.bench_with_input(
            BenchmarkId::new("federated_allocate_release", n),
            &last,
            |b, pool| {
                b.iter(|| {
                    let admitted = federation.try_allocate(black_box(*pool), 1);
                    let released = federation.try_release(*pool, 1);
                    assert!(admitted && released);
                    black_box((admitted, released))
                })
            },
        );
        assert_eq!(sample(n), Some(n));
        assert_eq!(snapshot(n).map(|owner| owner.total_cost()), Some(n64));
        group.bench_with_input(BenchmarkId::new("sampler_complete", n), &n, |b, n| {
            b.iter(|| {
                let result = sample(black_box(*n));
                assert_eq!(result, Some(*n));
                black_box(result)
            })
        });
        group.bench_with_input(BenchmarkId::new("snapshot_admit_seal", n), &n, |b, n| {
            b.iter(|| {
                let result = snapshot(black_box(*n));
                assert!(result.is_some());
                black_box(result)
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("select_then_actuate");
    for n in [8, 32, 128] {
        assert_eq!(select_actuate(n), Some(true));
        group.bench_with_input(BenchmarkId::new("all_seats_lifecycle", n), &n, |b, n| {
            b.iter(|| {
                let result = select_actuate(black_box(*n));
                assert_eq!(result, Some(true));
                black_box(result)
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("rate_limit");
    let setup = || {
        let mut owner = a::RateLimit::new(16, 1, 2).ok()?;
        for _ in 0..16 {
            if !owner.try_acquire() {
                return None;
            }
        }
        Some(owner)
    };
    assert!(setup().is_some());
    let mut full = setup();
    group.bench_function("full_window_refusal", |b| {
        b.iter(|| {
            let result = full.as_mut().map(a::RateLimit::try_acquire);
            assert_eq!(result, Some(false));
            black_box(result)
        })
    });
    group.bench_function("rollover_then_acquire", |b| {
        b.iter_batched_ref(
            setup,
            |owner| {
                let result = owner.as_mut().and_then(|owner| {
                    owner.tick().ok()?;
                    Some(owner.try_acquire())
                });
                assert_eq!(result, Some(true));
                black_box(result)
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

criterion_group! { name = benches; config = Criterion::default().sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(2)); targets = compositions }
criterion_main!(benches);
