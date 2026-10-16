//! Execution benchmarks.
use automation_structures as a;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::{hint::black_box, time::Duration};

const SIZES: [usize; 3] = [16, 256, 4096];

fn sequential(n: usize) -> Option<bool> {
    let mut owner = a::Sequential::new(n, 4, 0).ok()?;
    for _ in 0..n {
        if !owner.begin_step() || !owner.complete_step(black_box(1)) {
            return None;
        }
    }
    Some(owner.is_done())
}

fn fork_join(n: usize) -> Option<bool> {
    let mut owner = a::ForkJoin::new(n, 4, 0).ok()?;
    for worker in 0..n {
        if !owner.start_worker(black_box(worker)) || !owner.complete_worker(worker, black_box(1)) {
            return None;
        }
    }
    if !owner.barrier() || !owner.produce_output() {
        return None;
    }
    Some(owner.output_ready())
}

fn dag(n: usize, wide: bool) -> Option<bool> {
    let mut edges = Vec::new();
    for node in 1..n {
        edges.push((if wide { 0 } else { node.checked_sub(1)? }, node));
    }
    let mut owner = a::StepGraph::new(n, edges).ok()?;
    for node in 0..n {
        if node != 0 && !owner.become_ready(black_box(node)) {
            return None;
        }
        if !owner.start(black_box(node)) || !owner.complete(node) {
            return None;
        }
    }
    Some(owner.is_done())
}

fn stream(n: usize, stages: usize) -> Option<usize> {
    let mut owner = a::StreamGraph::<a::FifoStorage>::try_with_storage(stages, n, n, 4).ok()?;
    for _ in 0..n {
        if !owner.ingest(black_box(1)) || !owner.advance_first() {
            return None;
        }
        if stages == 4 && !owner.advance_second() {
            return None;
        }
        black_box(owner.consume()?);
    }
    Some(owner.emitted())
}

fn typed_stream(n: usize) -> Option<a::TypedStream<u64>> {
    let mut owner = a::TypedStream::try_new(1, n, u64::try_from(n).ok()?).ok()?;
    for _ in 0..n {
        owner.publish(1, 1).ok()?;
    }
    Some(owner)
}

fn fanout(n: usize) -> Option<a::TypedFanout<u64>> {
    let mut owner = a::TypedFanout::try_new(1, n, u64::try_from(n).ok()?).ok()?;
    for _ in 0..n {
        owner.publish(1, 1).ok()?;
    }
    Some(owner)
}

fn branch_fanout(n: usize) -> Option<a::TypedBranchFanout<u64>> {
    let limit = n.checked_add(1)?;
    let bytes = u64::try_from(n).ok()?;
    let mut owner =
        a::TypedBranchFanout::try_new([1, 2], [n, limit], [bytes, bytes.checked_mul(2)?], limit)
            .ok()?;
    for _ in 0..n {
        owner.publish_pair(1, 2, 1).ok()?;
    }
    Some(owner)
}

fn buffer<S: a::BufferLayout<u64>>(n: usize) -> Option<a::Buffer<u64, S>> {
    let mut owner = a::Buffer::<u64, S>::try_with_storage(n).ok()?;
    for _ in 0..n {
        owner.push(1).ok()?;
    }
    Some(owner)
}

fn execution(c: &mut Criterion) {
    let mut group = c.benchmark_group("modalities");
    for n in SIZES {
        assert_eq!(sequential(n), Some(true));
        assert_eq!(fork_join(n), Some(true));
        group.bench_with_input(BenchmarkId::new("sequential_lifecycle", n), &n, |b, n| {
            b.iter(|| {
                let result = sequential(black_box(*n));
                assert_eq!(result, Some(true));
                black_box(result)
            })
        });
        group.bench_with_input(BenchmarkId::new("fork_join_lifecycle", n), &n, |b, n| {
            b.iter(|| {
                let result = fork_join(black_box(*n));
                assert_eq!(result, Some(true));
                black_box(result)
            })
        });
        for (name, wide) in [("dag_chain", false), ("dag_wide_fork", true)] {
            assert_eq!(dag(n, wide), Some(true));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, n| {
                b.iter(|| {
                    let result = dag(black_box(*n), wide);
                    assert_eq!(result, Some(true));
                    black_box(result)
                })
            });
        }
        for stages in [3, 4] {
            assert_eq!(stream(n, stages), Some(n));
            group.bench_with_input(
                BenchmarkId::new(format!("stream_{stages}_stage"), n),
                &n,
                |b, n| {
                    b.iter(|| {
                        let result = stream(black_box(*n), stages);
                        assert_eq!(result, Some(*n));
                        black_box(result)
                    })
                },
            );
        }
    }
    group.finish();

    let mut group = c.benchmark_group("typed_stream");
    for n in SIZES {
        let fixture = typed_stream(n);
        assert_eq!(fixture.as_ref().map(a::TypedStream::len), Some(n));
        group.bench_with_input(
            BenchmarkId::new("receive_publish_fixed_depth", n),
            &n,
            |b, n| {
                b.iter_batched_ref(
                    || typed_stream(*n),
                    |owner| {
                        let result = owner.as_mut().and_then(|owner| {
                            let receipt = owner.receive().ok()?;
                            let sequence = owner.publish(black_box(1), 1).ok()?;
                            Some((receipt.value, sequence))
                        });
                        assert!(result.is_some());
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        let mut full = fixture;
        assert!(
            full.as_mut()
                .is_some_and(|owner| owner.publish(1, 1).is_err())
        );
        group.bench_with_input(BenchmarkId::new("slot_pressure_refusal", n), &n, |b, _| {
            b.iter(|| {
                let result = full
                    .as_mut()
                    .map(|owner| owner.publish(black_box(1), 1).is_err());
                assert_eq!(result, Some(true));
                black_box(result)
            })
        });
        group.bench_with_input(BenchmarkId::new("closed_drain", n), &n, |b, n| {
            b.iter_batched_ref(
                || {
                    typed_stream(*n).map(|mut owner| {
                        owner.close_input();
                        owner
                    })
                },
                |owner| {
                    let result = owner.as_mut().and_then(|owner| {
                        for _ in 0..*n {
                            black_box(owner.receive().ok()?);
                        }
                        Some(matches!(owner.receive(), Err(a::TypedStreamError::Closed)))
                    });
                    assert_eq!(result, Some(true));
                    black_box(result)
                },
                BatchSize::PerIteration,
            )
        });
    }
    let mut byte_full = a::TypedStream::<u64>::try_new(1, 2, 1).ok();
    assert!(
        byte_full
            .as_mut()
            .is_some_and(|owner| owner.publish(1, 1).is_ok())
    );
    group.bench_function("byte_pressure_refusal", |b| {
        b.iter(|| {
            let result = byte_full
                .as_mut()
                .map(|owner| owner.publish(black_box(1), 1).is_err());
            assert_eq!(result, Some(true));
            black_box(result)
        })
    });
    group.finish();

    let mut group = c.benchmark_group("fanout");
    for n in SIZES {
        assert_eq!(
            fanout(n).as_ref().map(a::TypedFanout::retained_len),
            Some(n)
        );
        assert_eq!(
            branch_fanout(n)
                .as_ref()
                .map(|owner| owner.len(a::FanoutBranch::Left)),
            Some(n)
        );
        group.bench_with_input(
            BenchmarkId::new("shared_original_consume_both_publish", n),
            &n,
            |b, n| {
                b.iter_batched_ref(
                    || fanout(*n),
                    |owner| {
                        let result = owner.as_mut().and_then(|owner| {
                            let left = owner.observe(a::FanoutBranch::Left).ok()?.token;
                            let right = owner.observe(a::FanoutBranch::Right).ok()?.token;
                            owner.consume(left).ok()?;
                            owner.consume(right).ok()?;
                            owner.publish(black_box(1), 1).ok()
                        });
                        assert!(result.is_some());
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        group.bench_with_input(
            BenchmarkId::new("asymmetric_receive_both_publish", n),
            &n,
            |b, n| {
                b.iter_batched_ref(
                    || branch_fanout(*n),
                    |owner| {
                        let result = owner.as_mut().and_then(|owner| {
                            black_box(owner.receive(a::FanoutBranch::Left).ok()?);
                            black_box(owner.receive(a::FanoutBranch::Right).ok()?);
                            owner.publish_pair(black_box(1), black_box(2), 1).ok()
                        });
                        assert!(result.is_some());
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
        let mut owner = branch_fanout(n);
        assert!(
            owner
                .as_mut()
                .is_some_and(|owner| owner.publish_pair(1, 2, 1).is_err())
        );
        group.bench_with_input(
            BenchmarkId::new("asymmetric_left_pressure_refusal", n),
            &n,
            |b, _| {
                b.iter(|| {
                    let result = owner
                        .as_mut()
                        .map(|owner| owner.publish_pair(black_box(1), black_box(2), 1).is_err());
                    assert_eq!(result, Some(true));
                    black_box(result)
                })
            },
        );
    }
    group.finish();

    let mut group = c.benchmark_group("buffer");
    for n in SIZES {
        let mut contiguous = buffer::<a::ContiguousStorage>(n);
        let mut fifo = buffer::<a::FifoStorage>(n);
        assert_eq!(contiguous.as_ref().map(a::Buffer::len), Some(n));
        assert_eq!(fifo.as_ref().map(a::Buffer::len), Some(n));
        group.bench_with_input(BenchmarkId::new("contiguous_pop_push", n), &n, |b, _| {
            b.iter(|| {
                let result = contiguous.as_mut().and_then(|owner| {
                    let value = owner.pop()?;
                    owner.push(black_box(1)).ok()?;
                    Some(value)
                });
                assert_eq!(result, Some(1));
                black_box(result)
            })
        });
        group.bench_with_input(BenchmarkId::new("fifo_pop_push", n), &n, |b, _| {
            b.iter(|| {
                let result = fifo.as_mut().and_then(|owner| {
                    let value = owner.pop()?;
                    owner.push(black_box(1)).ok()?;
                    Some(value)
                });
                assert_eq!(result, Some(1));
                black_box(result)
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("accumulator");
    for n in SIZES {
        group.bench_with_input(BenchmarkId::new("drain_pending_prefix", n), &n, |b, n| {
            b.iter_batched_ref(
                || a::Accumulator::new(vec![1_u64; *n]),
                |owner| {
                    for _ in 0..*n {
                        let value = owner.advance();
                        assert_eq!(value, Some(1));
                        let _observed = black_box(value);
                    }
                    assert_eq!(owner.accumulated_len(), *n);
                    black_box(owner.accumulated_len())
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_with_input(
            BenchmarkId::new("append_completed_prefix", n),
            &n,
            |b, n| {
                b.iter_batched_ref(
                    || a::Accumulator::from_accumulated(vec![1_u64; *n]),
                    |owner| {
                        let result = owner.try_append(black_box(1));
                        assert!(result.is_ok());
                        black_box(result)
                    },
                    BatchSize::PerIteration,
                )
            },
        );
    }
    group.finish();
}

criterion_group! { name = benches; config = Criterion::default().sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(2)); targets = execution }
criterion_main!(benches);
