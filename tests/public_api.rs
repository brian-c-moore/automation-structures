#[test]
fn borrowed_batch_reductions_preserve_exact_bounded_results_and_input() {
    use automation_structures::compositions::reduction::{reduce_max, reduce_sum};
    use automation_structures::{IncrementalReduction, MaximumU64};
    for (items, sum, maximum) in [
        (vec![], 0, 0),
        (vec![1_000_000_000], 1_000_000_000, 1_000_000_000),
        (
            vec![1_000_000_000, 0, 1_000_000_000],
            2_000_000_000,
            1_000_000_000,
        ),
        (vec![9, 2, 3, 9, 0], 23, 9),
        (vec![0, 3, 2, 9], 14, 9),
    ] {
        let before = items.clone();
        let address = items.as_ptr();
        assert_eq!(reduce_sum(&items), sum);
        assert_eq!(reduce_max(&items), maximum);
        assert_eq!(items, before);
        assert_eq!(items.as_ptr(), address);
    }
    let mut maximum = IncrementalReduction::new(3, MaximumU64);
    assert!(maximum.try_record(u64::MAX));
    assert!(maximum.try_record(0));
    assert!(maximum.try_record(u64::MAX));
    assert_eq!(maximum.result(), u64::MAX);
    assert_eq!(maximum.processed_len(), 3);
    assert!(!maximum.try_record(1));
    assert_eq!(maximum.result(), u64::MAX);
}

#[test]
fn counter_preview_frames_generation_exhaustion() {
    let mut counter = automation_structures::Counter::new(u64::MAX);
    assert!(!counter.can_increment());
    assert!(!counter.try_increment());
    assert_eq!(counter.value(), u64::MAX);
    assert!(counter.try_decrement());
    assert!(counter.can_increment());
    assert!(counter.try_increment());
    assert_eq!(counter.value(), u64::MAX);
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions exercise typed FIFO custody, pressure, and closure; setup propagates typed errors"
)]
fn typed_stream_preserves_original_fifo_payloads_pressure_and_closure()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{TypedStream, TypedStreamError};
    let mut stream = TypedStream::try_new(73, 2, 5)?;
    assert!(matches!(stream.receive(), Err(TypedStreamError::Empty)));
    assert_eq!(stream.received_count(), 0);
    let first = vec![1u8, 2].into_boxed_slice();
    let first_address = first.as_ptr();
    let second = vec![3u8, 4, 5].into_boxed_slice();
    let second_address = second.as_ptr();
    assert_eq!(
        stream.publish(first, 2).map_err(|refusal| refusal.error)?,
        0
    );
    assert_eq!(
        stream.publish(second, 3).map_err(|refusal| refusal.error)?,
        1
    );
    assert_eq!((stream.len(), stream.retained_bytes()), (2, 5));
    let refused = vec![6u8].into_boxed_slice();
    let refused_address = refused.as_ptr();
    let refusal = stream
        .publish(refused, 1)
        .err()
        .ok_or("expected slot refusal")?;
    assert_eq!(refusal.error, TypedStreamError::SlotCapacity);
    assert_eq!(refusal.value.as_ptr(), refused_address);
    assert_eq!((stream.len(), stream.retained_bytes()), (2, 5));
    let received = stream.receive()?;
    assert_eq!(
        (received.scope, received.sequence, received.encoded_bytes),
        (73, 0, 2)
    );
    assert_eq!(received.value.as_ptr(), first_address);
    assert_eq!(&*received.value, &[1, 2]);
    assert_eq!(stream.received_count(), 1);
    assert_eq!((stream.len(), stream.retained_bytes()), (1, 3));
    let third = vec![7u8, 8].into_boxed_slice();
    let third_address = third.as_ptr();
    let refusal = stream
        .publish(third, 3)
        .err()
        .ok_or("expected byte refusal")?;
    assert_eq!(refusal.error, TypedStreamError::ByteCapacity);
    assert_eq!(refusal.value.as_ptr(), third_address);
    assert_eq!(
        stream
            .publish(refusal.value, 2)
            .map_err(|refusal| refusal.error)?,
        2
    );
    let received = stream.receive()?;
    assert_eq!(received.sequence, 1);
    assert_eq!(received.value.as_ptr(), second_address);
    assert!(stream.close_input());
    assert!(!stream.close_input());
    assert!(!stream.is_drained());
    let refused = vec![10u8].into_boxed_slice();
    let refused_address = refused.as_ptr();
    let refusal = stream
        .publish(refused, 1)
        .err()
        .ok_or("expected closed refusal")?;
    assert_eq!(refusal.error, TypedStreamError::Closed);
    assert_eq!(refusal.value.as_ptr(), refused_address);
    let received = stream.receive()?;
    assert_eq!(received.sequence, 2);
    assert_eq!(received.value.as_ptr(), third_address);
    assert_eq!((stream.len(), stream.retained_bytes()), (0, 0));
    assert_eq!(stream.received_count(), 3);
    assert!(stream.is_empty());
    assert!(stream.is_drained());
    assert!(matches!(stream.receive(), Err(TypedStreamError::Closed)));

    let mut zero = TypedStream::try_new(74, 1, 0)?;
    assert!(
        matches!(zero.publish(11u64, 1), Err(refusal) if refusal.error == TypedStreamError::ByteCapacity && refusal.value == 11)
    );
    assert_eq!(zero.publish(12u64, 0).map_err(|refusal| refusal.error)?, 0);
    assert_eq!(zero.receive()?.value, 12);
    for ordinal in 1..=100u64 {
        assert_eq!(
            zero.publish(ordinal, 0).map_err(|refusal| refusal.error)?,
            ordinal
        );
        assert_eq!(zero.receive()?.value, ordinal);
    }
    let mut no_slots = TypedStream::try_new(75, 0, u64::MAX)?;
    assert!(
        matches!(no_slots.publish(13u64, 0), Err(refusal) if refusal.error == TypedStreamError::SlotCapacity && refusal.value == 13)
    );
    assert!(no_slots.close_input());
    assert!(no_slots.is_drained());
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions check the Signal change/catch-up and token-refusal contract; setup propagates typed errors"
)]
fn summary_signal_retains_latest_value_and_dynamic_generation_custody()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{SignalObservation, SignalProfileError, SummarySignal};
    let mut signal = SummarySignal::new(41, 7u64, 2, 3);
    assert_eq!(
        (
            signal.value(),
            signal.change_count(),
            signal.listener_count()
        ),
        (7, 0, 0)
    );
    let first = signal.register()?;
    assert!(!signal.pending(first)?);
    assert_eq!(
        signal.notify(first)?,
        SignalObservation {
            value: 7,
            head: 0,
            changed: false
        }
    );
    assert_eq!(signal.set_value(7), Ok(false));
    assert_eq!(signal.set_value(9), Ok(true));
    assert_eq!(signal.set_value(11), Ok(true));
    assert!(signal.pending(first)?);
    let second = signal.register()?;
    assert_ne!(first, second);
    assert_eq!(signal.register(), Err(SignalProfileError::ListenerCapacity));
    assert_eq!(
        signal.notify(first)?,
        SignalObservation {
            value: 11,
            head: 2,
            changed: true
        }
    );
    assert_eq!(
        signal.notify(first)?,
        SignalObservation {
            value: 11,
            head: 2,
            changed: false
        }
    );
    assert_eq!(
        signal.notify(second)?,
        SignalObservation {
            value: 11,
            head: 2,
            changed: true
        }
    );
    signal.remove(first)?;
    assert_eq!(signal.listener_count(), 1);
    let replacement = signal.register()?;
    assert_ne!(first, replacement);
    assert_eq!(
        signal.pending(first),
        Err(SignalProfileError::UnknownListener)
    );
    assert_eq!(
        signal.notify(first),
        Err(SignalProfileError::UnknownListener)
    );
    assert_eq!(
        signal.remove(first),
        Err(SignalProfileError::UnknownListener)
    );
    assert!(signal.pending(replacement)?);
    let mut foreign = SummarySignal::new(42, 0u64, 1, 0);
    assert_eq!(
        foreign.notify(replacement),
        Err(SignalProfileError::ForeignScope)
    );
    assert_eq!(
        foreign.remove(replacement),
        Err(SignalProfileError::ForeignScope)
    );
    assert_eq!(
        foreign.pending(replacement),
        Err(SignalProfileError::ForeignScope)
    );
    assert_eq!(
        (
            foreign.listener_count(),
            foreign.value(),
            foreign.change_count()
        ),
        (0, 0, 0)
    );
    assert_eq!(signal.set_value(13), Ok(true));
    assert_eq!(
        signal.set_value(15),
        Err(SignalProfileError::ChangeCapacity)
    );
    assert_eq!(signal.set_value(13), Ok(false));
    assert_eq!(signal.value(), 13);
    assert_eq!(signal.change_count(), 3);
    assert_eq!(
        signal.notify(replacement)?,
        SignalObservation {
            value: 13,
            head: 3,
            changed: true
        }
    );
    signal.remove(second)?;
    signal.remove(replacement)?;
    assert_eq!(signal.listener_count(), 0);
    let mut no_listeners = SummarySignal::new(43, 0u64, 0, 0);
    assert_eq!(
        no_listeners.register(),
        Err(SignalProfileError::ListenerCapacity)
    );
    assert_eq!(
        no_listeners.set_value(1),
        Err(SignalProfileError::ChangeCapacity)
    );
    assert_eq!(no_listeners.value(), 0);
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions check shared original custody, branch pressure and final-reference release; setup propagates typed errors"
)]
fn typed_fanout_retains_original_until_both_governed_branches_consume()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{FanoutBranch, TypedFanout, TypedFanoutError};
    use std::rc::Rc;
    let mut stream = TypedFanout::try_new(81, 2, 5)?;
    assert!(matches!(
        stream.observe(FanoutBranch::Left),
        Err(TypedFanoutError::Empty)
    ));
    let first = Rc::new(vec![1u8, 2]);
    let first_address = first.as_ptr();
    let first_lifetime = Rc::downgrade(&first);
    let second = Rc::new(vec![3u8, 4, 5]);
    let second_lifetime = Rc::downgrade(&second);
    assert_eq!(
        stream.publish(first, 2).map_err(|refusal| refusal.error)?,
        0
    );
    assert_eq!(
        stream.publish(second, 3).map_err(|refusal| refusal.error)?,
        1
    );
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (2, 5));
    assert_eq!(stream.remaining_references(0), Some(2));
    assert_eq!(first_lifetime.strong_count(), 1);
    let left = stream.observe(FanoutBranch::Left)?;
    assert_eq!(left.value.as_ptr(), first_address);
    let left_token = left.token;
    assert_eq!(stream.observe(FanoutBranch::Left)?.token, left_token);
    stream.consume(left_token)?;
    assert_eq!(stream.remaining_references(0), Some(1));
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (2, 5));
    assert_eq!(first_lifetime.strong_count(), 1);
    assert_eq!(
        stream.consume(left_token),
        Err(TypedFanoutError::StaleObservation)
    );
    let third = Rc::new(vec![7u8, 8]);
    let third_lifetime = Rc::downgrade(&third);
    let refusal = stream
        .publish(third, 2)
        .err()
        .ok_or("expected branch pressure")?;
    assert_eq!(refusal.error, TypedFanoutError::BranchCapacity);
    assert_eq!(stream.pending_len(FanoutBranch::Left), 1);
    assert_eq!(stream.pending_len(FanoutBranch::Right), 2);
    let right = stream.observe(FanoutBranch::Right)?;
    assert_eq!(right.value.as_ptr(), first_address);
    stream.consume(right.token)?;
    assert_eq!(first_lifetime.strong_count(), 0);
    assert_eq!(stream.remaining_references(0), None);
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (1, 3));
    assert_eq!(
        stream
            .publish(refusal.value, 2)
            .map_err(|refusal| refusal.error)?,
        2
    );
    let next_left = stream.observe(FanoutBranch::Left)?.token;
    assert_eq!(next_left.sequence(), 1);
    stream.consume(next_left)?;
    assert_eq!(stream.remaining_references(1), Some(1));

    let mut other = TypedFanout::try_new(82, 1, 1)?;
    other
        .publish(Rc::new(vec![9u8]), 1)
        .map_err(|refusal| refusal.error)?;
    let foreign = other.observe(FanoutBranch::Left)?.token;
    assert_eq!(stream.consume(foreign), Err(TypedFanoutError::ForeignScope));
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (2, 5));
    assert!(stream.close_input());
    assert!(!stream.close_input());
    assert!(!stream.is_drained());
    assert!(
        matches!(stream.publish(Rc::new(vec![10u8]), 1), Err(refusal) if refusal.error == TypedFanoutError::Closed)
    );
    let next_right = stream.observe(FanoutBranch::Right)?.token;
    stream.consume(next_right)?;
    assert_eq!(second_lifetime.strong_count(), 0);
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (1, 2));
    let last_right = stream.observe(FanoutBranch::Right)?.token;
    stream.consume(last_right)?;
    assert_eq!(third_lifetime.strong_count(), 1);
    assert_eq!(stream.remaining_references(2), Some(1));
    assert_eq!(stream.retained_bytes(), 2);
    let last_left = stream.observe(FanoutBranch::Left)?.token;
    stream.consume(last_left)?;
    assert_eq!(third_lifetime.strong_count(), 0);
    assert_eq!((stream.retained_len(), stream.retained_bytes()), (0, 0));
    assert!(stream.is_drained());
    assert_eq!(
        stream.consume(last_left),
        Err(TypedFanoutError::StaleObservation)
    );
    assert!(matches!(
        stream.observe(FanoutBranch::Left),
        Err(TypedFanoutError::Closed)
    ));
    assert!(matches!(
        stream.observe(FanoutBranch::Right),
        Err(TypedFanoutError::Closed)
    ));
    assert!(matches!(
        TypedFanout::<u64>::try_new(83, 0, 5),
        Err(TypedFanoutError::ZeroCapacity)
    ));
    let mut pressure = TypedFanout::try_new(83, 1, 0)?;
    assert!(
        matches!(pressure.publish(12u64, 1), Err(refusal) if refusal.error == TypedFanoutError::ByteCapacity && refusal.value == 12)
    );
    assert_eq!(pressure.retained_len(), 0);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions check Registry ownership transfer; fallible setup returns typed errors"
)]
fn registry_take_returns_original_owned_payload_and_frames_other_bindings()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::resource_registry::ResourceRegistry;
    let mut registry = ResourceRegistry::new();
    let first = vec![1u8, 2].into_boxed_slice();
    let first_address = first.as_ptr();
    let middle = vec![3u8, 4].into_boxed_slice();
    let middle_address = middle.as_ptr();
    let last = vec![5u8, 6].into_boxed_slice();
    let last_address = last.as_ptr();
    registry
        .try_insert_unique(7u64, first)
        .map_err(|(reason, _, _)| reason)?;
    registry
        .try_insert_unique(2u64, middle)
        .map_err(|(reason, _, _)| reason)?;
    registry
        .try_insert_unique(9u64, last)
        .map_err(|(reason, _, _)| reason)?;
    let (key, returned) = registry
        .take_query(&2u64)
        .ok_or("missing owned middle binding")?;
    assert_eq!(key, 2);
    assert_eq!(returned.as_ptr(), middle_address);
    assert_eq!(&*returned, [3, 4]);
    assert_eq!(registry.entries.len(), 2);
    assert!(registry.take_query(&2u64).is_none());
    assert!(registry.take_query(&100u64).is_none());
    assert_eq!(
        registry
            .lookup_query(&7u64)
            .ok_or("missing first binding")?
            .as_ptr(),
        first_address
    );
    assert_eq!(
        registry
            .lookup_query(&9u64)
            .ok_or("missing last binding")?
            .as_ptr(),
        last_address
    );
    assert_eq!(
        registry
            .take_query(&9u64)
            .ok_or("missing last transfer")?
            .1
            .as_ptr(),
        last_address
    );
    assert_eq!(
        registry
            .take_query(&7u64)
            .ok_or("missing first transfer")?
            .1
            .as_ptr(),
        first_address
    );
    assert!(registry.entries.is_empty());
    assert!(registry.take_query(&7u64).is_none());
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions are the independent minimum-selection test oracle; setup returns typed storage errors"
)]
fn complete_minimum_selection_preserves_every_tie_without_a_quota()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{CompetitiveSelectionMinimum, NullableSigned, SignedRowOrder};
    for (input, expected) in [
        (vec![], vec![]),
        (vec![3, 1, 1, 2], vec![1usize, 2]),
        (vec![1, 1, 1, 1], vec![0usize, 1, 2, 3]),
        (vec![i64::MAX, i64::MIN, i64::MIN, 0], vec![1usize, 2]),
        (vec![7], vec![0usize]),
    ] {
        let values: Vec<_> = input.into_iter().map(NullableSigned::Value).collect();
        let original = values.as_ptr();
        let selected = CompetitiveSelectionMinimum::try_new(SignedRowOrder {
            values: &values,
            descending: false,
            nulls_first: false,
        })
        .map_err(|(reason, _)| reason)?;
        assert_eq!(selected.selected(), expected);
        assert_eq!(selected.len(), expected.len());
        assert_eq!(selected.is_empty(), expected.is_empty());
        assert_eq!(values.as_ptr(), original);
    }
    let values = vec![
        NullableSigned::Missing,
        NullableSigned::Value(0),
        NullableSigned::Missing,
    ];
    let selected = CompetitiveSelectionMinimum::try_new(SignedRowOrder {
        values: &values,
        descending: false,
        nulls_first: true,
    })
    .map_err(|(reason, _)| reason)?;
    assert_eq!(selected.selected(), [0, 2]);
    let values = vec![
        NullableSigned::Value(3),
        NullableSigned::Value(1),
        NullableSigned::Value(3),
    ];
    let selected = CompetitiveSelectionMinimum::try_new(SignedRowOrder {
        values: &values,
        descending: true,
        nulls_first: false,
    })
    .map_err(|(reason, _)| reason)?;
    assert_eq!(selected.selected(), [0, 2]);
    let values = vec![NullableSigned::Value(0); 257];
    let selected = CompetitiveSelectionMinimum::try_new(SignedRowOrder {
        values: &values,
        descending: false,
        nulls_first: false,
    })
    .map_err(|(reason, _)| reason)?;
    assert_eq!(selected.selected(), (0usize..257).collect::<Vec<_>>());
    Ok(())
}

#[cfg(feature = "proof-api")]
mod owned_reduction {
    use crate::domain_witnesses::AppendBytes;
    use automation_structures::{OwnedReductionError, VersionedReduction};

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn non_copy_versions_preserve_order_refusal_cancellation_and_original_allocations()
    -> Result<(), Box<dyn std::error::Error>> {
        let initial = vec![7u8];
        let original = initial.as_ptr();
        let mut owner = VersionedReduction::try_new(initial, 2, AppendBytes { maximum: 3 })
            .map_err(|(reason, _, _)| reason)?;
        assert_eq!(owner.processed_len(), 0);
        assert_eq!(owner.version(0), Some(&vec![7]));
        assert_eq!(owner.version(1), None);
        let input = vec![4u8];
        let input_address = input.as_ptr();
        let cancelled = owner.prepare(input).map_err(|(reason, _)| reason)?.cancel();
        assert_eq!(cancelled.as_ptr(), input_address);
        assert_eq!(owner.processed_len(), 0);
        assert_eq!(
            owner
                .prepare(cancelled)
                .map_err(|(reason, _)| reason)?
                .commit(),
            1
        );
        assert_eq!(owner.version(1), Some(&vec![7, 4]));
        let first = owner
            .version(1)
            .ok_or("missing first owned version")?
            .as_ptr();
        let too_large = vec![9u8, 8];
        let refused_address = too_large.as_ptr();
        let (reason, refused) = owner
            .prepare(too_large)
            .err()
            .ok_or("domain refusal was accepted")?;
        assert_eq!(reason, OwnedReductionError::Domain);
        assert_eq!(refused.as_ptr(), refused_address);
        assert_eq!(owner.processed_len(), 1);
        assert_eq!(
            owner
                .version(1)
                .ok_or("missing retained first version")?
                .as_ptr(),
            first
        );
        assert_eq!(
            owner
                .prepare(vec![3])
                .map_err(|(reason, _)| reason)?
                .commit(),
            2
        );
        assert_eq!(owner.version(2), Some(&vec![7, 4, 3]));
        assert_eq!(
            owner.version(0).ok_or("missing initial version")?.as_ptr(),
            original
        );
        assert_eq!(
            owner
                .version(1)
                .ok_or("missing historical version")?
                .as_ptr(),
            first
        );
        assert_eq!(owner.version(usize::MAX), None);
        let (reason, input) = owner
            .prepare(vec![1])
            .err()
            .ok_or("capacity refusal was accepted")?;
        assert_eq!(reason, OwnedReductionError::Capacity);
        assert_eq!(input, vec![1]);
        assert_eq!(owner.processed_len(), 2);
        assert_eq!(owner.version(2), Some(&vec![7, 4, 3]));
        let mut zero = VersionedReduction::try_new(vec![], 0, AppendBytes { maximum: 0 })
            .map_err(|(reason, _, _)| reason)?;
        assert_eq!(zero.version(0), Some(&vec![]));
        assert_eq!(
            zero.prepare(vec![])
                .err()
                .ok_or("zero ceiling was accepted")?
                .0,
            OwnedReductionError::Capacity
        );
        Ok(())
    }
}

mod typed_admission {
    use automation_structures::primitives::resource_registry::ByteKey;
    use automation_structures::{TypedAllocation, TypedAllocationError, UnrestrictedAllocation};

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn borrowed_queries_preserve_byte_identity_and_payload_custody()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut allocation = TypedAllocation::try_new(&vec![2, 4], UnrestrictedAllocation)?;
        allocation
            .prepare(ByteKey::from_bytes(vec![0, 255]), vec![7u8], vec![1, 1])?
            .commit();
        let query: &[u8] = &[0, 255];
        let pointer = allocation
            .get_query(&query)
            .ok_or("missing admitted payload")?
            .as_ptr();
        assert_eq!(allocation.get_query(&query), Some(&vec![7]));
        assert!(allocation.get_query(&(&[0][..])).is_none());
        let sealed = allocation.seal();
        assert_eq!(
            sealed
                .get_query(&query)
                .ok_or("missing sealed payload")?
                .as_ptr(),
            pointer
        );
        assert_eq!(sealed.budget(0), Some((2, 1)));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn preparation_cancellation_and_seal_preserve_the_owned_payload()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::sync::Arc;
        let mut allocation = TypedAllocation::try_new(&vec![3, 3, 5], UnrestrictedAllocation)?;
        let payload = Arc::new(vec![3u8, 1]);
        let retained = Arc::clone(&payload);
        let charges = vec![1, 0, 2];
        let charges_address = charges.as_ptr();
        let pending = allocation.prepare(ByteKey::from_bytes(vec![]), payload, charges)?;
        let cancelled = pending.cancel();
        assert!(Arc::ptr_eq(&cancelled.value, &retained));
        assert_eq!(cancelled.charges.as_ptr(), charges_address);
        assert_eq!(Arc::strong_count(&retained), 2);
        assert_eq!(allocation.len(), 0);
        for dimension in 0..3 {
            assert_eq!(
                allocation
                    .budget(dimension)
                    .ok_or("missing Budget dimension")?
                    .1,
                0
            );
        }
        allocation
            .prepare(cancelled.key, cancelled.value, cancelled.charges)?
            .commit();
        assert_eq!(allocation.len(), 1);
        assert_eq!(allocation.budget(0), Some((3, 1)));
        assert_eq!(allocation.budget(1), Some((3, 0)));
        assert_eq!(allocation.budget(2), Some((5, 2)));
        let duplicate = allocation
            .prepare(
                ByteKey::from_bytes(vec![]),
                Arc::new(vec![99u8]),
                vec![1, 0, 1],
            )
            .err()
            .ok_or("duplicate identity admitted")?;
        assert_eq!(duplicate.reason, Some(TypedAllocationError::DuplicateKey));
        assert_eq!(duplicate.value.as_slice(), &[99]);
        assert!(Arc::ptr_eq(
            allocation
                .get(&ByteKey::from_bytes(vec![]))
                .ok_or("missing retained payload")?,
            &retained
        ));
        assert_eq!(allocation.budget(2), Some((5, 2)));
        let dropped = allocation.prepare(
            ByteKey::from_bytes(vec![1]),
            Arc::new(vec![8u8]),
            vec![1, 1, 1],
        )?;
        drop(dropped);
        assert_eq!(allocation.len(), 1);
        assert_eq!(allocation.budget(0), Some((3, 1)));
        let sealed = allocation.seal();
        assert_eq!(sealed.len(), 1);
        assert!(Arc::ptr_eq(
            sealed
                .get(&ByteKey::from_bytes(vec![]))
                .ok_or("missing sealed payload")?,
            &retained
        ));
        assert_eq!(sealed.budget(2), Some((5, 2)));
        assert_eq!(sealed.budget(3), None);
        assert!(sealed.get(&ByteKey::from_bytes(vec![1])).is_none());
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn every_dimension_and_shape_refusal_preserves_all_owners()
    -> Result<(), Box<dyn std::error::Error>> {
        assert!(matches!(
            TypedAllocation::<u64, Vec<u8>>::try_new(&vec![], UnrestrictedAllocation),
            Err(TypedAllocationError::EmptySchema)
        ));
        for (capacities, expected_dimension) in
            [(vec![0, 5, 5], 0), (vec![5, 0, 5], 1), (vec![5, 5, 0], 2)]
        {
            let mut allocation = TypedAllocation::try_new(&capacities, UnrestrictedAllocation)?;
            let payload = vec![7u8, 3];
            let address = payload.as_ptr();
            let refused = allocation
                .prepare(7u64, payload, vec![1, 1, 1])
                .err()
                .ok_or("over-capacity entry admitted")?;
            assert_eq!(refused.reason, Some(TypedAllocationError::Capacity));
            assert_eq!(refused.dimension, Some(expected_dimension));
            assert_eq!(refused.value.as_ptr(), address);
            assert_eq!(refused.value, vec![7, 3]);
            assert!(allocation.is_empty());
            for (dimension, capacity) in capacities.iter().copied().enumerate() {
                assert_eq!(allocation.budget(dimension), Some((capacity, 0)));
            }
        }
        let mut allocation = TypedAllocation::try_new(&vec![2, 3], UnrestrictedAllocation)?;
        assert_eq!(
            allocation
                .prepare(1u64, vec![1u8], vec![1])
                .err()
                .ok_or("wrong-width entry admitted")?
                .reason,
            Some(TypedAllocationError::WidthMismatch)
        );
        for membership in [0, 2, u64::MAX] {
            assert_eq!(
                allocation
                    .prepare(1, vec![1], vec![membership, 0])
                    .err()
                    .ok_or("invalid membership charge admitted")?
                    .reason,
                Some(TypedAllocationError::MembershipCharge)
            );
        }
        assert_eq!(allocation.budget(0), Some((2, 0)));
        assert_eq!(allocation.budget(1), Some((3, 0)));
        assert_eq!(
            allocation
                .prepare(1, vec![1], vec![1, u64::MAX])
                .err()
                .ok_or("over-capacity charge admitted")?
                .dimension,
            Some(1)
        );
        assert!(allocation.is_empty());
        Ok(())
    }

    struct OnlySeven;
    impl automation_structures::AllocationDomain<u64, Vec<u8>> for OnlySeven {
        fn admits_exec(&self, key: &u64, value: &Vec<u8>, charges: &Vec<u64>) -> bool {
            *key == 7 && charges.len() == 2 && charges.get(1) == Some(&(value.len() as u64))
        }
    }
    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn domain_refusal_returns_data_and_diagnostics_exclude_payloads()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut allocation = TypedAllocation::try_new(&vec![2, 20], OnlySeven)?;
        let refused = allocation
            .prepare(8u64, b"secret-payload".to_vec(), vec![1, 14])
            .err()
            .ok_or("out-of-domain entry admitted")?;
        assert_eq!(refused.reason, Some(TypedAllocationError::OutsideDomain));
        assert_eq!(refused.value, b"secret-payload");
        assert!(!format!("{refused:?} {refused}").contains("secret-payload"));
        assert!(allocation.is_empty());
        assert_eq!(allocation.budget(1), Some((20, 0)));
        allocation
            .prepare(7, b"secret-payload".to_vec(), vec![1, 14])?
            .commit();
        assert_eq!(
            allocation.get(&7).map(Vec::as_slice),
            Some(b"secret-payload".as_slice())
        );
        assert_eq!(allocation.budget(1), Some((20, 14)));
        Ok(())
    }
}

mod typed_batch {
    use automation_structures::{
        ByteKey, TypedAllocation, TypedAllocationError, UnrestrictedAllocation,
    };

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn unbudgeted_membership_has_no_quota_and_retains_exact_owned_batches()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut allocation = TypedAllocation::unbudgeted(UnrestrictedAllocation);
        assert_eq!(allocation.dimension_count(), 0);
        assert_eq!(allocation.budget(0), None);
        let items: Vec<_> = (0u64..64)
            .map(|key| (key, (Box::new(key), vec![])))
            .collect();
        let address = items.as_ptr();
        let first_address = &*items.first().ok_or("missing first item")?.1.0 as *const u64;
        let cancelled = allocation.prepare_batch(items)?.cancel();
        assert_eq!(cancelled.items.as_ptr(), address);
        assert!(allocation.is_empty());
        allocation.prepare_batch(cancelled.items)?.commit();
        assert_eq!(allocation.len(), 64);
        assert_eq!(
            &**allocation.get(&0).ok_or("missing first payload")? as *const u64,
            first_address
        );
        for key in 0u64..64 {
            assert_eq!(allocation.get(&key).map(|value| **value), Some(key));
        }
        let duplicate = vec![(64, (Box::new(64), vec![])), (1, (Box::new(99), vec![]))];
        let address = duplicate.as_ptr();
        let refused = allocation
            .prepare_batch(duplicate)
            .err()
            .ok_or("retained duplicate admitted")?;
        assert_eq!(refused.reason, Some(TypedAllocationError::DuplicateKey));
        assert_eq!(refused.entry, Some(1));
        assert_eq!(refused.items.as_ptr(), address);
        assert_eq!(allocation.len(), 64);
        assert!(allocation.get(&64).is_none());
        let duplicate = vec![(64, (Box::new(64), vec![])), (64, (Box::new(99), vec![]))];
        let refused = allocation
            .prepare_batch(duplicate)
            .err()
            .ok_or("pending duplicate admitted")?;
        assert_eq!(refused.reason, Some(TypedAllocationError::DuplicateKey));
        assert_eq!(refused.entry, Some(1));
        assert_eq!(allocation.len(), 64);
        for charges in [vec![0], vec![1], vec![u64::MAX]] {
            let refused = allocation
                .prepare(64, Box::new(64), charges)
                .err()
                .ok_or("resource charges admitted without a schema")?;
            assert_eq!(refused.reason, Some(TypedAllocationError::WidthMismatch));
            assert_eq!(allocation.len(), 64);
        }
        allocation.prepare(64, Box::new(64), vec![])?.commit();
        allocation.prepare_batch(vec![])?.commit();
        let sealed = allocation.seal();
        assert_eq!(sealed.len(), 65);
        assert_eq!(sealed.budget(0), None);
        assert_eq!(sealed.get(&64).map(|value| **value), Some(64));
        // Domain cost zero remains distinct from positive unit membership.
        let mut lod = TypedAllocation::try_new(&vec![2, 0], UnrestrictedAllocation)?;
        lod.prepare_batch(vec![(1u64, (7u64, vec![1, 0])), (2, (9, vec![1, 0]))])?
            .commit();
        assert_eq!(lod.len(), 2);
        assert_eq!(lod.budget(0), Some((2, 2)));
        assert_eq!(lod.budget(1), Some((0, 0)));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn complete_batch_preserves_owned_order_and_commits_every_charge()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut allocation = TypedAllocation::try_new(&vec![3, 6, 9], UnrestrictedAllocation)?;
        let first = Box::new(7u64);
        let first_address = &*first as *const u64;
        let second = Box::new(99u64);
        let second_address = &*second as *const u64;
        let items = vec![
            (ByteKey::from_bytes(vec![]), (first, vec![1, 0, 3])),
            (ByteKey::from_bytes(vec![0, 255]), (second, vec![1, 6, 6])),
        ];
        let address = items.as_ptr();
        let cancelled = allocation.prepare_batch(items)?.cancel();
        assert_eq!(cancelled.items.as_ptr(), address);
        assert_eq!(cancelled.reason, None);
        assert_eq!(allocation.len(), 0);
        allocation.prepare_batch(cancelled.items)?.commit();
        assert_eq!(allocation.len(), 2);
        assert_eq!(allocation.budget(0), Some((3, 2)));
        assert_eq!(allocation.budget(1), Some((6, 6)));
        assert_eq!(allocation.budget(2), Some((9, 9)));
        assert_eq!(
            &**allocation
                .get_query(&(&[][..]))
                .ok_or("missing first admitted payload")? as *const u64,
            first_address
        );
        assert_eq!(
            &**allocation
                .get_query(&(&[0, 255][..]))
                .ok_or("missing second admitted payload")? as *const u64,
            second_address
        );
        let sealed = allocation.seal();
        assert_eq!(
            **sealed
                .get_query(&(&[0, 255][..]))
                .ok_or("missing sealed payload")?,
            99
        );
        assert_eq!(sealed.budget(2), Some((9, 9)));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn duplicate_and_late_content_refusals_return_the_whole_original_batch()
    -> Result<(), Box<dyn std::error::Error>> {
        for refused_entry in 0..3 {
            let mut allocation = TypedAllocation::try_new(&vec![8, 20], UnrestrictedAllocation)?;
            let mut items: Vec<_> = (0u64..3)
                .map(|key| (key, (Box::new(key), vec![1, 1])))
                .collect();
            items
                .get_mut(refused_entry)
                .ok_or("missing refusal fixture item")?
                .1
                .1 = vec![1];
            let address = items.as_ptr();
            let payload_address =
                &*items.first().ok_or("missing original first item")?.1.0 as *const u64;
            let refused = allocation
                .prepare_batch(items)
                .err()
                .ok_or("wrong-width batch admitted")?;
            assert_eq!(refused.reason, Some(TypedAllocationError::WidthMismatch));
            assert_eq!(refused.entry, Some(refused_entry));
            assert_eq!(refused.items.as_ptr(), address);
            assert_eq!(
                &*refused
                    .items
                    .first()
                    .ok_or("missing returned first item")?
                    .1
                    .0 as *const u64,
                payload_address
            );
            assert_eq!(allocation.len(), 0);
            assert_eq!(allocation.budget(0), Some((8, 0)));
        }
        let mut allocation = TypedAllocation::try_new(&vec![8, 20], UnrestrictedAllocation)?;
        let items = vec![
            (ByteKey::from_bytes(vec![]), (vec![7u8], vec![1, 1])),
            (ByteKey::from_bytes(vec![1]), (vec![2], vec![1, 1])),
            (ByteKey::from_bytes(vec![]), (vec![99], vec![1, 1])),
        ];
        let address = items.as_ptr();
        let refused = allocation
            .prepare_batch(items)
            .err()
            .ok_or("duplicate batch admitted")?;
        assert_eq!(refused.reason, Some(TypedAllocationError::DuplicateKey));
        assert_eq!(refused.entry, Some(2));
        assert_eq!(refused.items.as_ptr(), address);
        assert_eq!(allocation.len(), 0);
        assert_eq!(allocation.budget(1), Some((20, 0)));
        allocation
            .prepare(ByteKey::from_bytes(vec![]), vec![7u8], vec![1, 1])?
            .commit();
        let refused = allocation
            .prepare_batch(refused.items)
            .err()
            .ok_or("retained duplicate admitted")?;
        assert_eq!(refused.reason, Some(TypedAllocationError::DuplicateKey));
        assert_eq!(refused.entry, Some(0));
        assert_eq!(allocation.get_query(&(&[][..])), Some(&vec![7]));
        assert_eq!(allocation.budget(0), Some((8, 1)));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn each_dimension_and_overflow_pressure_refuses_before_publication()
    -> Result<(), Box<dyn std::error::Error>> {
        for (capacities, dimension) in [(vec![1, 8, 8], 0), (vec![8, 1, 8], 1), (vec![8, 8, 1], 2)]
        {
            let mut allocation = TypedAllocation::try_new(&capacities, UnrestrictedAllocation)?;
            let items = vec![
                (1u64, (vec![7u8], vec![1, 1, 1])),
                (2, (vec![99], vec![1, 1, 1])),
            ];
            let address = items.as_ptr();
            let refused = allocation
                .prepare_batch(items)
                .err()
                .ok_or("over-capacity batch admitted")?;
            assert_eq!(refused.reason, Some(TypedAllocationError::Capacity));
            assert_eq!(
                (refused.entry, refused.dimension),
                (Some(1), Some(dimension))
            );
            assert_eq!(refused.items.as_ptr(), address);
            assert_eq!(allocation.len(), 0);
            for (dimension, capacity) in capacities.iter().copied().enumerate() {
                assert_eq!(allocation.budget(dimension), Some((capacity, 0)));
            }
        }
        let mut allocation = TypedAllocation::try_new(&vec![2, u64::MAX], UnrestrictedAllocation)?;
        let refused = allocation
            .prepare_batch(vec![
                (1u64, (7u64, vec![1, u64::MAX])),
                (2, (99, vec![1, 1])),
            ])
            .err()
            .ok_or("overflowing charge batch admitted")?;
        assert_eq!((refused.entry, refused.dimension), (Some(1), Some(1)));
        assert_eq!(allocation.budget(1), Some((u64::MAX, 0)));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn empty_and_dropped_batches_preserve_owners_and_diagnostics_exclude_payloads()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut allocation = TypedAllocation::try_new(&vec![2, 4], UnrestrictedAllocation)?;
        allocation
            .prepare_batch(Vec::<(u64, (Vec<u8>, Vec<u64>))>::new())?
            .commit();
        assert!(allocation.is_empty());
        let prepared =
            allocation.prepare_batch(vec![(1u64, (b"secret-payload".to_vec(), vec![1, 1]))])?;
        assert!(!format!("{prepared:?}").contains("secret-payload"));
        drop(prepared);
        assert!(allocation.is_empty());
        let refused = allocation
            .prepare_batch(vec![(1, (b"secret-payload".to_vec(), vec![1, 8]))])
            .err()
            .ok_or("over-capacity batch admitted")?;
        assert!(!format!("{refused:?} {refused}").contains("secret-payload"));
        assert_eq!(allocation.budget(1), Some((4, 0)));
        Ok(())
    }
}

#[test]
fn owned_buffer_transfer_moves_noncopy_payloads_in_authored_order() {
    use automation_structures::Buffer;
    let values: Vec<_> = (0..4096).map(Box::new).collect();
    let pointers: Vec<_> = values.iter().map(|value| &**value as *const i32).collect();
    let buffer = Buffer::from_values(values);
    assert_eq!(buffer.capacity(), 4096);
    for (position, value) in buffer.into_iter().enumerate() {
        assert_eq!(i32::try_from(position), Ok(*value));
        assert_eq!(pointers.get(position), Some(&(&*value as *const i32)));
    }
}

mod reduction_rows {
    use automation_structures::{
        CheckedSignedAdd, RecordRefusal, ReductionColumns, ReductionRowError,
    };

    fn observations(
        owner: &ReductionColumns<CheckedSignedAdd>,
    ) -> Vec<(Option<usize>, Option<i64>)> {
        (0..owner.column_count())
            .map(|column| (owner.column_processed(column), owner.column_result(column)))
            .collect()
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn complete_row_and_cancellation_preserve_column_owners()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut empty = ReductionColumns::<CheckedSignedAdd>::try_new(&vec![], 0)?;
        empty.prepare_row(&vec![])?.commit();
        assert_eq!(empty.column_count(), 0);
        assert_eq!(empty.column_result(0), None);
        let mut owner = ReductionColumns::try_new(&vec![CheckedSignedAdd; 3], 2)?;
        assert_eq!(observations(&owner), vec![(Some(0), Some(0)); 3]);
        owner.prepare_row(&vec![7, -4, 8])?.cancel();
        assert_eq!(observations(&owner), vec![(Some(0), Some(0)); 3]);
        drop(owner.prepare_row(&vec![7, -4, 8])?);
        assert_eq!(observations(&owner), vec![(Some(0), Some(0)); 3]);
        let mut inputs = vec![7, -4, 8];
        let prepared = owner.prepare_row(&inputs)?;
        *inputs.first_mut().ok_or("missing mutable input fixture")? = 99;
        prepared.commit();
        assert_eq!(
            observations(&owner),
            vec![(Some(1), Some(7)), (Some(1), Some(-4)), (Some(1), Some(8))]
        );
        owner.prepare_row(&vec![-4, 4, -8])?.commit();
        assert_eq!(
            observations(&owner),
            vec![(Some(2), Some(3)), (Some(2), Some(0)), (Some(2), Some(0))]
        );
        assert_eq!(owner.column_processed(3), None);
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn any_column_or_width_refusal_leaves_the_complete_row_unchanged()
    -> Result<(), Box<dyn std::error::Error>> {
        for refused in 0..3 {
            let mut owner = ReductionColumns::try_new(&vec![CheckedSignedAdd; 3], 3)?;
            let mut first = vec![7, -4, 8];
            *first
                .get_mut(refused)
                .ok_or("missing refusal column fixture")? = i64::MAX;
            owner.prepare_row(&first)?.commit();
            let before = observations(&owner);
            assert!(
                matches!(owner.prepare_row(&vec![1, 1, 1]), Err(ReductionRowError::Column {
                column, reason: RecordRefusal::Domain }) if column == refused)
            );
            assert_eq!(observations(&owner), before);
            assert!(matches!(
                owner.prepare_row(&vec![1, 1]),
                Err(ReductionRowError::WidthMismatch)
            ));
            assert_eq!(observations(&owner), before);
        }
        let mut owner = ReductionColumns::try_new(&vec![CheckedSignedAdd; 3], 1)?;
        owner.prepare_row(&vec![7, -4, 8])?.commit();
        let before = observations(&owner);
        assert!(matches!(
            owner.prepare_row(&vec![1, 1, 1]),
            Err(ReductionRowError::Column {
                column: 0,
                reason: RecordRefusal::Capacity
            })
        ));
        assert_eq!(observations(&owner), before);
        let mut zero = ReductionColumns::try_new(&vec![CheckedSignedAdd; 3], 0)?;
        assert!(matches!(
            zero.prepare_row(&vec![0, 0, 0]),
            Err(ReductionRowError::Column {
                column: 0,
                reason: RecordRefusal::Capacity
            })
        ));
        assert_eq!(observations(&zero), vec![(Some(0), Some(0)); 3]);
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn nullable_columns_share_row_progress_without_conflating_contribution_counts()
    -> Result<(), Box<dyn std::error::Error>> {
        use automation_structures::{
            CheckedSignedSumCount,
            NullableSigned::{Missing, Value},
            SignedSumCount,
        };
        let mut owner = ReductionColumns::try_new(&vec![CheckedSignedSumCount; 2], 3)?;
        for items in [
            vec![Value(3), Missing],
            vec![Missing, Value(5)],
            vec![Value(-1), Value(0)],
        ] {
            owner.prepare_row(&items)?.commit();
        }
        assert_eq!(owner.column_processed(0), Some(3));
        assert_eq!(owner.column_processed(1), Some(3));
        assert_eq!(
            owner.column_result(0),
            Some(SignedSumCount { sum: 2, count: 2 })
        );
        assert_eq!(
            owner.column_result(1),
            Some(SignedSumCount { sum: 5, count: 2 })
        );
        Ok(())
    }
}

mod graph_owner_queries {
    use automation_structures::{
        AdjacencyBuildError, AllEdges, EdgeDirection, EdgeHandleDomain, PositionalEdgeHandles,
        RegistryPredicate, RelationshipGraph, RelationshipGraphError, ValueEq,
    };
    use vstd::prelude::*;
    verus! {
        struct MinWeight { minimum: u64 }
        impl RegistryPredicate<(usize, usize, u64), ()> for MinWeight {
            open spec fn selected(&self, edge: (usize, usize, u64), _value: ()) -> bool {
                edge.2 >= self.minimum
            }
            fn test(&self, edge: &(usize, usize, u64), _value: &()) -> (selected: bool) {
                edge.2 >= self.minimum
            }
        }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        struct ScopedEdge { scope: u64, position: usize }
        impl ValueEq for ScopedEdge {
            fn value_eq(&self, other: &Self) -> (equal: bool) {
                self.scope == other.scope && self.position == other.position
            }
        }
        struct ScopedEdges { scope: u64, count: usize }
        impl EdgeHandleDomain<ScopedEdge> for ScopedEdges {
            open spec fn domain_len(&self) -> nat { self.count as nat }
            open spec fn handle_spec(&self, original: usize) -> ScopedEdge {
                ScopedEdge { scope: self.scope, position: original }
            }
            open spec fn ordinal_spec(&self, handle: ScopedEdge) -> Option<usize> {
                if handle.position < self.count { Some(handle.position) } else { None }
            }
            fn len(&self) -> (length: usize) { self.count }
            fn handle(&self, original: usize) -> (handle: ScopedEdge) {
                ScopedEdge { scope: self.scope, position: original }
            }
            fn ordinal(&self, handle: &ScopedEdge) -> (original: Option<usize>) {
                if handle.position < self.count { Some(handle.position) } else { None }
            }
            proof fn correspondence(&self, original: usize) {}
        }
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn materialized_adjacency_preserves_filtered_parallel_records_and_both_inverses()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut graph = RelationshipGraph::new(4, 10);
        for (source, destination, weight) in [(0, 2, 7), (0, 1, 3), (0, 2, 9), (3, 0, 8), (2, 3, 0)]
        {
            assert_eq!(graph.add_edge(source, destination, weight), Ok(true));
        }
        let adjacency = graph
            .materialize(
                ScopedEdges {
                    scope: 17,
                    count: 5,
                },
                MinWeight { minimum: 5 },
            )
            .map_err(|(reason, _, _, _)| reason)?;
        let first = ScopedEdge {
            scope: 17,
            position: 0,
        };
        let parallel = ScopedEdge {
            scope: 17,
            position: 2,
        };
        let reverse = ScopedEdge {
            scope: 17,
            position: 3,
        };
        let excluded = ScopedEdge {
            scope: 17,
            position: 1,
        };
        assert_eq!((adjacency.num_nodes(), adjacency.edge_count()), (4, 5));
        assert_eq!(
            adjacency.incident(0, EdgeDirection::Outgoing),
            Some([first, parallel].as_slice())
        );
        assert_eq!(
            adjacency.incident(3, EdgeDirection::Outgoing),
            Some([reverse].as_slice())
        );
        assert_eq!(
            adjacency.incident(2, EdgeDirection::Incoming),
            Some([first, parallel].as_slice())
        );
        assert_eq!(
            adjacency.incident(0, EdgeDirection::Incoming),
            Some([reverse].as_slice())
        );
        assert_eq!(
            adjacency.incident(1, EdgeDirection::Outgoing),
            Some([].as_slice())
        );
        assert_eq!(
            adjacency.incident(1, EdgeDirection::Incoming),
            Some([].as_slice())
        );
        assert_eq!(adjacency.incident(4, EdgeDirection::Outgoing), None);
        assert_eq!(
            adjacency.incident(usize::MAX, EdgeDirection::Incoming),
            None
        );
        assert_eq!(adjacency.handle_at(0), Some(first));
        assert_eq!(adjacency.handle_at(5), None);
        assert_eq!(adjacency.edge(&first), Some((0, 2, 7)));
        assert_eq!(adjacency.edge(&parallel), Some((0, 2, 9)));
        assert_eq!(adjacency.edge(&excluded), Some((0, 1, 3)));
        assert_eq!(adjacency.rank_of(&first, EdgeDirection::Outgoing), Some(0));
        assert_eq!(
            adjacency.rank_of(&parallel, EdgeDirection::Outgoing),
            Some(1)
        );
        assert_eq!(
            adjacency.rank_of(&reverse, EdgeDirection::Outgoing),
            Some(2)
        );
        assert_eq!(
            adjacency.rank_of(&reverse, EdgeDirection::Incoming),
            Some(0)
        );
        assert_eq!(adjacency.rank_of(&first, EdgeDirection::Incoming), Some(1));
        assert_eq!(
            adjacency.rank_of(&parallel, EdgeDirection::Incoming),
            Some(2)
        );
        assert_eq!(adjacency.rank_of(&excluded, EdgeDirection::Outgoing), None);
        assert_eq!(adjacency.rank_of(&excluded, EdgeDirection::Incoming), None);
        // The decoder deliberately accepts this ordinal. Exact retained equality
        // must reject the other scope rather than alias the authored record.
        let foreign = ScopedEdge {
            scope: 18,
            position: 0,
        };
        assert_eq!(adjacency.edge(&foreign), None);
        assert_eq!(adjacency.rank_of(&foreign, EdgeDirection::Outgoing), None);
        assert_eq!(
            adjacency.edge(&ScopedEdge {
                scope: 17,
                position: usize::MAX
            }),
            None
        );
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn materialized_adjacency_handles_empty_isolated_and_refused_universes()
    -> Result<(), Box<dyn std::error::Error>> {
        let empty = RelationshipGraph::new(0, 0)
            .materialize(PositionalEdgeHandles { count: 0 }, AllEdges)
            .map_err(|(reason, _, _, _)| reason)?;
        assert_eq!((empty.num_nodes(), empty.edge_count()), (0, 0));
        assert_eq!(empty.incident(0, EdgeDirection::Outgoing), None);
        assert_eq!(empty.edge(&0), None);
        let isolated = RelationshipGraph::new(3, 0)
            .materialize(PositionalEdgeHandles { count: 0 }, AllEdges)
            .map_err(|(reason, _, _, _)| reason)?;
        for node in 0..3 {
            assert_eq!(
                isolated.incident(node, EdgeDirection::Outgoing),
                Some([].as_slice())
            );
            assert_eq!(
                isolated.incident(node, EdgeDirection::Incoming),
                Some([].as_slice())
            );
        }
        let mut graph = RelationshipGraph::new(2, 9);
        assert_eq!(graph.add_edge(0, 1, 7), Ok(true));
        let (reason, returned, domain, predicate) = graph
            .materialize(PositionalEdgeHandles { count: 0 }, MinWeight { minimum: 5 })
            .err()
            .ok_or("unrepresentable handle domain was admitted")?;
        assert_eq!(reason, AdjacencyBuildError::HandleDomain);
        assert_eq!(
            (
                returned.num_nodes(),
                returned.max_weight(),
                returned.edge_count()
            ),
            (2, 9, 1)
        );
        assert_eq!(returned.edge(0), Some((0, 1, 7)));
        assert_eq!((domain.count, predicate.minimum), (0, 5));
        let (reason, returned, domain, _) = RelationshipGraph::new(usize::MAX, 11)
            .materialize(PositionalEdgeHandles { count: 0 }, AllEdges)
            .err()
            .ok_or("unrepresentable offset length was admitted")?;
        assert_eq!(reason, AdjacencyBuildError::NodeOffsetOverflow);
        assert_eq!(
            (
                returned.num_nodes(),
                returned.max_weight(),
                returned.edge_count()
            ),
            (usize::MAX, 11, 0)
        );
        assert_eq!(domain.count, 0);
        Ok(())
    }

    #[test]
    fn incident_queries_and_frozen_view_use_the_same_weighted_edge_owner() {
        let mut graph = RelationshipGraph::new(4, 10);
        let all = MinWeight { minimum: 0 };
        let selected = MinWeight { minimum: 5 };
        assert_eq!(
            graph.filtered_degree(0, EdgeDirection::Outgoing, &all),
            Ok(0)
        );
        assert!(!graph.contains(0, 2));
        for edge in [(0, 2, 7), (0, 1, 3), (0, 2, 9), (3, 0, 8), (2, 3, 0)] {
            assert_eq!(graph.add_edge(edge.0, edge.1, edge.2), Ok(true));
        }
        assert_eq!(graph.add_edge(0, 2, 7), Ok(false));
        {
            let view = graph.frozen_adjacency();
            assert_eq!(view.edge_count(), 5);
            assert_eq!(view.edge(0), Some((0, 2, 7)));
            assert_eq!(view.edge(1), Some((0, 1, 3)));
            assert_eq!(view.edge(4), Some((2, 3, 0)));
            assert_eq!(view.edge(5), None);
            assert_eq!(
                view.filtered_degree(0, EdgeDirection::Outgoing, &selected),
                Ok(2)
            );
            assert_eq!(
                view.filtered_degree(0, EdgeDirection::Outgoing, &all),
                Ok(3)
            );
            assert_eq!(
                view.filtered_degree(0, EdgeDirection::Incoming, &selected),
                Ok(1)
            );
            assert_eq!(
                view.filtered_degree(3, EdgeDirection::Incoming, &all),
                Ok(1)
            );
            assert_eq!(
                view.filtered_degree(4, EdgeDirection::Outgoing, &all),
                Err(RelationshipGraphError::NodeOutOfRange)
            );
        }
        assert!(graph.contains(0, 2));
        assert!(!graph.contains(2, 0));
        graph.remove_edges(0, 2);
        let view = graph.frozen_adjacency();
        assert_eq!(view.edge_count(), 3);
        assert_eq!(view.edge(0), Some((0, 1, 3)));
        assert_eq!(view.edge(1), Some((3, 0, 8)));
        assert_eq!(view.edge(2), Some((2, 3, 0)));
        assert_eq!(
            view.filtered_degree(0, EdgeDirection::Outgoing, &selected),
            Ok(0)
        );
        assert_eq!(
            view.filtered_degree(0, EdgeDirection::Outgoing, &all),
            Ok(1)
        );
        assert!(!graph.contains(0, 2));
    }
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn sampler_observes_the_full_usize_cardinality_bound()
-> Result<(), automation_structures::SamplerError> {
    let mut sampler = automation_structures::Sampler::new(vec![3, 1], usize::MAX);
    assert_eq!(sampler.sample_size(), usize::MAX);
    assert_eq!(sampler.selected_len(), 0);
    sampler.sample(0)?;
    assert_eq!(sampler.selected_len(), 1);
    sampler.sample(1)?;
    assert_eq!(sampler.selected_len(), 2);
    assert_eq!(sampler.sample_size(), usize::MAX);
    Ok(())
}

mod buffer_size_queries {
    use automation_structures::{Buffer, BufferSizeError, BufferSizeProjection};
    use vstd::prelude::*;
    verus! {
        struct EncodedSize;
        impl BufferSizeProjection<usize> for EncodedSize {
            open spec fn size_spec(&self, value: usize) -> usize { value }
            fn size(&self, value: &usize) -> (size: usize) { *value }
        }
    }

    #[test]
    fn buffer_projection_observes_empty_zero_and_fifo_changes_without_retaining_a_total() {
        let mut buffer = Buffer::new(3);
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(0));
        assert_eq!(buffer.push(0), Ok(()));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(0));
        assert_eq!(buffer.push(7), Ok(()));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(7));
        assert_eq!(buffer.push(11), Ok(()));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(18));
        assert_eq!(buffer.as_ref(), &[0, 7, 11]);
        assert_eq!(buffer.pop(), Some(0));
        assert_eq!(buffer.pop(), Some(7));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(11));
    }

    #[test]
    fn buffer_projection_refuses_exact_overflow_and_preserves_contents() {
        let mut buffer = Buffer::new(3);
        assert_eq!(buffer.push(usize::MAX), Ok(()));
        assert_eq!(buffer.push(0), Ok(()));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(usize::MAX));
        assert_eq!(buffer.push(1), Ok(()));
        assert_eq!(
            buffer.projected_size(&EncodedSize),
            Err(BufferSizeError::Overflow)
        );
        assert_eq!(buffer.len(), 3);
        assert_eq!(buffer.as_ref(), &[usize::MAX, 0, 1]);
        assert_eq!(buffer.pop(), Some(usize::MAX));
        assert_eq!(buffer.projected_size(&EncodedSize), Ok(1));
    }
}

mod projected_reduction {
    use automation_structures::{
        CheckedSignedAdd, IncrementalReduction, RecordRefusal, ReductionProjection,
    };
    use vstd::prelude::*;
    verus! {
        struct SignedInputs { values: Vec<i64> }
        impl ReductionProjection<CheckedSignedAdd> for SignedInputs {
            open spec fn domain_len(&self) -> nat { self.values@.len() }
            open spec fn item_spec(&self, position: int) -> i64 { self.values@[position] }
            fn len(&self) -> (length: usize) { self.values.len() }
            #[expect(clippy::indexing_slicing, reason = "ReductionProjection::item requires position below domain_len, the actual values length")]
            fn item(&self, position: usize) -> (item: i64) { self.values[position] }
        }
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn projected_fold_preserves_full_order_and_the_first_refused_prefix()
    -> Result<(), Box<dyn std::error::Error>> {
        let empty = SignedInputs { values: vec![] };
        let fold = IncrementalReduction::try_from_projection(&empty, CheckedSignedAdd)
            .map_err(|(reason, _fold)| reason)?;
        assert_eq!((fold.processed_len(), fold.result()), (0, 0));
        let full = SignedInputs {
            values: vec![7, -4, 8],
        };
        let fold = IncrementalReduction::try_from_projection(&full, CheckedSignedAdd)
            .map_err(|(reason, _fold)| reason)?;
        assert_eq!((fold.processed_len(), fold.result()), (3, 11));
        let refused = SignedInputs {
            values: vec![i64::MAX, 1, -1],
        };
        let (reason, fold) = IncrementalReduction::try_from_projection(&refused, CheckedSignedAdd)
            .err()
            .ok_or("undefined combination admitted")?;
        assert_eq!(reason, RecordRefusal::Domain);
        assert_eq!((fold.processed_len(), fold.result()), (1, i64::MAX));
        assert_eq!(refused.values, [i64::MAX, 1, -1]);
        let different_order = SignedInputs {
            values: vec![i64::MAX, -1, 1],
        };
        let fold = IncrementalReduction::try_from_projection(&different_order, CheckedSignedAdd)
            .map_err(|(reason, _fold)| reason)?;
        assert_eq!((fold.processed_len(), fold.result()), (3, i64::MAX));
        Ok(())
    }
}

mod owner_queries {
    use automation_structures::{RegistryInsertError, RegistryPredicate, ResourceRegistry};
    use vstd::prelude::*;
    verus! {
        struct AtLeast { minimum: u64 }
        impl RegistryPredicate<u64, u64> for AtLeast {
            open spec fn selected(&self, _key: u64, value: u64) -> bool { value >= self.minimum }
            fn test(&self, _key: &u64, value: &u64) -> (selected: bool) { *value >= self.minimum }
        }
    }

    #[test]
    fn registry_queries_use_the_retained_mapping_after_insert_replace_and_remove() {
        let mut registry = ResourceRegistry::new();
        let predicate = AtLeast { minimum: 8 };
        assert_eq!(registry.count_matching(&predicate), 0);
        assert!(!registry.any_matching(&predicate));
        assert!(registry.all_matching(&predicate));
        assert_eq!(registry.try_insert_unique(1, 7), Ok(0));
        assert_eq!(registry.try_insert_unique(2, 9), Ok(1));
        assert_eq!(
            registry.try_insert_unique(1, 99),
            Err((RegistryInsertError::DuplicateKey, 1, 99))
        );
        assert_eq!(registry.get(1), Some(7));
        assert_eq!(registry.entry(0), Some((1, 7)));
        assert_eq!(registry.len(), 2);
        assert_eq!(registry.count_matching(&predicate), 1);
        assert!(registry.any_matching(&predicate));
        assert!(!registry.all_matching(&predicate));
        assert_eq!(registry.insert(1, 8), Some(7));
        assert_eq!(registry.count_matching(&predicate), 2);
        assert!(registry.all_matching(&predicate));
        assert_eq!(registry.remove(2), Some(9));
        assert_eq!(registry.count_matching(&predicate), 1);
    }

    #[cfg(feature = "proof-api")]
    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn indexed_unique_insertion_returns_owned_payload_without_replacing_the_old_value()
    -> Result<(), Box<dyn std::error::Error>> {
        use automation_structures::primitives::resource_registry::{
            ByteKey, ResourceRegistry as Owner,
        };
        let mut owner = Owner::new_indexed();
        assert!(
            owner
                .try_insert_unique(ByteKey::from_bytes(b"exact".to_vec()), vec![7])
                .is_ok()
        );
        let duplicate = ByteKey::from_bytes(b"exact".to_vec());
        let (reason, returned_key, returned_value) = owner
            .try_insert_unique(duplicate, vec![99])
            .err()
            .ok_or("existing identity admitted")?;
        assert_eq!(reason, RegistryInsertError::DuplicateKey);
        assert_eq!(returned_key.as_bytes(), b"exact");
        assert_eq!(returned_value, vec![99]);
        assert_eq!(owner.lookup_query(&&b"exact"[..]), Some(&vec![7]));
        Ok(())
    }
}

#[cfg(feature = "proof-api")]
mod registry_byte_keys {
    use automation_structures::primitives::resource_registry::{ByteKey, ResourceRegistry};

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn equal_allocations_replace_and_borrowed_queries_do_not_escape()
    -> Result<(), Box<dyn std::error::Error>> {
        let encoded = vec![1u8, 0, 2];
        let allocation = encoded.as_ptr();
        let key = ByteKey::from_bytes(encoded);
        assert_eq!(key.as_bytes().as_ptr(), allocation);
        let mut registry = ResourceRegistry::<ByteKey, Vec<u64>>::new();
        registry.register_key(key, vec![11, 12]);
        registry.register_key(ByteKey::from_bytes(vec![9]), vec![31, 32]);
        let storage = registry.entries.as_ptr();
        let capacity = registry.entries.capacity();
        let replacement = ByteKey::from_bytes(vec![1u8, 0, 2]);
        assert_ne!(replacement.as_bytes().as_ptr(), allocation);
        registry.register_key(replacement, vec![21, 22]);
        assert_eq!(registry.entries.len(), 2);
        let first = registry
            .entries
            .first()
            .ok_or("missing surviving first entry")?;
        let second = registry
            .entries
            .get(1)
            .ok_or("missing replaced second entry")?;
        assert_eq!(first.0.as_bytes(), &[9]);
        assert_eq!(first.1, vec![31, 32]);
        assert_eq!(second.0.as_bytes(), &[1, 0, 2]);
        assert_eq!(registry.entries.as_ptr(), storage);
        assert_eq!(registry.entries.capacity(), capacity);
        let value = {
            let temporary_probe = [99, 1, 0, 2, 88];
            registry
                .lookup_query(
                    &temporary_probe
                        .get(1..4)
                        .ok_or("missing borrowed probe range")?,
                )
                .ok_or("missing borrowed payload")?
        };
        assert_eq!(value, &[21, 22]);
        assert!(std::ptr::eq(value, &second.1));
        assert!(registry.lookup_query(&&[1u8, 0][..]).is_none());
        registry.deregister_key(ByteKey::from_bytes(vec![1u8, 0, 2]));
        assert_eq!(registry.entries.len(), 1);
        assert_eq!(
            registry
                .entries
                .first()
                .ok_or("missing final survivor")?
                .0
                .as_bytes(),
            &[9]
        );
        assert_eq!(registry.entries.as_ptr(), storage);
        Ok(())
    }

    #[test]
    fn exact_byte_identity_distinguishes_lengths_prefixes_and_embedded_zeros() {
        let cases: &[&[u8]] = &[
            &[],
            &[0],
            &[0, 0],
            &[1],
            &[1, 0],
            &[1, 0, 1],
            &[1, 1, 0],
            &[255, 0],
        ];
        let mut registry = ResourceRegistry::<ByteKey, u64>::new();
        for (id, bytes) in cases.iter().enumerate() {
            registry.register_key(ByteKey::from_bytes(bytes.to_vec()), id as u64);
        }
        assert_eq!(registry.entries.len(), cases.len());
        let storage = registry.entries.as_ptr();
        for _ in 0..128 {
            for (id, bytes) in cases.iter().enumerate() {
                assert_eq!(registry.lookup_query(bytes), Some(&(id as u64)));
            }
            assert!(registry.lookup_query(&&[2u8][..]).is_none());
        }
        assert_eq!(registry.entries.as_ptr(), storage);
        registry.register_key(ByteKey::from_bytes(vec![1, 0]), 99);
        assert_eq!(registry.entries.len(), cases.len());
        for (id, bytes) in cases.iter().enumerate() {
            let expected = if *bytes == [1, 0] { 99 } else { id as u64 };
            assert_eq!(registry.lookup_query(bytes), Some(&expected));
        }
    }
}

#[cfg(feature = "proof-api")]
mod registry_owned {

    use automation_structures::primitives::resource_registry::{RegistryKey, ResourceRegistry};
    use vstd::prelude::*;

    verus! {
    struct OwnedKey { code: u64 }

    impl RegistryKey for OwnedKey {
        fn value_eq(&self, other: &Self) -> (equal: bool)
            ensures equal == (*self == *other),
        {
            self.code == other.code
        }
    }
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn owned_registry_borrows_and_preserves_exact_replacement_order()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut registry = ResourceRegistry::<OwnedKey, Vec<u64>>::new();
        registry.register(OwnedKey { code: 7 }, vec![11, 12]);
        registry.register(OwnedKey { code: 8 }, vec![21, 22]);
        registry.register(OwnedKey { code: 9 }, vec![31, 32]);
        let borrowed = registry
            .lookup_ref(&OwnedKey { code: 8 })
            .ok_or("missing borrowed payload")?;
        assert!(std::ptr::eq(
            borrowed,
            &registry.entries.get(1).ok_or("missing borrowed entry")?.1
        ));
        assert_eq!(borrowed, &[21, 22]);
        assert!(registry.lookup_ref(&OwnedKey { code: 99 }).is_none());
        let storage = registry.entries.as_ptr();
        let capacity = registry.entries.capacity();

        registry.register(OwnedKey { code: 8 }, vec![41, 42]);
        assert_eq!(registry.entries.as_ptr(), storage);
        assert_eq!(registry.entries.capacity(), capacity);
        let observed: Vec<_> = registry
            .entries
            .iter()
            .map(|(k, v)| (k.code, v.as_slice()))
            .collect();
        assert_eq!(
            observed,
            vec![(7, &[11, 12][..]), (9, &[31, 32][..]), (8, &[41, 42][..])]
        );

        registry.deregister(OwnedKey { code: 9 });
        assert_eq!(registry.entries.as_ptr(), storage);
        assert_eq!(registry.entries.capacity(), capacity);
        let observed: Vec<_> = registry
            .entries
            .iter()
            .map(|(k, v)| (k.code, v.as_slice()))
            .collect();
        assert_eq!(observed, vec![(7, &[11, 12][..]), (8, &[41, 42][..])]);
        assert!(registry.lookup_ref(&OwnedKey { code: 9 }).is_none());
        let removed = registry.deregister_at(1);
        assert_eq!(
            removed.map(|(key, value)| (key.code, value)),
            Some((8, vec![41, 42]))
        );
        assert_eq!(
            registry.entries.first().ok_or("missing final survivor")?.1,
            vec![11, 12]
        );
        Ok(())
    }

    #[test]
    fn repeated_replacement_retains_the_registry_allocation() {
        let mut registry = ResourceRegistry::<u64, u64>::new();
        registry.register(7, 11);
        registry.register(8, 21);
        registry.register(9, 31);
        let storage = registry.entries.as_ptr();
        let capacity = registry.entries.capacity();
        for value in 0..4096 {
            registry.register(8, value);
            assert_eq!(registry.entries.as_ptr(), storage);
            assert_eq!(registry.entries.capacity(), capacity);
            assert_eq!(registry.entries, vec![(7, 11), (9, 31), (8, value)]);
            assert_eq!(registry.lookup(8), Some(value));
            assert_eq!(registry.lookup(7), Some(11));
            assert_eq!(registry.lookup(9), Some(31));
            assert_eq!(registry.lookup(99), None);
        }
    }
}

use automation_structures::{
    Accumulator, ActuationError, ActuationPass, AllocationSnapshot, AllocationSnapshotError,
    AuditRecord, AuditSink, BacktrackingBuildError, BacktrackingError, BacktrackingTraversal,
    Bisection, Budget, BudgetError, Buffer, CompetitiveSelectionError, CompetitiveSelectionHard,
    CompetitiveSelectionHardExclusive, CompetitiveSelectionRanked, CompetitiveSelectionSoft,
    ConvergenceBuildError, ConvergenceError, ConvergenceGovernor, ConvergencePhase,
    ConvergenceState, Counter, Cursor, CursorError, EquivalenceClass, EquivalenceClassError,
    FederatedBudget, ForkJoin, ForkJoinPhase, Marker, PropagationBuildError, PropagationError,
    PropagationPass, QualityHierarchy, QualityHierarchyError, RateLimit, RateLimitError, Reduction,
    ReductionError, RelationshipGraph, RelationshipGraphError, ResourceRegistry, Sampler,
    SamplerError, SelectThenActuate, SelectThenActuateBuildError, SelectThenActuateError,
    Sequential, Signal, SignalError, StepGraph, StepGraphBuildError, StepState, StreamGraph,
    TraversalEngine, TraversalError, WorkerState, projection_consistent, strictly_before,
};

#[test]
fn checked_budget_api_preserves_guards_and_observations() {
    let mut budget = Budget::new(10);

    assert_eq!(budget.capacity(), 10);
    assert_eq!(budget.available(), 10);
    assert!(budget.try_reserve(4));
    assert!(!budget.try_allocate(7));
    assert_eq!(
        budget.commit_reservation(5),
        Err(BudgetError::AmountExceedsReservation)
    );
    assert_eq!(budget.commit_reservation(4), Ok(()));
    assert_eq!(budget.mark_eviction(3), Ok(()));
    assert_eq!(budget.pending_eviction(), 3);
    assert_eq!(
        budget.complete_eviction(4),
        Err(BudgetError::AmountExceedsPendingEviction)
    );
    assert_eq!(budget.complete_eviction(3), Ok(()));
    assert_eq!(budget.allocated(), 1);
    assert_eq!(budget.reserved(), 0);
    assert_eq!(budget.release(2), Err(BudgetError::AmountExceedsAllocation));
    assert_eq!(budget.release(1), Ok(()));
    assert_eq!(budget.available(), 10);
}

#[test]
fn checked_cursor_api_refuses_regression() {
    let mut cursor = Cursor::new(3);

    assert_eq!(cursor.advance_to(2), Err(CursorError::Regression));
    assert_eq!(cursor.position(), 3);
    assert_eq!(cursor.advance_to(5), Ok(()));
    assert_eq!(cursor.position(), 5);
    assert_eq!(cursor.advance_to(5), Ok(()));
    assert_eq!(cursor.position(), 5);
}

#[test]
fn checked_registry_returns_prior_values() {
    let mut registry = ResourceRegistry::new();
    assert!(registry.is_empty());
    assert_eq!(registry.insert(4, 10), None);
    assert_eq!(registry.insert(4, 20), Some(10));
    assert_eq!(registry.get(4), Some(20));
    assert_eq!(registry.entry(0), Some((4, 20)));
    assert_eq!(registry.entry(1), None);
    assert_eq!(registry.remove(4), Some(20));
    assert_eq!(registry.remove(4), None);
    assert_eq!(registry.len(), 0);
}

#[test]
fn checked_registry_preserves_deterministic_survivor_order() {
    let mut registry = ResourceRegistry::new();
    assert_eq!(registry.insert(1, 10), None);
    assert_eq!(registry.insert(2, 20), None);
    assert_eq!(registry.insert(3, 30), None);
    assert_eq!(registry.insert(2, 21), Some(20));
    assert_eq!(registry.entry(0), Some((1, 10)));
    assert_eq!(registry.entry(1), Some((3, 30)));
    assert_eq!(registry.entry(2), Some((2, 21)));
    assert_eq!(registry.remove(1), Some(10));
    assert_eq!(registry.entry(0), Some((3, 30)));
    assert_eq!(registry.entry(1), Some((2, 21)));
}

#[cfg(feature = "proof-api")]
#[test]
fn proof_registry_instantiates_with_typed_composition_keys() {
    use automation_structures::primitives::resource_registry::ResourceRegistry as ProofRegistry;

    let mut registry: ProofRegistry<(usize, usize, u64), ()> = ProofRegistry::new();
    registry.register((1, 2, 3), ());
    assert_eq!(registry.lookup((1, 2, 3)), Some(()));
    assert_eq!(registry.lookup((1, 2, 4)), None);
}

#[test]
fn checked_audit_sink_bounds_append_and_exposes_immutable_records() {
    let mut sink = AuditSink::new(1);
    assert!(sink.is_empty());
    assert!(sink.try_record(9));
    assert!(!sink.try_record(10));
    assert_eq!(sink.capacity(), 1);
    assert_eq!(sink.len(), 1);
    assert_eq!(sink.last_hash(), 10);
    assert_eq!(
        sink.record(0),
        Some(AuditRecord {
            operation: 9,
            previous_hash: 0,
            hash: 10,
        })
    );
    assert_eq!(sink.record(1), None);
    assert!(sink.validate());
}

#[test]
fn checked_propagation_rejects_disabled_actions() {
    assert!(matches!(
        PropagationPass::new(2, 3, vec![], vec![4]),
        Err(PropagationBuildError::InitialValueOutOfRange)
    ));
    assert!(matches!(
        PropagationPass::new(2, 3, vec![(0, 1)], vec![0]),
        Err(PropagationBuildError::EdgeEndpointOutOfRange)
    ));

    let result = PropagationPass::new(1, 3, vec![(0, 1)], vec![0, 2]);
    assert!(result.is_ok());
    if let Ok(mut pass) = result {
        assert_eq!(pass.num_nodes(), 2);
        assert_eq!(pass.update_node(0), Err(PropagationError::RoundNotRunning));
        assert_eq!(pass.start_round(), Ok(()));
        assert_eq!(
            pass.start_round(),
            Err(PropagationError::RoundAlreadyRunning)
        );
        assert_eq!(pass.update_node(2), Err(PropagationError::NodeOutOfRange));
        assert_eq!(pass.update_node(0), Ok(()));
        assert_eq!(
            pass.update_node(0),
            Err(PropagationError::NodeAlreadyUpdated)
        );
        assert_eq!(pass.end_round(), Err(PropagationError::RoundIncomplete));
        assert_eq!(pass.update_node(1), Ok(()));
        assert_eq!(pass.end_round(), Ok(()));
        assert_eq!(pass.iteration(), 1);
        assert_eq!(pass.value(1), Some(1));
        assert_eq!(pass.start_round(), Err(PropagationError::PassTerminated));
        assert_eq!(pass.terminate(), Ok(()));
    }
}

#[test]
fn checked_actuation_rejects_disabled_actions() {
    let mut pass = ActuationPass::new(vec![Some(11), None]);
    assert_eq!(pass.len(), 2);
    assert_eq!(pass.actuate(2), Err(ActuationError::SeatOutOfRange));
    assert_eq!(pass.actuate(1), Err(ActuationError::SeatUnallocated));
    assert_eq!(pass.finish(), Err(ActuationError::PassIncomplete));
    assert_eq!(pass.actuate(0), Ok(()));
    assert_eq!(pass.effect(0), Some(Some(11)));
    assert_eq!(pass.deallocate(0), Err(ActuationError::SeatAlreadyActuated));
    assert_eq!(pass.allocate(1, 22), Ok(()));
    assert_eq!(
        pass.allocate(1, 33),
        Err(ActuationError::SeatAlreadyAllocated)
    );
    assert_eq!(pass.deallocate(1), Ok(()));
    assert!(pass.ready_to_finish());
    assert_eq!(pass.finish(), Ok(()));
    assert!(pass.is_complete());
    assert_eq!(pass.allocate(1, 22), Err(ActuationError::PassComplete));
    assert_eq!(pass.allocation(2), None);
}

#[test]
fn checked_quality_hierarchy_preserves_refinement_guards() {
    let mut hierarchy = QualityHierarchy::new(4, 5);
    assert!(!hierarchy.is_empty());
    assert_eq!(hierarchy.len(), 4);
    assert_eq!(hierarchy.max_level(), 5);

    assert_eq!(hierarchy.set_node_properties(0, 3, 1), Ok(()));
    assert_eq!(hierarchy.set_node_properties(1, 2, 2), Ok(()));
    assert_eq!(hierarchy.set_node_properties(2, 2, 3), Ok(()));
    assert_eq!(hierarchy.set_node_properties(3, 1, 4), Ok(()));
    assert_eq!(hierarchy.add_child(0, 1), Ok(()));
    assert_eq!(hierarchy.add_child(0, 2), Ok(()));
    assert_eq!(hierarchy.add_child(1, 3), Ok(()));

    assert_eq!(hierarchy.parent(0), None);
    assert_eq!(hierarchy.parent(1), Some(0));
    assert_eq!(hierarchy.level(3), Some(1));
    assert_eq!(hierarchy.cost(3), Some(4));
    assert_eq!(hierarchy.edge_count(), 3);
    assert_eq!(hierarchy.edge(0), Some((0, 1)));
    assert_eq!(hierarchy.edge(3), None);
    assert_eq!(
        hierarchy.set_node_properties(0, 4, 1),
        Err(QualityHierarchyError::NodeNotIsolated)
    );
    assert_eq!(
        hierarchy.add_child(0, 1),
        Err(QualityHierarchyError::EdgeAlreadyExists)
    );
    assert_eq!(
        hierarchy.add_child(2, 1),
        Err(QualityHierarchyError::ChildAlreadyParented)
    );
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions witness canonical forest coverage and unchanged completion refusal; fallible setup propagates errors"
)]
fn rooted_traversal_discovers_chains_multiple_roots_and_zero_costs()
-> Result<(), Box<dyn std::error::Error>> {
    let mut hierarchy = QualityHierarchy::try_new(5, u64::MAX)?;
    for (node, level) in [(0, 2), (1, 3), (2, 1), (3, u64::MAX), (4, 2)] {
        hierarchy.set_node_properties(node, level, 0)?;
    }
    hierarchy.add_child(3, 1)?;
    hierarchy.add_child(1, 4)?;
    hierarchy.add_child(0, 2)?;
    let profile = hierarchy
        .try_traversal()
        .map_err(|(reason, _original)| reason)?;
    assert_eq!((profile.considered(), profile.pending()), (0, 5));
    assert_eq!(profile.costs(), &[0; 5]);
    let mut profile = match profile.finish() {
        Err(profile) => profile,
        Ok(_) => return Err("completion published before traversal".into()),
    };
    for (node, parent) in [
        (3, None),
        (1, Some(3)),
        (0, None),
        (4, Some(1)),
        (2, Some(0)),
    ] {
        assert!(!profile.discovered(node));
        if let Some(parent) = parent {
            assert!(profile.discovered(parent));
        }
        assert_eq!(profile.step(), Some(node));
        assert!(profile.discovered(node));
    }
    assert_eq!((profile.considered(), profile.pending()), (5, 0));
    assert_eq!(profile.step(), None);
    assert!(!profile.discovered(5));
    let completed = profile
        .finish()
        .map_err(|_original| "completed forest refused sealing")?;
    assert_eq!(completed.discovery_order(), &[3, 1, 0, 4, 2]);
    assert_eq!(completed.levels(), &[2, 3, 1, u64::MAX, 2]);
    let mut empty = QualityHierarchy::try_new(0, u64::MAX)?
        .try_traversal()
        .map_err(|(reason, _original)| reason)?;
    assert_eq!((empty.considered(), empty.pending()), (0, 0));
    assert_eq!(empty.step(), None);
    assert!(empty.finish().is_ok());
    Ok(())
}

#[test]
fn checked_backtracking_pairs_descent_with_inverse_ascent() {
    assert!(matches!(
        BacktrackingTraversal::new(2, 3, 3),
        Err(BacktrackingBuildError::InitialAuxOutOfRange)
    ));

    let traversal = BacktrackingTraversal::new(2, 3, 0);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.ascend(), Err(BacktrackingError::AtRoot));
        assert_eq!(traversal.visit(), Err(BacktrackingError::NotLeaf));
        assert_eq!(traversal.descend(1, 2), Ok(()));
        assert_eq!(traversal.descend(2, 2), Ok(()));
        assert_eq!(traversal.descend(1, 1), Ok(()));
        assert_eq!(traversal.depth(), 3);
        assert_eq!(traversal.auxiliary(), 2);
        assert_eq!(traversal.choice(0), Some(1));
        assert_eq!(traversal.choice(1), Some(2));
        assert_eq!(traversal.choice(2), Some(1));
        assert_eq!(traversal.choice(3), None);
        assert!(traversal.is_leaf());
        assert_eq!(traversal.descend(1, 1), Err(BacktrackingError::AtLeaf));
        assert_eq!(traversal.visit(), Ok(()));
        assert_eq!(traversal.visit(), Err(BacktrackingError::AlreadyVisited));
        assert_eq!(traversal.visited_count(), 1);
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.auxiliary(), 0);
        assert_eq!(traversal.ascend(), Err(BacktrackingError::AtRoot));
    }
}

#[test]
fn checked_hard_selection_is_stable_and_invalidates_stale_results() {
    assert!(matches!(
        CompetitiveSelectionHard::new(0),
        Err(CompetitiveSelectionError::NoCandidates)
    ));

    let selection = CompetitiveSelectionHard::new(3);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.update_score(0, 5), Ok(()));
        assert_eq!(selection.update_score(1, 7), Ok(()));
        assert_eq!(selection.update_score(2, 7), Ok(()));
        assert_eq!(selection.evaluate(), 1);
        assert_eq!(selection.winner(), Some(1));
        assert_eq!(
            selection.update_score(3, 9),
            Err(CompetitiveSelectionError::CandidateOutOfRange)
        );
        assert_eq!(selection.update_score(0, 8), Ok(()));
        assert_eq!(selection.winner(), None);
        assert_eq!(selection.evaluate(), 0);
    }
}

#[test]
fn checked_hard_exclusive_selection_prevents_candidate_reuse() {
    let selection = CompetitiveSelectionHardExclusive::new(2, 2, 10);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.update_score(0, 0, 9), Ok(()));
        assert_eq!(selection.update_score(0, 1, 8), Ok(()));
        assert_eq!(selection.update_score(1, 0, 10), Ok(()));
        assert_eq!(selection.update_score(1, 1, 7), Ok(()));
        assert_eq!(selection.evaluate(0), Ok(0));
        assert_eq!(selection.evaluate(1), Ok(1));
        assert_eq!(selection.candidate_available(1, 0), Some(false));
        assert_eq!(
            selection.evaluate(1),
            Err(CompetitiveSelectionError::SeatAlreadyAllocated)
        );
        assert_eq!(
            selection.update_score(2, 0, 1),
            Err(CompetitiveSelectionError::SeatOutOfRange)
        );
        assert_eq!(
            selection.update_score(0, 2, 1),
            Err(CompetitiveSelectionError::CandidateOutOfRange)
        );
        assert_eq!(
            selection.update_score(0, 0, 11),
            Err(CompetitiveSelectionError::ScoreOutOfRange)
        );
        assert_eq!(selection.update_score(0, 0, 10), Ok(()));
        assert_eq!(selection.allocation(0), None);
        assert_eq!(selection.allocation(1), None);
    }
}

#[test]
fn checked_soft_selection_exposes_incremental_apportionment() {
    let selection = CompetitiveSelectionSoft::begin(vec![3, 1], 4, 3);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.assigned_weight(), 2);
        assert!(!selection.is_complete());
        assert_eq!(selection.assign_next(), Ok(0));
        assert_eq!(selection.assign_next(), Ok(0));
        assert!(selection.is_complete());
        assert_eq!(selection.weight(0), Some(3));
        assert_eq!(selection.weight(1), Some(1));
        assert_eq!(
            selection.assign_next(),
            Err(CompetitiveSelectionError::AllocationComplete)
        );
        assert_eq!(selection.update_score(1, 3), Ok(()));
        assert_eq!(selection.assigned_weight(), 2);
        assert!(!selection.is_complete());
    }

    assert!(matches!(
        CompetitiveSelectionSoft::begin(vec![1, 1], 1, 1),
        Err(CompetitiveSelectionError::WeightTotalBelowReservedFloor)
    ));
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn checked_ranked_selection_is_stable_and_rejects_invalid_replacements()
-> Result<(), Box<dyn std::error::Error>> {
    let selection = CompetitiveSelectionRanked::new(vec![5, 5, 4], 2, 5);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.selected_len(), 0);
        selection.select();
        assert_eq!(selection.selected_len(), 2);
        assert_eq!(selection.is_selected(0), Some(true));
        assert_eq!(selection.is_selected(1), Some(true));
        assert_eq!(selection.is_selected(2), Some(false));
        assert_eq!(
            selection.update_scores(vec![1, 2]),
            Err(CompetitiveSelectionError::ScoreCountMismatch)
        );
        assert_eq!(selection.selected_len(), 2);
        assert_eq!(
            selection.update_scores(vec![1, 2, 6]),
            Err(CompetitiveSelectionError::ScoreOutOfRange)
        );
        assert_eq!(selection.selected_len(), 2);
        assert_eq!(selection.update_scores(vec![1, 2, 3]), Ok(()));
        assert_eq!(selection.selected_len(), 0);
        assert_eq!(selection.is_selected(0), Some(false));
        selection.select();
        assert_eq!(selection.is_selected(1), Some(true));
        assert_eq!(selection.is_selected(2), Some(true));
        assert_eq!(selection.selected_len(), 2);
    }
    for (scores, limit, expected) in [
        (vec![], usize::MAX, 0),
        (vec![5, 5], 0, 0),
        (vec![5, 5], usize::MAX, 2),
    ] {
        let mut selection = CompetitiveSelectionRanked::new(scores, limit, 5)?;
        assert_eq!(selection.selected_len(), 0);
        selection.select();
        assert_eq!(selection.selected_len(), expected);
    }
    Ok(())
}

#[test]
fn checked_convergence_governor_computes_its_own_window_average() {
    assert!(matches!(
        ConvergenceGovernor::new(1, 3, 0, 5),
        Err(ConvergenceBuildError::EmptyWindow)
    ));

    let governor = ConvergenceGovernor::new(10, 30, 3, 50);
    assert!(governor.is_ok());
    if let Ok(mut governor) = governor {
        assert_eq!(governor.state(), ConvergenceState::Active);
        assert_eq!(governor.phase(), ConvergencePhase::Cold);
        assert_eq!(governor.update(51), Err(ConvergenceError::DeltaOutOfRange));
        assert_eq!(governor.update(12), Ok(12));
        assert_eq!(governor.state(), ConvergenceState::Cooling);
        assert_eq!(governor.phase(), ConvergencePhase::Warming);
        assert!(governor.peak_observed());
        assert_eq!(governor.update(2), Ok(7));
        assert_eq!(governor.state(), ConvergenceState::Converged);
        assert_eq!(governor.phase(), ConvergencePhase::Declining);
        assert_eq!(governor.history_len(), 2);
        assert_eq!(governor.history(0), Some(12));
        assert_eq!(governor.history(1), Some(2));
        assert_eq!(governor.history(2), None);
    }
}

#[test]
fn checked_allocation_snapshot_couples_membership_and_budget() {
    let mut snapshot = AllocationSnapshot::new(7, 3);
    assert_eq!(snapshot.accept(0, 3), Ok(()));
    assert_eq!(
        snapshot.accept(0, 1),
        Err(AllocationSnapshotError::NodeAlreadyAccepted)
    );
    assert_eq!(
        snapshot.accept(3, 1),
        Err(AllocationSnapshotError::NodeOutOfRange)
    );
    assert_eq!(
        snapshot.accept(1, 0),
        Err(AllocationSnapshotError::ZeroCost)
    );
    assert_eq!(
        snapshot.accept(1, 5),
        Err(AllocationSnapshotError::InsufficientBudget)
    );
    assert_eq!(snapshot.accept(1, 4), Ok(()));
    assert_eq!(snapshot.total_cost(), 7);
    assert_eq!(snapshot.budget_remaining(), 0);
    assert_eq!(snapshot.accepted(0), Some(0));
    assert_eq!(snapshot.accepted(1), Some(1));
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn captured_allocation_preserves_the_admitted_membership_and_costs()
-> Result<(), Box<dyn std::error::Error>> {
    let captured = AllocationSnapshot::capture(10, 3, &[0, 0, 3, 1, 2], &[3, 1, 1, 2, 9])?;
    assert_eq!(
        captured.accepted_entries().copied().collect::<Vec<_>>(),
        vec![(0, 3), (1, 2)]
    );
    assert_eq!(
        (
            captured.capacity(),
            captured.num_nodes(),
            captured.total_cost()
        ),
        (10, 3, 5)
    );
    assert_eq!(captured.budget_remaining(), 5);
    assert!(captured.contains(0));
    assert!(!captured.contains(2));
    assert_eq!(captured.len(), 2);
    assert!(!captured.is_empty());
    assert!(matches!(
        AllocationSnapshot::capture(10, 3, &[0], &[]),
        Err(AllocationSnapshotError::InputLengthMismatch)
    ));
    let mut builder = AllocationSnapshot::new(10, 3);
    assert_eq!(builder.accept(0, 3), Ok(()));
    let sealed = builder.seal();
    assert_eq!(
        sealed.accepted_entries().copied().collect::<Vec<_>>(),
        vec![(0, 3)]
    );
    assert_eq!((sealed.total_cost(), sealed.budget_remaining()), (3, 7));
    let empty = AllocationSnapshot::capture(0, 0, &[], &[])?;
    assert!(empty.is_empty());
    assert_eq!((empty.total_cost(), empty.budget_remaining()), (0, 0));
    Ok(())
}

#[test]
fn typed_incremental_reduction_uses_one_prefix_and_refuses_unchanged() {
    use automation_structures::{CheckedSignedAdd, IncrementalReduction};
    let mut reduction = IncrementalReduction::new(2, CheckedSignedAdd);
    assert_eq!((reduction.processed_len(), reduction.result()), (0, 0));
    assert!(reduction.try_record(i64::MAX));
    assert!(!reduction.try_record(1));
    assert_eq!(
        (reduction.processed_len(), reduction.result()),
        (1, i64::MAX)
    );
    assert!(reduction.try_record(-i64::MAX));
    assert!(!reduction.try_record(99));
    assert_eq!((reduction.processed_len(), reduction.result()), (2, 0));
    let mut empty = IncrementalReduction::new(0, CheckedSignedAdd);
    assert!(!empty.try_record(1));
    assert_eq!((empty.processed_len(), empty.result()), (0, 0));
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn prepared_reduction_commits_once_and_returns_refused_or_cancelled_input()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{CheckedSignedAdd, IncrementalReduction, RecordRefusal};
    let mut reduction = IncrementalReduction::new(2, CheckedSignedAdd);
    assert_eq!(
        reduction
            .prepare(7)
            .map_err(|(reason, _input)| reason)?
            .cancel(),
        7
    );
    assert_eq!((reduction.processed_len(), reduction.result()), (0, 0));
    {
        let _cancelled = reduction.prepare(11).map_err(|(reason, _input)| reason)?;
    }
    assert_eq!((reduction.processed_len(), reduction.result()), (0, 0));
    assert_eq!(
        reduction
            .prepare(i64::MAX)
            .map_err(|(reason, _input)| reason)?
            .commit(),
        (1, i64::MAX)
    );
    assert!(matches!(
        reduction.prepare(1),
        Err((RecordRefusal::Domain, 1))
    ));
    assert_eq!(
        (reduction.processed_len(), reduction.result()),
        (1, i64::MAX)
    );
    assert_eq!(
        reduction
            .prepare(-i64::MAX)
            .map_err(|(reason, _input)| reason)?
            .commit(),
        (2, 0)
    );
    assert!(matches!(
        reduction.prepare(99),
        Err((RecordRefusal::Capacity, 99))
    ));
    assert_eq!((reduction.processed_len(), reduction.result()), (2, 0));
    let mut zero = IncrementalReduction::new(0, CheckedSignedAdd);
    assert!(matches!(zero.prepare(5), Err((RecordRefusal::Capacity, 5))));
    assert_eq!((zero.processed_len(), zero.result()), (0, 0));
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn prepared_reduction_columns_publish_only_after_every_column_is_admitted()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{CheckedSignedAdd, IncrementalReduction, RecordRefusal};
    let mut first = IncrementalReduction::new(2, CheckedSignedAdd);
    let mut second = IncrementalReduction::new(2, CheckedSignedAdd);
    let mut third = IncrementalReduction::new(2, CheckedSignedAdd);
    assert!(third.try_record(i64::MAX));
    let a = first.prepare(7).map_err(|(reason, _input)| reason)?;
    let b = second.prepare(-4).map_err(|(reason, _input)| reason)?;
    assert!(matches!(third.prepare(1), Err((RecordRefusal::Domain, 1))));
    assert_eq!(a.cancel(), 7);
    assert_eq!(b.cancel(), -4);
    assert_eq!((first.processed_len(), first.result()), (0, 0));
    assert_eq!((second.processed_len(), second.result()), (0, 0));
    assert_eq!((third.processed_len(), third.result()), (1, i64::MAX));
    let a = first.prepare(7).map_err(|(reason, _input)| reason)?;
    let b = second.prepare(-4).map_err(|(reason, _input)| reason)?;
    let c = third
        .prepare(-i64::MAX)
        .map_err(|(reason, _input)| reason)?;
    assert_eq!(a.commit(), (1, 7));
    assert_eq!(b.commit(), (1, -4));
    assert_eq!(c.commit(), (2, 0));
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn execution_previews_observe_the_actual_barrier_and_predecessor_owners()
-> Result<(), Box<dyn std::error::Error>> {
    let mut fork = ForkJoin::new(2, 10, 0)?;
    assert!(!fork.all_complete());
    assert!(fork.start_worker(0));
    assert!(fork.complete_worker(0, 1));
    assert!(!fork.all_complete());
    assert!(!fork.barrier());
    assert!(fork.start_worker(1));
    assert!(fork.complete_worker(1, 2));
    assert!(fork.all_complete());
    assert!(fork.barrier());
    let mut graph = StepGraph::new(3, vec![(0, 1), (0, 2)])?;
    assert_eq!(graph.predecessors_complete(0), Some(true));
    assert_eq!(graph.predecessors_complete(1), Some(false));
    assert_eq!(graph.predecessors_complete(3), None);
    assert!(graph.start(0));
    assert!(graph.complete(0));
    assert_eq!(graph.predecessors_complete(1), Some(true));
    assert_eq!(graph.predecessors_complete(2), Some(true));
    assert!(graph.become_ready(1));
    Ok(())
}

#[test]
fn checked_federated_budget_preserves_capacity_conservation() {
    let mut budget = FederatedBudget::new(10, 2);
    assert!(budget.try_delegate(0, 6));
    assert!(!budget.try_delegate(1, 5));
    assert!(budget.try_delegate(1, 4));
    assert!(budget.try_allocate(0, 5));
    assert_eq!(budget.pool_allocated(1), Some(0));
    assert!(!budget.try_allocate(0, 2));
    assert!(budget.try_allocate(1, 2));
    assert_eq!(budget.pool_allocated(0), Some(5));
    assert!(budget.try_release(0, 3));
    assert_eq!(budget.master_allocated(), 10);
    assert_eq!(budget.pool_capacity(1), Some(4));
    assert_eq!(budget.pool_allocated(0), Some(2));
    assert_eq!(budget.pool_allocated(1), Some(2));
}

#[test]
fn checked_bisection_converges_within_its_probe_budget() {
    let bisection = Bisection::new(16, 11);
    assert!(bisection.is_ok());
    if let Ok(mut bisection) = bisection {
        assert!(!bisection.is_converged());
        bisection.converge();
        assert!(bisection.is_converged());
        assert!(bisection.lower() <= 11 && 11 <= bisection.upper());
        assert!(bisection.probes_taken() <= bisection.max_probes());
    }
}

#[test]
fn checked_equivalence_class_bounds_indices_and_union_work() {
    let mut classes = EquivalenceClass::new(3, 2);
    assert_eq!(classes.union(0, 1), Ok(true));
    assert_eq!(classes.equivalent(0, 1), Ok(true));
    assert_eq!(classes.union(0, 1), Ok(false));
    assert_eq!(classes.union(1, 2), Ok(true));
    assert_eq!(classes.unions_performed(), 2);
    assert_eq!(classes.max_unions(), 2);
    assert_eq!(classes.union(0, 2), Ok(false));
    assert_eq!(
        classes.representative(3),
        Err(EquivalenceClassError::ElementOutOfRange)
    );
}

#[test]
fn checked_rate_limit_rolls_windows_on_its_logical_clock() {
    let limit = RateLimit::new(2, 2, 2);
    assert!(limit.is_ok());
    if let Ok(mut limit) = limit {
        assert!(limit.try_acquire());
        assert!(limit.try_acquire());
        assert!(!limit.try_acquire());
        assert_eq!(limit.tick(), Ok(()));
        assert!(!limit.try_acquire());
        assert_eq!(limit.tick(), Ok(()));
        assert!(limit.try_acquire());
        assert_eq!(limit.window_start(), 2);
        assert_eq!(limit.tick(), Err(RateLimitError::ClockExhausted));
    }
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn checked_rate_limit_rejects_zero_duration_and_bounds_an_unchanged_clock()
-> Result<(), Box<dyn std::error::Error>> {
    assert!(matches!(
        RateLimit::new(1, 0, 10),
        Err(automation_structures::RateLimitBuildError::ZeroWindowDuration)
    ));
    let mut limit = RateLimit::new(2, 1, 1)?;
    let admitted = (0..100).filter(|_| limit.try_acquire()).count();
    assert_eq!(admitted, 2);
    assert_eq!(limit.clock(), 0);
    assert_eq!(limit.count(), 2);
    assert_eq!(limit.tick(), Ok(()));
    assert!(limit.try_acquire());
    assert!(limit.try_acquire());
    assert!(!limit.try_acquire());
    Ok(())
}

#[test]
fn checked_reduction_consumes_one_ordered_prefix() {
    let reduction = Reduction::new(vec![2, 3, 5]);
    assert!(reduction.is_ok());
    if let Ok(mut reduction) = reduction {
        assert_eq!(reduction.process_next(), Ok(()));
        assert_eq!(reduction.result(), 2);
        assert_eq!(reduction.process_next(), Ok(()));
        assert_eq!(reduction.process_next(), Ok(()));
        assert!(reduction.is_complete());
        assert_eq!(reduction.result(), 10);
        assert_eq!(reduction.process_next(), Err(ReductionError::Complete));
    }
}

#[test]
fn checked_relationship_graph_keeps_adjacency_in_sync() {
    let mut graph = RelationshipGraph::new(3, 10);
    assert_eq!(graph.add_edge(0, 1, 4), Ok(true));
    assert_eq!(graph.add_edge(0, 1, 4), Ok(false));
    assert_eq!(graph.add_edge(0, 1, 7), Ok(true));
    assert_eq!(graph.add_edge(1, 2, 6), Ok(true));
    assert_eq!(graph.edge_count(), 3);
    assert_eq!(
        graph.add_edge(0, 0, 1),
        Err(RelationshipGraphError::SelfLoop)
    );
    assert_eq!(
        graph.add_edge(0, 3, 1),
        Err(RelationshipGraphError::NodeOutOfRange)
    );
    assert_eq!(
        graph.add_edge(0, 2, 11),
        Err(RelationshipGraphError::WeightOutOfRange)
    );
    assert!(graph.contains(0, 1));
    graph.remove_edges(0, 1);
    assert!(!graph.contains(0, 1));
    assert!(graph.contains(1, 2));
    assert_eq!(graph.edge_count(), 1);
    assert_eq!(graph.edge(0), Some((1, 2, 6)));
}

#[test]
fn checked_sampler_keeps_selection_bounded_and_supported() {
    let mut sampler = Sampler::new(vec![2, 0, 4], 2);
    assert_eq!(sampler.sample(1), Err(SamplerError::OutsideSupport));
    assert_eq!(sampler.sample(0), Ok(()));
    assert_eq!(sampler.sample(0), Err(SamplerError::AlreadySelected));
    assert_eq!(sampler.draw_weighted(2, 3), Ok(true));
    assert_eq!(sampler.sample(1), Err(SamplerError::SampleFull));
    assert!(!sampler.zero(0));

    let mut branches = Sampler::new(vec![2, 0, 4], 3);
    assert_eq!(branches.draw_uniform(0), Ok(true));
    assert_eq!(branches.draw_uniform(0), Ok(false));
    assert!(branches.zero(1));
    assert_eq!(branches.draw_uniform(1), Ok(false));
    assert_eq!(branches.draw_weighted(2, 4), Ok(false));
    assert_eq!(branches.draw_weighted(2, 3), Ok(true));
    assert_eq!(
        branches.draw_weighted(3, 0),
        Err(SamplerError::ItemOutOfRange)
    );
    assert!(!branches.zero(3));
}

#[test]
fn checked_select_then_actuate_uses_one_selection_and_actuation_lifecycle() {
    let composition = SelectThenActuate::new(2, 2);
    assert!(composition.is_ok());
    if let Ok(mut composition) = composition {
        assert_eq!(composition.score(0, 0), Some(0));
        assert_eq!(composition.score(0, 1), Some(0));
        assert_eq!(composition.score(1, 0), Some(0));
        assert_eq!(composition.score(1, 1), Some(0));
        assert_eq!(composition.update_score(0, 0, 2), Ok(()));
        assert_eq!(composition.update_score(0, 1, 5), Ok(()));
        assert_eq!(composition.score(1, 0), Some(0));
        assert_eq!(composition.score(1, 1), Some(0));
        assert_eq!(composition.evaluate(0), Ok(1));
        assert_eq!(composition.allocation(1), None);
        assert_eq!(
            composition.evaluate(0),
            Err(SelectThenActuateError::SeatAlreadyAllocated)
        );
        assert_eq!(composition.actuate(0), Ok(()));
        assert_eq!(composition.is_actuated(0), Some(true));
        assert_eq!(
            composition.update_score(0, 1, 6),
            Err(SelectThenActuateError::EffectAlreadyApplied)
        );
        assert_eq!(composition.finish(), Ok(()));
        assert!(composition.is_complete());
    }
}

#[test]
fn checked_signal_tracks_each_recorded_change_epoch() {
    let signal = Signal::new(0, 3, 2);
    assert!(signal.is_ok());
    if let Ok(mut signal) = signal {
        assert_eq!(signal.set_value(0), Ok(false));
        assert_eq!(signal.set_value(3), Err(SignalError::ValueOutOfRange));
        assert_eq!(signal.set_value(2), Ok(true));
        assert_eq!(signal.is_pending(0), Some(true));
        assert_eq!(signal.notify(0), Ok(()));
        assert_eq!(signal.notify(0), Err(SignalError::ListenerNotPending));
        assert_eq!(signal.is_notified(0), Some(true));
        assert_eq!(signal.set_value(1), Ok(true));
        assert_eq!(signal.change_count(), 2);
        assert_eq!(signal.value(), 1);
        assert_eq!(signal.is_pending(0), Some(true));
        assert_eq!(signal.notify(0), Ok(()));
        assert_eq!(signal.notify(2), Err(SignalError::ListenerOutOfRange));
    }

    let bounded = Signal::with_change_capacity(0, 2, 1, 1);
    assert!(bounded.is_ok());
    if let Ok(mut bounded) = bounded {
        assert_eq!(bounded.set_value(1), Ok(true));
        assert_eq!(
            bounded.set_value(0),
            Err(SignalError::ChangeCapacityExhausted)
        );
        assert_eq!(bounded.change_count(), 1);
        assert_eq!(bounded.value(), 1);
    }
}

#[test]
fn checked_traversal_engine_tracks_budgeted_acceptance() {
    let traversal = TraversalEngine::new(3, 0, 4);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.accepted_cost(), 0);
        assert_eq!(traversal.terminate(), Err(TraversalError::QueueNotEmpty));
        assert_eq!(traversal.visit(0), Ok(()));
        assert!(traversal.is_accepted(0));
        assert_eq!(traversal.accepted_len(), 1);
        assert_eq!(traversal.accepted_cost(), 2);
        assert!(traversal.is_queued(1));
        assert_eq!(traversal.visit(1), Ok(()));
        assert!(traversal.is_accepted(1));
        assert_eq!(traversal.accepted_len(), 2);
        assert_eq!(traversal.accepted_cost(), 4);
        assert_eq!(traversal.visit(2), Ok(()));
        assert!(traversal.is_visited(2));
        assert!(!traversal.is_accepted(2));
        assert_eq!(traversal.accepted_len(), 2);
        assert_eq!(traversal.accepted_cost(), 4);
        assert_eq!(traversal.terminate(), Ok(()));
    }
}

#[test]
fn checked_traversal_skip_removes_only_the_named_frontier_node() {
    let traversal = TraversalEngine::new(4, 0, 8);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.visit(0), Ok(()));
        assert_eq!(traversal.accepted_cost(), 2);
        assert_eq!(traversal.queued_len(), 3);
        assert_eq!(traversal.skip(2), Ok(()));
        assert_eq!(traversal.accepted_cost(), 2);
        assert!(!traversal.is_queued(2));
        assert!(!traversal.is_visited(2));
        assert!(!traversal.is_accepted(2));
        assert!(traversal.is_queued(1));
        assert!(traversal.is_queued(3));
        assert_eq!(traversal.skip(2), Err(TraversalError::NodeNotQueued));
        assert_eq!(traversal.skip(4), Err(TraversalError::NodeOutOfRange));
    }
}

#[test]
fn checked_sequential_execution_preserves_history_position_agreement() {
    let execution = Sequential::new(2, 4, 0);
    assert!(execution.is_ok());
    if let Ok(mut execution) = execution {
        assert!(!execution.complete_step(1));
        assert!(execution.begin_step());
        assert!(!execution.begin_step());
        assert!(!execution.complete_step(4));
        assert!(execution.complete_step(2));
        assert!(execution.begin_step());
        assert!(execution.complete_step(3));
        assert!(execution.is_done());
        assert_eq!(execution.history(0), Some(2));
        assert_eq!(execution.history(1), Some(3));
        assert!(!execution.begin_step());
    }
}

#[test]
fn checked_fork_join_requires_every_worker_before_output() {
    let execution = ForkJoin::new(2, 10, 0);
    assert!(execution.is_ok());
    if let Ok(mut execution) = execution {
        assert!(!execution.barrier());
        assert!(execution.start_worker(0));
        assert!(execution.start_worker(1));
        assert_eq!(execution.worker_state(0), Some(WorkerState::Running));
        assert!(execution.complete_worker(0, 4));
        assert!(!execution.barrier());
        assert!(execution.complete_worker(1, 6));
        assert!(execution.barrier());
        assert_eq!(execution.phase(), ForkJoinPhase::Join);
        assert!(execution.produce_output());
        assert_eq!(execution.output(0), Some(4));
        assert_eq!(execution.output(1), Some(6));
        assert_eq!(execution.phase(), ForkJoinPhase::Done);
    }
}

#[test]
fn checked_step_graph_enforces_predecessor_completion() {
    assert!(matches!(
        StepGraph::new(2, vec![(0, 2)]),
        Err(StepGraphBuildError::EdgeEndpointOutOfRange)
    ));
    assert!(matches!(
        StepGraph::new(2, vec![(0, 1), (0, 1)]),
        Err(StepGraphBuildError::DuplicateEdge)
    ));

    let graph = StepGraph::new(2, vec![(0, 1)]);
    assert!(graph.is_ok());
    if let Ok(mut graph) = graph {
        assert_eq!(graph.state(0), Some(StepState::Ready));
        assert_eq!(graph.state(1), Some(StepState::NotReady));
        assert!(!graph.start(1));
        assert!(graph.start(0));
        assert!(graph.complete(0));
        assert!(graph.become_ready(1));
        assert!(graph.start(1));
        assert!(graph.complete(1));
        assert!(graph.is_done());
    }
}

#[test]
fn checked_stream_graph_preserves_fifo_and_backpressure() {
    let stream = StreamGraph::new(3, 1, 2, 10);
    assert!(stream.is_ok());
    if let Ok(mut stream) = stream {
        assert!(stream.has_enabled_action());
        assert_eq!(stream.consume(), None);
        assert!(stream.ingest(3));
        assert_eq!(
            stream.ingested(),
            stream.emitted()
                + stream.first_queue_len()
                + stream.second_queue_len()
                + stream.third_queue_len()
        );
        assert!(!stream.ingest(5));
        assert!(stream.advance_first());
        assert!(stream.ingest(5));
        assert_eq!(stream.consume(), Some(3));
        assert!(stream.advance_first());
        assert_eq!(stream.consume(), Some(5));
        assert!(stream.is_done());
        assert!(stream.has_enabled_action());
    }
}

#[test]
fn checked_four_stage_stream_graph_uses_the_second_transfer() {
    let stream = StreamGraph::new(4, 1, 2, 10);
    assert!(stream.is_ok());
    if let Ok(mut stream) = stream {
        assert!(stream.has_enabled_action());
        assert!(!stream.advance_second());
        assert!(stream.ingest(3));
        assert!(stream.advance_first());
        assert_eq!(stream.second_queue_len(), 1);
        assert!(stream.advance_second());
        assert_eq!(stream.second_queue_len(), 0);
        assert_eq!(stream.third_queue_len(), 1);
        assert_eq!(stream.consume(), Some(3));
        assert!(stream.ingest(5));
        assert!(stream.advance_first());
        assert!(stream.advance_second());
        assert_eq!(stream.consume(), Some(5));
        assert!(stream.is_done());
        assert!(stream.has_enabled_action());
    }
}

#[test]
fn connective_accumulator_carries_one_partial_result() {
    let mut input = Accumulator::new(vec![4u64, 5]);
    assert_eq!(input.accumulated_len(), 0);
    assert_eq!(input.pending_len(), 2);
    assert_eq!(input.checked_len(), Some(2));
    assert!(!input.is_complete());
    assert_eq!(input.pending(0), Some(4));
    assert_eq!(input.pending(1), Some(5));
    assert_eq!(input.advance(), Some(4));
    assert_eq!(input.accumulated(0), Some(4));
    assert_eq!(input.advance(), Some(5));
    assert!(input.is_complete());
    assert_eq!(input.advance(), None);

    let mut output = Accumulator::from_accumulated(Vec::<u64>::new());
    assert_eq!(output.try_append(4), Ok(()));
    assert_eq!(output.try_append(5), Ok(()));
    assert_eq!(output.try_append(6), Ok(()));
    assert_eq!(output.accumulated_len(), 3);
    assert_eq!(output.checked_len(), Some(3));
    assert_eq!(output.accumulated(0), Some(4));
    assert_eq!(output.accumulated(2), Some(6));
}

#[test]
fn connective_buffer_is_bounded_fifo() {
    let mut buffer = Buffer::new(2);
    assert_eq!(buffer.push(1), Ok(()));
    assert_eq!(buffer.push(2), Ok(()));
    assert_eq!(buffer.push(3), Err(3));
    assert!(buffer.is_full());
    assert_eq!(buffer.pop(), Some(1));
    assert_eq!(buffer.pop(), Some(2));
    assert_eq!(buffer.pop(), None);

    let mut distinct = Buffer::<u64>::new(2);
    assert!(distinct.push_unique(7));
    assert!(!distinct.push_unique(7));
    assert!(distinct.contains(7));
    assert!(distinct.remove(7));
    assert!(!distinct.contains(7));

    let mut ordered = Buffer::<u64>::new(4);
    assert!(ordered.push_unique(1));
    assert!(ordered.push_unique(2));
    assert!(ordered.push_unique(3));
    assert!(ordered.remove(2));
    assert_eq!(ordered.pop(), Some(1));
    assert_eq!(ordered.pop(), Some(3));
    assert_eq!(ordered.pop(), None);
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn preallocated_buffer_preserves_owned_fifo_and_reports_capacity_overflow()
-> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = Buffer::<String>::try_new(2)?;
    assert_eq!(buffer.capacity(), 2);
    assert!(buffer.is_empty());
    assert_eq!(buffer.push(String::from("first")), Ok(()));
    assert_eq!(buffer.push(String::from("second")), Ok(()));
    assert_eq!(
        buffer.push(String::from("refused")),
        Err(String::from("refused"))
    );
    assert_eq!(buffer.pop().as_deref(), Some("first"));
    assert_eq!(buffer.push(String::from("third")), Ok(()));
    assert_eq!(buffer.pop().as_deref(), Some("second"));
    assert_eq!(buffer.pop().as_deref(), Some("third"));
    assert_eq!(buffer.pop(), None);
    assert!(Buffer::<u64>::try_new(usize::MAX).is_err());
    let mut zero = Buffer::<u64>::try_new(0)?;
    assert_eq!(zero.push(1), Err(1));
    assert_eq!(zero.pop(), None);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn preallocated_buffer_reuses_reserved_storage_through_fifo_cycles()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::connectives::buffer::Buffer as Carrier;
    let mut buffer = Carrier::<u64>::try_new(4)?;
    let capacity = buffer.values.capacity();
    let allocation = buffer.values.as_ptr();
    assert!(capacity >= 4);
    for cycle in 0..32 {
        for offset in 0..4 {
            assert_eq!(buffer.push(cycle * 4 + offset), Ok(()));
        }
        assert_eq!(buffer.push(999), Err(999));
        for offset in 0..4 {
            assert_eq!(buffer.pop(), Some(cycle * 4 + offset));
        }
        assert_eq!(buffer.values.capacity(), capacity);
        assert_eq!(buffer.values.as_ptr(), allocation);
    }
    Ok(())
}

#[test]
fn connective_counter_marker_projection_and_order_are_reusable() {
    let mut counter = Counter::new(0);
    assert!(!counter.try_decrement());
    assert!(counter.try_increment());
    assert_eq!(counter.value(), 1);
    assert!(counter.try_decrement());
    assert_eq!(counter.value(), 0);

    let mut marker = Marker::new(false);
    assert!(marker.set());
    assert!(!marker.set());
    assert!(marker.clear());
    assert!(!marker.clear());

    assert!(projection_consistent(true, true));
    assert!(!projection_consistent(true, false));
    assert!(strictly_before(1, 2));
    assert!(!strictly_before(2, 2));
}

#[test]
fn public_types_support_standard_debugging_and_thread_transfer() {
    fn assert_common<T: core::fmt::Debug + Send + Sync + 'static>() {}
    fn assert_error<T: std::error::Error + Send + Sync + 'static>() {}

    assert_common::<Budget>();
    assert_common::<ResourceRegistry>();
    assert_common::<AuditRecord>();
    assert_common::<AuditSink>();
    assert_common::<Cursor>();
    assert_common::<PropagationPass>();
    assert_common::<ActuationPass>();
    assert_common::<QualityHierarchy>();
    assert_common::<BacktrackingTraversal>();
    assert_common::<CompetitiveSelectionHard>();
    assert_common::<CompetitiveSelectionHardExclusive>();
    assert_common::<CompetitiveSelectionSoft>();
    assert_common::<CompetitiveSelectionRanked>();
    assert_common::<ConvergenceGovernor>();
    assert_common::<AllocationSnapshot>();
    assert_common::<FederatedBudget>();
    assert_common::<Bisection>();
    assert_common::<EquivalenceClass>();
    assert_common::<RateLimit>();
    assert_common::<Reduction>();
    assert_common::<RelationshipGraph>();
    assert_common::<Sampler>();
    assert_common::<SelectThenActuate>();
    assert_common::<Signal>();
    assert_common::<TraversalEngine>();
    assert_common::<Sequential>();
    assert_common::<ForkJoin>();
    assert_common::<StepGraph>();
    assert_common::<StreamGraph>();
    assert_common::<Accumulator<u64>>();
    assert_common::<Buffer<u64>>();
    assert_common::<Counter>();
    assert_common::<Marker>();
    assert_common::<automation_structures::PropagationRound>();
    assert_common::<ConvergencePhase>();
    assert_common::<ConvergenceState>();
    assert_common::<ForkJoinPhase>();
    assert_common::<WorkerState>();
    assert_common::<StepState>();

    assert_error::<BudgetError>();
    assert_error::<CursorError>();
    assert_error::<PropagationBuildError>();
    assert_error::<PropagationError>();
    assert_error::<ActuationError>();
    assert_error::<QualityHierarchyError>();
    assert_error::<BacktrackingBuildError>();
    assert_error::<BacktrackingError>();
    assert_error::<CompetitiveSelectionError>();
    assert_error::<ConvergenceBuildError>();
    assert_error::<ConvergenceError>();
    assert_error::<AllocationSnapshotError>();
    assert_error::<automation_structures::BisectionBuildError>();
    assert_error::<automation_structures::BisectionError>();
    assert_error::<EquivalenceClassError>();
    assert_error::<automation_structures::RateLimitBuildError>();
    assert_error::<RateLimitError>();
    assert_error::<automation_structures::ReductionBuildError>();
    assert_error::<ReductionError>();
    assert_error::<RelationshipGraphError>();
    assert_error::<SamplerError>();
    assert_error::<SelectThenActuateBuildError>();
    assert_error::<SelectThenActuateError>();
    assert_error::<automation_structures::SignalBuildError>();
    assert_error::<SignalError>();
    assert_error::<automation_structures::TraversalBuildError>();
    assert_error::<TraversalError>();
    assert_error::<automation_structures::SequentialBuildError>();
    assert_error::<automation_structures::ForkJoinBuildError>();
    assert_error::<StepGraphBuildError>();
    assert_error::<automation_structures::StreamGraphBuildError>();
    assert_error::<automation_structures::ArrangementError>();
    assert_error::<automation_structures::AdjacencyBuildError>();
}

#[test]
fn checked_constructors_reject_invalid_configurations() {
    assert!(matches!(
        Bisection::new(1, 0),
        Err(automation_structures::BisectionBuildError::DomainTooSmall)
    ));
    assert!(matches!(
        Bisection::new(2, 0),
        Err(automation_structures::BisectionBuildError::ThresholdOutOfRange)
    ));
    assert!(matches!(
        RateLimit::new(0, 1, 1),
        Err(automation_structures::RateLimitBuildError::ZeroLimit)
    ));
    assert!(matches!(
        Reduction::new(vec![1_000_000_001]),
        Err(automation_structures::ReductionBuildError::ValueOutOfRange)
    ));
    assert!(matches!(
        Signal::new(1, 1, 0),
        Err(automation_structures::SignalBuildError::InitialValueOutOfRange)
    ));
    assert!(matches!(
        SelectThenActuate::new(1, 0),
        Err(SelectThenActuateBuildError::NoCandidates)
    ));
    assert!(matches!(
        TraversalEngine::new(0, 0, 0),
        Err(automation_structures::TraversalBuildError::NoNodes)
    ));
    assert!(matches!(
        TraversalEngine::new(1, 1, 0),
        Err(automation_structures::TraversalBuildError::RootOutOfRange)
    ));
    assert!(matches!(
        Sequential::new(0, 1, 0),
        Err(automation_structures::SequentialBuildError::NoSteps)
    ));
    assert!(matches!(
        Sequential::new(1, 0, 0),
        Err(automation_structures::SequentialBuildError::EmptyValueDomain)
    ));
    assert!(matches!(
        ForkJoin::new(1, 0, 0),
        Err(automation_structures::ForkJoinBuildError::EmptyValueDomain)
    ));
    assert!(matches!(
        StreamGraph::new(2, 1, 1, 1),
        Err(automation_structures::StreamGraphBuildError::UnsupportedChainLength)
    ));
    assert!(matches!(
        StreamGraph::new(3, 0, 1, 1),
        Err(automation_structures::StreamGraphBuildError::ZeroCapacity)
    ));
    assert!(matches!(
        StreamGraph::new(3, 1, 1, 0),
        Err(automation_structures::StreamGraphBuildError::EmptyRecordDomain)
    ));
}

#[cfg(feature = "proof-api")]
mod summarized_audit {
    use automation_structures::primitives::audit_sink::{
        AuditSink, CheckedSignedAdd, CheckedSignedSumCount, NullableSigned, SignedSumCount,
    };

    #[test]
    fn typed_summary_preserves_order_latest_and_refuses_overflow() {
        let mut sink = AuditSink::with_summary(4, CheckedSignedAdd);
        assert_eq!(sink.committed_count(), 0);
        assert_eq!(sink.latest(), None);
        for value in [7, -11, 8] {
            assert!(sink.record_typed(value));
        }
        assert_eq!(sink.carry(), 4);
        assert_eq!(sink.latest(), Some(8));
        assert_eq!(sink.committed_count(), 3);
        assert!(!sink.record_typed(i64::MAX));
        assert_eq!(
            (sink.carry(), sink.latest(), sink.committed_count()),
            (4, Some(8), 3)
        );
        assert!(sink.record_typed(-4));
        assert!(!sink.record_typed(1));
        assert_eq!(
            (sink.carry(), sink.latest(), sink.committed_count()),
            (0, Some(-4), 4)
        );
    }

    #[test]
    fn summary_and_retained_share_record_for_signed_limits_and_repeated_work() {
        let mut empty = AuditSink::with_summary(0, CheckedSignedAdd);
        assert!(!empty.record_typed(0));
        let mut full = AuditSink::with_typed_operator(4, CheckedSignedAdd);
        let mut summary = AuditSink::with_summary(4, CheckedSignedAdd);
        for value in [i64::MIN, -1, i64::MAX, 1, 0, 1] {
            assert_eq!(summary.record_typed(value), full.record_typed(value));
            assert_eq!(summary.carry(), full.carry());
            assert_eq!(summary.committed_count(), full.committed_count());
            assert_eq!(summary.latest(), full.latest());
        }
        let mut repeated = AuditSink::with_summary(1_000_000, CheckedSignedAdd);
        for _ in 0..100_000 {
            assert!(repeated.record_typed(1));
        }
        assert_eq!(repeated.carry(), 100_000);
        assert_eq!(repeated.committed_count(), 100_000);
        assert_eq!(repeated.latest(), Some(1));
        assert!(core::mem::size_of_val(&repeated) < 128);
    }

    #[test]
    fn nullable_pair_counts_contributions_and_frames_refusal() {
        let mut fold = AuditSink::with_summary(6, CheckedSignedSumCount);
        use NullableSigned::{Missing, Value};
        for value in [Missing, Value(7), Missing, Value(-11)] {
            assert!(fold.record_typed(value));
        }
        assert_eq!(fold.carry(), SignedSumCount { sum: -4, count: 2 });
        assert_eq!(fold.committed_count(), 4);
        assert_eq!(fold.latest(), Some(Value(-11)));
        assert!(!fold.record_typed(Value(i64::MIN)));
        assert_eq!(
            (fold.carry(), fold.committed_count()),
            (SignedSumCount { sum: -4, count: 2 }, 4)
        );
        assert!(fold.record_typed(Missing));
        assert_eq!(fold.latest(), Some(Missing));
        assert_eq!(fold.carry(), SignedSumCount { sum: -4, count: 2 });
    }
}

#[cfg(feature = "proof-api")]
mod indexed_registry {
    use automation_structures::primitives::{
        audit_sink::{AuditSink, CheckedSignedAdd},
        resource_registry::{ByteKey, RegistryStorage, ResourceRegistry},
    };

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions are the controlled test failure boundary"
    )]
    fn exact_bytes_borrowed_probes_order_and_owned_storage()
    -> Result<(), Box<dyn std::error::Error>> {
        let keys = [
            vec![],
            vec![0],
            vec![1],
            vec![1, 0],
            vec![1, 0, 2],
            vec![1, 2],
        ];
        let mut registry = ResourceRegistry::new_indexed();
        assert!(registry.try_reserve_entries(keys.len()));
        let capacity = registry.entries.capacity();
        for (i, bytes) in keys.iter().enumerate() {
            let retained = bytes.clone();
            let address = retained.as_ptr();
            assert!(
                registry
                    .try_register_key(ByteKey::from_bytes(retained), vec![i])
                    .is_ok()
            );
            assert_eq!(
                registry
                    .entries
                    .key_at(i)
                    .ok_or("missing retained key")?
                    .as_bytes()
                    .as_ptr(),
                address
            );
        }
        assert!(registry.entries.key_at(usize::MAX).is_none());
        assert!(registry.entries.value_at(usize::MAX).is_none());
        assert!(registry.entries.value_mut_at(usize::MAX).is_none());
        assert!(registry.entries.remove(usize::MAX).is_none());
        assert_eq!(registry.entries.len(), keys.len());
        assert_eq!(registry.entries.capacity(), capacity);
        for (i, bytes) in keys.iter().enumerate() {
            let mut surrounded = vec![255];
            surrounded.extend(bytes);
            surrounded.push(254);
            let probe = surrounded
                .get(1..surrounded.len() - 1)
                .ok_or("missing interior borrowed probe")?;
            assert_eq!(registry.lookup_query(&probe), Some(&vec![i]));
        }
        assert!(registry.lookup_query(&[1u8, 0, 2, 0].as_slice()).is_none());
        assert!(
            registry
                .try_register_key(ByteKey::from_bytes(vec![1]), vec![99])
                .is_ok()
        );
        let expected = [
            vec![],
            vec![0],
            vec![1, 0],
            vec![1, 0, 2],
            vec![1, 2],
            vec![1],
        ];
        for (i, key) in expected.iter().enumerate() {
            assert_eq!(
                registry
                    .entries
                    .key_at(i)
                    .ok_or("missing retained key")?
                    .as_bytes(),
                key
            );
        }
        registry.deregister_key(ByteKey::from_bytes(vec![1, 0]));
        assert_eq!(registry.entries.len(), 5);
        assert!(registry.lookup_query(&[1u8, 0].as_slice()).is_none());
        assert_eq!(registry.lookup_query(&[1u8].as_slice()), Some(&vec![99]));
        assert_eq!(registry.entries.capacity(), capacity);
        assert!(!registry.try_reserve_entries(usize::MAX));
        assert_eq!(registry.entries.len(), 5);
        assert_eq!(registry.lookup_query(&[1u8].as_slice()), Some(&vec![99]));
        Ok(())
    }

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions are the controlled test failure boundary"
    )]
    fn borrowed_aggregate_owners_retain_keys_values_and_capacity()
    -> Result<(), Box<dyn std::error::Error>> {
        let mut registry = ResourceRegistry::new_indexed();
        assert!(registry.try_reserve_entries(64));
        for i in 0u64..64 {
            assert!(
                registry
                    .try_register_key(
                        ByteKey::from_bytes(i.to_be_bytes().to_vec()),
                        AuditSink::with_summary(100_000, CheckedSignedAdd)
                    )
                    .is_ok()
            );
        }
        let key_addresses: Vec<_> = (0..64)
            .map(|i| {
                registry
                    .entries
                    .key_at(i)
                    .map(|key| key.as_bytes().as_ptr())
                    .ok_or("missing retained key")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let value_addresses: Vec<_> = (0..64)
            .map(|i| {
                registry
                    .entries
                    .value_at(i)
                    .map(|value| value as *const _)
                    .ok_or("missing retained value")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let capacity = registry.entries.capacity();
        for i in 0u64..100_000 {
            let probe = (i % 64).to_be_bytes();
            let fold = registry
                .lookup_query_mut(&probe.as_slice())
                .ok_or("missing retained group")?;
            assert!(fold.record_typed(1));
        }
        let mut total = 0;
        for i in 0..64 {
            let fold = registry
                .entries
                .value_at(i)
                .ok_or("missing retained fold")?;
            total += fold.carry();
            assert_eq!(usize::try_from(fold.carry())?, fold.committed_count());
            assert_eq!(
                fold.committed_count(),
                100_000usize.div_euclid(64) + usize::from(i < 100_000 % 64)
            );
            assert_eq!(
                registry
                    .entries
                    .key_at(i)
                    .ok_or("missing retained key")?
                    .as_bytes()
                    .as_ptr(),
                *key_addresses.get(i).ok_or("missing original key address")?
            );
            assert_eq!(
                fold as *const _,
                *value_addresses
                    .get(i)
                    .ok_or("missing original value address")?
            );
        }
        assert_eq!(total, 100_000);
        assert_eq!(registry.entries.capacity(), capacity);
        assert!(registry.lookup_query_mut(&[255u8].as_slice()).is_none());
        assert_eq!(registry.entries.len(), 64);
        Ok(())
    }
}

#[cfg(feature = "proof-api")]
mod finite_ordering {
    use automation_structures::{
        connectives::ordering_pass::{ArrangementError, SignedRowOrder, try_arrange_indices},
        primitives::audit_sink::NullableSigned::{Missing, Value},
    };

    #[test]
    #[expect(
        clippy::panic_in_result_fn,
        reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
    )]
    fn immutable_arrangement_owns_both_permutation_directions()
    -> Result<(), Box<dyn std::error::Error>> {
        use automation_structures::IndexArrangement;
        let values = vec![Value(3), Missing, Value(2), Value(3), Missing, Value(-4)];
        let order = SignedRowOrder {
            values: &values,
            descending: false,
            nulls_first: true,
        };
        let empty = IndexArrangement::try_new(0, &order)?;
        assert!(empty.is_empty());
        assert_eq!(empty.positions(), &[]);
        assert_eq!(empty.inverse(), &[]);
        assert_eq!(empty.rank_of(0), None);
        let arranged = IndexArrangement::try_new(6, &order)?;
        assert_eq!(arranged.positions(), &[1, 4, 5, 2, 0, 3]);
        assert_eq!(arranged.inverse(), &[4, 0, 3, 5, 1, 2]);
        assert_eq!(arranged.len(), 6);
        for (rank, original) in arranged.positions().iter().copied().enumerate() {
            assert_eq!(arranged.rank_of(original), Some(rank));
            assert_eq!(arranged.original_at(rank), Some(original));
        }
        assert_eq!(arranged.original_at(6), None);
        assert_eq!(arranged.rank_of(6), None);
        assert_eq!(arranged.rank_of(usize::MAX), None);
        let prefix = IndexArrangement::try_new(3, &order)?;
        assert_eq!(prefix.positions(), &[1, 2, 0]);
        assert_eq!(prefix.inverse(), &[2, 0, 1]);
        assert!(matches!(
            IndexArrangement::try_new(7, &order),
            Err(ArrangementError::OutsideDomain)
        ));
        assert_eq!(
            values,
            vec![Value(3), Missing, Value(2), Value(3), Missing, Value(-4)]
        );
        Ok(())
    }

    #[test]
    fn direction_nulls_and_equal_key_ties_are_exact() {
        let values = vec![Value(3), Missing, Value(2), Value(3), Missing, Value(-4)];
        let ascending = SignedRowOrder {
            values: &values,
            descending: false,
            nulls_first: true,
        };
        assert_eq!(
            try_arrange_indices(6, &ascending),
            Ok(vec![1, 4, 5, 2, 0, 3])
        );
        let descending = SignedRowOrder {
            values: &values,
            descending: true,
            nulls_first: false,
        };
        assert_eq!(
            try_arrange_indices(6, &descending),
            Ok(vec![0, 3, 2, 5, 1, 4])
        );
        let descending = SignedRowOrder {
            values: &values,
            descending: true,
            nulls_first: true,
        };
        assert_eq!(
            try_arrange_indices(6, &descending),
            Ok(vec![1, 4, 0, 3, 2, 5])
        );
        assert_eq!(try_arrange_indices(3, &descending), Ok(vec![1, 0, 2]));
        assert_eq!(
            values,
            vec![Value(3), Missing, Value(2), Value(3), Missing, Value(-4)]
        );
    }
    #[test]
    fn empty_domain_bounds_and_signed_extremes() {
        let values = vec![Value(i64::MAX), Value(i64::MIN), Value(0), Value(i64::MIN)];
        let order = SignedRowOrder {
            values: &values,
            descending: false,
            nulls_first: false,
        };
        assert_eq!(try_arrange_indices(0, &order), Ok(vec![]));
        assert_eq!(try_arrange_indices(4, &order), Ok(vec![1, 3, 2, 0]));
        assert_eq!(
            try_arrange_indices(5, &order),
            Err(ArrangementError::OutsideDomain)
        );
        assert_eq!(
            try_arrange_indices(usize::MAX, &order),
            Err(ArrangementError::OutsideDomain)
        );
    }
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn linear_registry_reservation_preserves_owned_mapping_and_capacity()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::resource_registry::ResourceRegistry;
    let mut owner = ResourceRegistry::<u64, Vec<u8>>::new();
    owner.register(7, vec![3, 1]);
    let payload_pointer = owner
        .lookup_ref(&7)
        .ok_or("missing retained payload")?
        .as_ptr();
    owner.try_reserve_entries(3)?;
    let capacity = owner.entries.capacity();
    let entries_pointer = owner.entries.as_ptr();
    assert_eq!(
        owner
            .lookup_ref(&7)
            .ok_or("missing payload after reservation")?
            .as_ptr(),
        payload_pointer
    );
    assert_eq!(owner.lookup_ref(&7), Some(&vec![3, 1]));
    owner.register(2, vec![4]);
    owner.register(9, vec![8]);
    owner.register(4, vec![6]);
    owner.register(2, vec![5]);
    assert_eq!(
        owner
            .entries
            .iter()
            .map(|(key, _)| *key)
            .collect::<Vec<_>>(),
        vec![7, 9, 4, 2]
    );
    assert_eq!(owner.lookup_ref(&2), Some(&vec![5]));
    assert_eq!(owner.lookup_ref(&7), Some(&vec![3, 1]));
    assert_eq!(owner.entries.capacity(), capacity);
    assert_eq!(owner.entries.as_ptr(), entries_pointer);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn linear_registry_reservation_refuses_oversized_storage_without_mutation()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::resource_registry::ResourceRegistry;
    let mut owner = ResourceRegistry::<u64, Vec<u8>>::new();
    owner.register(7, vec![3, 1]);
    owner.register(2, vec![8]);
    let entries_pointer = owner.entries.as_ptr();
    let payload_pointer = owner
        .lookup_ref(&7)
        .ok_or("missing retained payload")?
        .as_ptr();
    assert!(owner.try_reserve_entries(usize::MAX).is_err());
    assert_eq!(owner.entries, vec![(7, vec![3, 1]), (2, vec![8])]);
    assert_eq!(owner.entries.as_ptr(), entries_pointer);
    assert_eq!(
        owner
            .lookup_ref(&7)
            .ok_or("missing payload after refusal")?
            .as_ptr(),
        payload_pointer
    );
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn fallible_admission_selection_retains_canonical_initialization_and_ties()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::competitive_selection::CompetitiveSelectionHard;
    let mut owner = CompetitiveSelectionHard::try_new(3)?;
    assert_eq!(owner.scores, vec![0, 0, 0]);
    assert_eq!(owner.allocation, None);
    assert_eq!(owner.scores, CompetitiveSelectionHard::new(3).scores);
    let capacity = owner.scores.capacity();
    let pointer = owner.scores.as_ptr();
    owner.update_score(2, 1);
    owner.update_score(1, 1);
    owner.evaluate();
    assert_eq!(owner.allocation, Some(1));
    assert_eq!(owner.scores.capacity(), capacity);
    assert_eq!(owner.scores.as_ptr(), pointer);
    assert!(CompetitiveSelectionHard::try_new(usize::MAX).is_err());
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn fallible_admission_step_graph_retains_dependencies_and_refused_edges()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{StepState, modalities::step_graph::StepGraph};
    let edges = vec![(0, 1), (1, 2)];
    let pointer = edges.as_ptr();
    let mut owner = StepGraph::try_new(3, edges).map_err(|(error, _edges)| error)?;
    assert_eq!(owner.edges.as_ptr(), pointer);
    assert_eq!(
        owner.nstate,
        vec![StepState::Ready, StepState::NotReady, StepState::NotReady]
    );
    assert_eq!(owner.nstate, StepGraph::new(3, vec![(0, 1), (1, 2)]).nstate);
    let states_pointer = owner.nstate.as_ptr();
    assert!(!owner.start_running(1));
    assert!(owner.start_running(0));
    assert!(owner.complete_node(0));
    assert!(owner.become_ready(1));
    assert!(owner.start_running(1));
    assert!(owner.complete_node(1));
    assert!(owner.become_ready(2));
    assert!(owner.start_running(2));
    assert!(owner.complete_node(2));
    assert!(owner.done_stuttering());
    assert_eq!(owner.nstate.as_ptr(), states_pointer);
    let edges = vec![(0, 1)];
    let pointer = edges.as_ptr();
    let (_, returned) = StepGraph::try_new(usize::MAX, edges)
        .err()
        .ok_or("oversized state admitted")?;
    assert_eq!(returned, vec![(0, 1)]);
    assert_eq!(returned.as_ptr(), pointer);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn fallible_admission_actuation_retains_assignments_and_effect_scope()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::actuation_pass::ActuationPass;
    let assignments = vec![Some(7), None, Some(9)];
    let pointer = assignments.as_ptr();
    let mut owner =
        ActuationPass::try_new(assignments, 3).map_err(|(error, _assignments)| error)?;
    assert_eq!(owner.allocation.as_ptr(), pointer);
    assert_eq!(owner.effects, vec![None, None, None]);
    assert!(!owner.complete);
    let effects_pointer = owner.effects.as_ptr();
    owner.actuate(0);
    owner.actuate(2);
    owner.finish();
    assert_eq!(owner.effects, vec![Some(7), None, Some(9)]);
    assert!(owner.complete);
    assert_eq!(owner.effects.as_ptr(), effects_pointer);
    let empty = ActuationPass::try_new(vec![], 0).map_err(|(error, _assignments)| error)?;
    assert!(empty.allocation.is_empty() && empty.effects.is_empty() && !empty.complete);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn admitted_scalar_sequence_preserves_storage_and_order() -> Result<(), Box<dyn std::error::Error>>
{
    use automation_structures::modalities::sequential::Sequential;
    assert!(Sequential::try_new(usize::MAX, 10, 0).is_err());
    let mut s = Sequential::try_new(4, 10, 0)?;
    let pointer = s.history.as_ptr();
    let capacity = s.history.capacity();
    for value in [3, 1, 4, 2] {
        assert!(!s.complete_step(value));
        assert!(s.begin_step());
        assert!(!s.complete_step(10));
        assert!(s.complete_step(value));
        assert_eq!(s.history.as_ptr(), pointer);
        assert_eq!(s.history.capacity(), capacity);
    }
    assert_eq!(s.history, vec![3, 1, 4, 2]);
    assert!(s.done_stuttering());
    assert!(!s.begin_step());
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn admitted_fork_keeps_snapshot_storage_and_barrier() -> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::modalities::fork_join::ForkJoin;
    assert!(ForkJoin::try_new(usize::MAX, 10, 0).is_err());
    let mut s = ForkJoin::try_new(3, 10, 0)?;
    let pointers = (
        s.wstate.as_ptr(),
        s.wvalue.as_ptr(),
        s.output_snapshot.as_ptr(),
    );
    assert!(!s.produce_output());
    for (worker, value) in [3, 1, 4].into_iter().enumerate() {
        assert!(!s.barrier());
        assert!(s.start_worker(worker));
        assert!(s.complete_worker(worker, value));
    }
    assert!(s.barrier());
    assert!(s.produce_output());
    assert!(!s.produce_output());
    assert_eq!(s.output_snapshot, vec![3, 1, 4]);
    assert_eq!(
        (
            s.wstate.as_ptr(),
            s.wvalue.as_ptr(),
            s.output_snapshot.as_ptr()
        ),
        pointers
    );
    let mut empty = ForkJoin::try_new(0, 1, 0)?;
    assert!(empty.barrier());
    assert!(empty.produce_output());
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn admitted_federation_keeps_owner_storage_and_conservation()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::compositions::federated_budget::FederatedBudget;
    assert!(FederatedBudget::try_new(10, usize::MAX).is_err());
    let mut f = FederatedBudget::try_new(10, 2)?;
    let pointer = f.sub_pools.as_ptr();
    assert!(f.allocate_sub_pool(0, 7));
    assert!(!f.allocate_sub_pool(1, 4));
    assert!(f.allocate_from_sub_pool(0, 5));
    assert!(f.release_from_sub_pool(0, 5));
    assert_eq!(f.master.allocated, 7);
    let pool = f.sub_pools.first().ok_or("missing retained sub-pool")?;
    assert_eq!((pool.allocated, pool.reserved), (0, 7));
    assert_eq!(f.sub_pools.as_ptr(), pointer);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn admitted_audit_storage_frames_chain_on_reservation_failure()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::audit_sink::{AdditiveChain, AuditSink};
    let mut s = AuditSink::with_operator(4, AdditiveChain);
    s.try_reserve_records(4)?;
    let pointer = s.log.as_ptr();
    for value in [3, 1, 4, 2] {
        assert!(s.record(value));
        assert_eq!(s.log.as_ptr(), pointer);
    }
    let before = (s.committed_count(), s.carry(), s.latest());
    assert!(s.try_reserve_records(usize::MAX).is_err());
    assert_eq!((s.committed_count(), s.carry(), s.latest()), before);
    assert_eq!(s.log.as_ptr(), pointer);
    assert!(!s.record(1));
    assert_eq!(s.carry(), 10);
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn admitted_governor_reuses_complete_window() -> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::convergence_governor_phase_aware::ConvergenceGovernorPhaseAware;
    assert!(ConvergenceGovernorPhaseAware::try_new(1, 2, usize::MAX, 0).is_err());
    let mut g = ConvergenceGovernorPhaseAware::try_new(3, 6, 3, 9)?;
    assert!(!g.peak_observed);
    let pointer = g.delta_history.as_ptr();
    for round in 0..64 {
        let value = round % 10;
        g.update(value);
        assert!(g.delta_history.len() <= 3);
        assert_eq!(g.delta_history.as_ptr(), pointer);
        assert_eq!(g.delta_history.last(), Some(&value));
    }
    Ok(())
}

#[cfg(feature = "proof-api")]
#[test]
fn rate_clock_observation_matches_repeated_ticks() {
    use automation_structures::compositions::rate_limit::RateLimit;
    let mut observed = RateLimit::new(2, 5, 100);
    let mut ticked = RateLimit::new(2, 5, 100);
    for now in [0, 0, 3, 5, 27, 100] {
        while ticked.clock < now {
            ticked.tick();
        }
        assert!(observed.advance_clock_to(now));
        assert_eq!(observed.try_acquire(), ticked.try_acquire());
        assert_eq!(
            (
                observed.clock,
                observed.window_start,
                observed.budget.allocated
            ),
            (ticked.clock, ticked.window_start, ticked.budget.allocated)
        );
    }
    let before = (
        observed.clock,
        observed.window_start,
        observed.budget.allocated,
    );
    assert!(!observed.advance_clock_to(99));
    assert!(!observed.advance_clock_to(101));
    assert_eq!(
        (
            observed.clock,
            observed.window_start,
            observed.budget.allocated
        ),
        before
    );
}

#[cfg(feature = "proof-api")]
#[allow(dead_code)]
#[path = "../verification/downstream-verus/src/domains.rs"]
mod domain_witnesses;

#[test]
#[cfg(feature = "proof-api")]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn generic_propagation_retains_snapshot_and_refuses_without_marking()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::propagation_pass::PropagationPass;
    use domain_witnesses::{Bit, NeighborComplement};
    let mut p = PropagationPass::try_new(
        2,
        8,
        NeighborComplement { allowed: 2 },
        vec![],
        vec![Bit { set: false }; 2],
    )
    .map_err(|(error, _domain, _edges, _values)| error)?;
    let storage = (p.snapshot.as_ptr(), p.updated.as_ptr(), p.values.as_ptr());
    assert!(!p.try_update_node(0));
    for round in 0..8 {
        p.start_round();
        assert!(p.try_update_node(0));
        assert!(!p.try_update_node(0));
        assert!(!p.try_update_node(2));
        assert!(p.try_update_node(1));
        assert_eq!(
            p.values,
            vec![
                Bit {
                    set: round % 2 == 0
                };
                2
            ]
        );
        assert_eq!(
            p.snapshot,
            vec![
                Bit {
                    set: round % 2 != 0
                };
                2
            ]
        );
        p.end_round();
        assert_eq!(p.iteration, round + 1);
        assert_eq!(
            (p.snapshot.as_ptr(), p.updated.as_ptr(), p.values.as_ptr()),
            storage
        );
    }
    let mut refused = PropagationPass::try_new(
        2,
        1,
        NeighborComplement { allowed: 1 },
        vec![],
        vec![Bit { set: false }; 2],
    )
    .map_err(|(error, _domain, _edges, _values)| error)?;
    refused.start_round();
    assert!(!refused.try_update_node(1));
    assert_eq!(refused.values, vec![Bit { set: false }; 2]);
    assert_eq!(refused.updated, vec![false; 2]);
    let edges = vec![(0, 1)];
    let values = vec![Bit { set: false }; 2];
    let pointers = (edges.as_ptr(), values.as_ptr());
    // Capacity-overflow probes are ordinary Rust misuse of raw logical preconditions;
    // they check only error-path ownership, not admitted graph shape.
    let (_, domain, edges, values) = PropagationPass::try_new(
        usize::MAX,
        1,
        NeighborComplement { allowed: 2 },
        edges,
        values,
    )
    .err()
    .ok_or("overflow admitted")?;
    assert_eq!(domain.allowed, 2);
    assert_eq!((edges.as_ptr(), values.as_ptr()), pointers);
    Ok(())
}

#[test]
#[cfg(feature = "proof-api")]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions report test-oracle failures; fallible setup propagates typed errors"
)]
fn generic_traversal_retains_tokens_and_restores_domain_data()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::primitives::backtracking_traversal::BacktrackingTraversal;
    use domain_witnesses::{Bit, Toggle};
    let mut t = BacktrackingTraversal::try_new(Toggle { choices: 3 }, 3, Bit { set: false })
        .map_err(|(error, _domain, _initial)| error)?;
    t.try_reserve_visits(3)?;
    let storage = (t.path.as_ptr(), t.ledger.as_ptr(), t.visited.as_ptr());
    assert!(!t.can_descend(0, true));
    assert!(!t.can_descend(4, true));
    assert!(!t.can_descend(1, false));
    for choice in 1..=3 {
        for depth in 0..3 {
            t.descend(choice, true);
            assert_eq!(t.aux.set, depth % 2 == 0);
            assert_eq!(
                t.ledger.last().ok_or("missing retained undo token")?.saved,
                Bit {
                    set: depth % 2 != 0
                }
            );
            assert!(t.ledger.last().ok_or("missing retained undo token")?.delta);
        }
        assert!(!t.can_descend(1, true));
        assert!(t.can_visit());
        t.try_visit()?;
        assert!(!t.can_visit());
        assert_eq!(t.visited.last(), Some(&vec![choice; 3]));
        assert!(t.try_reserve_visits(usize::MAX).is_err());
        assert_eq!(t.visited.len(), usize::try_from(choice)?);
        for depth in (0..3).rev() {
            t.ascend();
            assert_eq!(t.aux.set, depth % 2 != 0);
        }
        assert_eq!(t.aux, Bit { set: false });
        assert!(t.path.is_empty() && t.ledger.is_empty());
        assert_eq!(
            (t.path.as_ptr(), t.ledger.as_ptr(), t.visited.as_ptr()),
            storage
        );
    }
    let (_, domain, initial) =
        BacktrackingTraversal::try_new(Toggle { choices: 3 }, usize::MAX, Bit { set: true })
            .err()
            .ok_or("overflow admitted")?;
    assert_eq!(domain.choices, 3);
    assert_eq!(initial, Bit { set: true });
    Ok(())
}

#[test]
#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions are independent test observations; fallible setup propagates errors"
)]
fn dynamic_candidates_extend_after_visits_and_seal_original_custody()
-> Result<(), Box<dyn std::error::Error>> {
    use automation_structures::{CandidateTraversal, CandidateTraversalError as Error};
    let context = Box::new("frozen context");
    let pointer = context.as_ref() as *const _;
    let mut owner = CandidateTraversal::try_new(context, 101, 5).map_err(|(error, _)| error)?;
    assert_eq!(owner.context().as_ref() as *const _, pointer);
    let first = owner
        .admit(None, Box::new(10), 4, 0)
        .map_err(|(error, _)| error)?;
    let second = owner
        .admit(None, Box::new(20), 7, 0)
        .map_err(|(error, _)| error)?;
    let original = Box::new(30);
    let original_pointer = original.as_ref() as *const _;
    let (error, returned) = owner
        .admit(Some(first), original, 3, 0)
        .err()
        .ok_or("pending parent admitted")?;
    assert_eq!(error, Error::ParentPending);
    assert_eq!(returned.as_ref() as *const _, original_pointer);
    assert_eq!(owner.pending(), 2);
    let mut owner = owner.finish().err().ok_or("pending owner sealed")?;
    assert_eq!(owner.step()?, Some(second));
    assert_eq!(owner.step()?, Some(first));
    assert_eq!(owner.context().as_ref() as *const _, pointer);
    // The refused consuming completion returns exactly the same owner.
    let mut owner = CandidateTraversal::try_new(Box::new("frozen context"), 102, 5)
        .map_err(|(error, _)| error)?;
    let root = owner
        .admit(None, Box::new(1), u64::MAX, 0)
        .map_err(|(error, _)| error)?;
    assert_eq!(owner.step()?, Some(root));
    let child = owner
        .admit(Some(root), Box::new(2), 4, 0)
        .map_err(|(error, _)| error)?;
    let other = owner
        .admit(None, Box::new(3), 4, 0)
        .map_err(|(error, _)| error)?;
    assert_eq!(owner.step()?, Some(child));
    let grandchild = owner
        .admit(Some(child), Box::new(4), 1, 0)
        .map_err(|(error, _)| error)?;
    assert_eq!(owner.step()?, Some(other));
    assert_eq!(owner.step()?, Some(grandchild));
    assert_eq!(owner.pending(), 0);
    assert_eq!(owner.step()?, None);
    assert!(owner.get(first).is_none());
    assert!(owner.get(second).is_none());
    let (error, returned) = owner
        .admit(Some(first), Box::new(9), 0, 0)
        .err()
        .ok_or("foreign parent admitted")?;
    assert_eq!((error, *returned), (Error::ForeignScope, 9));
    let (error, returned) = owner
        .admit(Some(child), Box::new(9), 5, 0)
        .err()
        .ok_or("invalid level admitted")?;
    assert_eq!((error, *returned), (Error::InvalidExtension, 9));
    let mut owner = owner.finish().err().ok_or("open owner sealed")?;
    owner.close();
    let (error, returned) = owner
        .admit(None, Box::new(9), 0, 0)
        .err()
        .ok_or("closed owner admitted")?;
    assert_eq!((error, *returned), (Error::Closed, 9));
    let done = owner.finish().map_err(|_| "closed drained owner refused")?;
    assert_eq!(done.len(), 4);
    assert_eq!(done.get(grandchild).map(|value| **value), Some(4));
    assert_eq!(**done.context(), "frozen context");
    let mut empty =
        CandidateTraversal::<_, Box<u64>>::try_new((), 103, 0).map_err(|(error, _)| error)?;
    let (error, returned) = empty
        .admit(None, Box::new(8), 0, 0)
        .err()
        .ok_or("zero capacity admitted")?;
    assert_eq!((error, *returned), (Error::CandidateCapacity, 8));
    empty.close();
    assert!(
        empty
            .finish()
            .map_err(|_| "empty completion refused")?
            .is_empty()
    );
    Ok(())
}
