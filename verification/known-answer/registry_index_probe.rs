//! Focused representation cost witness. This is not the analytical benchmark.
use automation_structures::primitives::resource_registry::{ByteKey, ResourceRegistry};
use std::{hint::black_box, time::Instant};

fn probe_key(query: u64, groups: u64) -> Result<u64, &'static str> {
    query
        .checked_mul(73)
        .and_then(|value| value.checked_add(19))
        .and_then(|value| value.checked_rem(groups))
        .ok_or("invalid probe key arithmetic")
}

#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions are independent representation-cost oracles; fallible setup propagates typed errors"
)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let queries = 25_000u64;
    for groups in [32u64, 1024, 16384] {
        let mut linear = ResourceRegistry::new();
        let mut indexed = ResourceRegistry::new_indexed();
        assert!(indexed.try_reserve_entries(usize::try_from(groups)?));
        for i in 0..groups {
            linear.register_key(ByteKey::from_bytes(i.to_be_bytes().to_vec()), i);
            assert!(
                indexed
                    .try_register_key(ByteKey::from_bytes(i.to_be_bytes().to_vec()), i)
                    .is_ok()
            );
        }
        let mut linear_ns = Vec::new();
        let mut indexed_ns = Vec::new();
        let expected = (0..queries).try_fold(0u64, |total, query| {
            total
                .checked_add(probe_key(query, groups)?)
                .ok_or("probe total overflow")
        })?;
        for _ in 0..5 {
            let started = Instant::now();
            let mut sum = 0u64;
            for q in 0..queries {
                let bytes = black_box(probe_key(q, groups)?.to_be_bytes());
                sum = sum
                    .checked_add(*black_box(
                        linear
                            .lookup_query(&bytes.as_slice())
                            .ok_or("missing admitted linear key")?,
                    ))
                    .ok_or("linear probe total overflow")?;
            }
            linear_ns.push(started.elapsed().as_nanos());
            assert_eq!(sum, expected);
            let started = Instant::now();
            let mut sum = 0u64;
            for q in 0..queries {
                let bytes = black_box(probe_key(q, groups)?.to_be_bytes());
                sum = sum
                    .checked_add(*black_box(
                        indexed
                            .lookup_query(&bytes.as_slice())
                            .ok_or("missing admitted indexed key")?,
                    ))
                    .ok_or("indexed probe total overflow")?;
            }
            indexed_ns.push(started.elapsed().as_nanos());
            assert_eq!(sum, expected);
        }
        // Sorting measurement samples is verification scaffolding, not Registry behavior.
        linear_ns.sort_unstable();
        indexed_ns.sort_unstable();
        println!(
            "{{\"groups\":{groups},\"queries\":{queries},\"repeats\":5,\"linear_median_ns\":{},\"indexed_median_ns\":{},\"indexed_capacity\":{}}}",
            linear_ns.get(2).ok_or("missing linear median sample")?,
            indexed_ns.get(2).ok_or("missing indexed median sample")?,
            indexed.entries.capacity()
        );
    }
    Ok(())
}
