//! Focused representation cost witness. This is not the analytical benchmark.
use automation_structures::primitives::resource_registry::{ByteKey, ResourceRegistry};
use std::{hint::black_box, time::Instant};

fn main() {
    let queries = 25_000u64;
    for groups in [32u64, 1024, 16384] {
        let mut linear = ResourceRegistry::new();
        let mut indexed = ResourceRegistry::new_indexed();
        assert!(indexed.try_reserve_entries(groups as usize));
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
        let expected: u64 = (0..queries).map(|q| (q * 73 + 19) % groups).sum();
        for _ in 0..5 {
            let started = Instant::now();
            let mut sum = 0;
            for q in 0..queries {
                let bytes = black_box(((q * 73 + 19) % groups).to_be_bytes());
                sum += *black_box(
                    linear
                        .lookup_query(&bytes.as_slice())
                        .expect("admitted key"),
                );
            }
            linear_ns.push(started.elapsed().as_nanos());
            assert_eq!(sum, expected);
            let started = Instant::now();
            let mut sum = 0;
            for q in 0..queries {
                let bytes = black_box(((q * 73 + 19) % groups).to_be_bytes());
                sum += *black_box(
                    indexed
                        .lookup_query(&bytes.as_slice())
                        .expect("admitted key"),
                );
            }
            indexed_ns.push(started.elapsed().as_nanos());
            assert_eq!(sum, expected);
        }
        // Sorting measurement samples is verification scaffolding, not Registry behavior.
        linear_ns.sort_unstable();
        indexed_ns.sort_unstable();
        println!(
            "{{\"groups\":{groups},\"queries\":{queries},\"repeats\":5,\"linear_median_ns\":{},\"indexed_median_ns\":{},\"indexed_capacity\":{}}}",
            linear_ns[2],
            indexed_ns[2],
            indexed.entries.capacity()
        );
    }
}
