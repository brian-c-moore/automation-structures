#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repository_root=$(dirname "$script_dir")
target_dir="${CARGO_TARGET_DIR:-$repository_root/target}"
binary_dir="$target_dir/debug"

cd "$repository_root"
cargo build --locked --all-features

for source in verification/known-answer/*_kat.rs; do
    name=$(basename "$source" .rs)
    binary="$binary_dir/automation-structures-$name"
    rustc \
        --edition 2021 \
        "$source" \
        --extern automation_structures="$target_dir/debug/libautomation_structures.rlib" \
        -L "dependency=$target_dir/debug/deps" \
        -o "$binary"
    "$binary"
done
