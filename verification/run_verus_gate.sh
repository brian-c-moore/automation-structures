#!/bin/sh
set -eu

verus_bin="${VERUS_BIN:-/opt/verus/verus-x86-linux/verus}"
output_dir="${1:-/tmp/automation-structures-verus}"

mkdir -p "$output_dir"

"$verus_bin" \
    src/lib.rs \
    --cfg 'feature="proof-api"' \
    --crate-name automation_structures \
    --crate-type=lib \
    --compile \
    --out-dir "$output_dir" \
    --triggers-mode silent \
    --multiple-errors 24
