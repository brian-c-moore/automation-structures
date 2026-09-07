#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repository_root=$(dirname "$script_dir")
output_dir="${1:-/tmp/automation-structures-verus}"

# Select the cargo-verus shipped beside the checksum-pinned verifier. Cargo
# resolves the ordinary data-library dependencies from the package lockfile.
if [ -n "${VERUS_BIN:-}" ]; then
    test -x "$VERUS_BIN"
    PATH="$(dirname "$VERUS_BIN"):$PATH"
    export PATH
fi

mkdir -p "$output_dir"
CARGO_TARGET_DIR=$(CDPATH='' cd -- "$output_dir" && pwd)
export CARGO_TARGET_DIR
cd "$repository_root"

if [ -n "${CARGO_VENDOR_CONFIG:-}" ]; then
    cargo verus build --locked --all-features --offline \
        --config "$CARGO_VENDOR_CONFIG" \
        --fwd-verus-args-to roots -- --triggers-mode silent --multiple-errors 24
else
    cargo verus build --locked --all-features \
        --fwd-verus-args-to roots -- --triggers-mode silent --multiple-errors 24
fi
