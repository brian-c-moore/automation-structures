#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)

package_root=$(sh "$script_dir/prepare_package.sh")

# Run the shipped crate's own tests and known-answer sources from the exact
# unpacked publication archive.
cargo test \
    --locked \
    --manifest-path "$package_root/Cargo.toml" \
    --all-targets \
    --all-features
cargo test \
    --locked \
    --manifest-path "$package_root/Cargo.toml" \
    --doc \
    --all-features
RUSTDOCFLAGS="${RUSTDOCFLAGS:--D warnings}" cargo doc \
    --locked \
    --manifest-path "$package_root/Cargo.toml" \
    --no-deps \
    --all-features
sh "$package_root/verification/run_known_answer.sh"

# Exercise the complete public catalog from the exact unpacked publication
# archive, not from the repository checkout.
cargo run \
    --locked \
    --manifest-path "$package_root/Cargo.toml" \
    --example catalog

# Compile and run a separate package whose dependency points at the unpacked
# archive. Cargo excludes nested packages from .crate files, so the consumer is
# copied to an isolated temporary directory before its path is rewritten.
consumer_root=$(mktemp -d)
cleanup() {
    rm -rf -- "$consumer_root"
}
trap cleanup EXIT HUP INT TERM

sh "$package_root/verification/prepare_path_consumer.sh" \
    "$package_root/verification/downstream-cargo" \
    "$consumer_root" \
    "$package_root"

cargo run --locked --manifest-path "$consumer_root/Cargo.toml"
