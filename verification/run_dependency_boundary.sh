#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repository_root=$(dirname "$script_dir")
cd "$repository_root"

# The older pair is admitted only in the pinned proc-macro compilation closure.
# Exclude proc-macro edges, including their transitive dependencies, to inspect
# every target's runtime graph. A direct or transitive runtime leak must fail.
runtime_tree=$(cargo tree --locked --all-features --target all \
    --edges normal,no-proc-macro --prefix none)
case "$runtime_tree" in
    *'hashbrown v0.12.3'*|*'indexmap v1.9.3'*)
        printf '%s\n' 'Verus-only dependency entered the runtime graph' >&2
        exit 1
        ;;
esac
duplicates=$(cargo tree --locked --all-features --target all \
    --edges normal,no-proc-macro --duplicates)
if [ -n "$duplicates" ]; then
    printf '%s\n' "$duplicates" >&2
    exit 1
fi
printf '%s\n' 'Dependency boundary: pinned macro-only pair excluded; no runtime duplicates'
