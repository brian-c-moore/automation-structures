#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repository_root=$(dirname "$script_dir")
target_dir="${CARGO_TARGET_DIR:-$repository_root/target}"
binary_dir="$target_dir/debug"

cd "$repository_root"
selected_case=${KNOWN_ANSWER_CASE:-}
if [ -n "$selected_case" ]; then
    case "$selected_case" in
        *[!a-z_]*) printf '%s\n' 'Invalid known-answer case name' >&2; exit 1 ;;
    esac
    case "$selected_case" in
        *_kat|registry_index_probe) ;;
        *) printf '%s\n' 'Unknown known-answer case' >&2; exit 1 ;;
    esac
    test -f "verification/known-answer/$selected_case.rs"
fi
sh "$script_dir/run_dependency_boundary.sh"
cargo build --locked --all-features

# The standalone fixtures do not inherit Cargo's lint table. Read that exact
# reviewed policy rather than maintaining a second list of accepted practices.
policy_flags=$(awk '
    /^\[lints.rust\]/ { section = "rust"; next }
    /^\[lints.clippy\]/ { section = "clippy"; next }
    /^\[/ { section = "" }
    section != "" && /^[a-z_]+[[:space:]]*=[[:space:]]*"(allow|warn|deny|forbid)"[[:space:]]*$/ {
        name = $1; level = $3; gsub(/["\r]/, "", level)
        namespace = section == "clippy" ? "clippy::" : ""
        printf "--%s=%s%s\n", level, namespace, name
    }
' Cargo.toml)
if [ -z "$policy_flags" ]; then
    printf '%s\n' 'Missing standalone fixture lint policy' >&2
    exit 1
fi

status=0
for source in verification/known-answer/*_kat.rs verification/known-answer/registry_index_probe.rs; do
    name=$(basename "$source" .rs)
    if [ -n "$selected_case" ] && [ "$name" != "$selected_case" ]; then continue; fi
    binary="$binary_dir/automation-structures-$name"
    printf 'KAT_LINT_SOURCE: %s\n' "$source"
    if ! rustfmt --edition 2024 --check "$source"; then
        status=1
        continue
    fi
    set --
    for flag in $policy_flags; do
        # This test-only physical binding requires GlobalAlloc's unsafe methods.
        # Deny still enforces every other site; the implementation has a narrow
        # documented expectation. Production and all other fixtures forbid unsafe.
        if [ "$name" = allocation_refusal_kat ] && [ "$flag" = --forbid=unsafe_code ]; then
            flag=--deny=unsafe_code
        fi
        set -- "$@" "$flag"
    done
    if clippy-driver \
        --edition 2024 \
        "$source" \
        --extern automation_structures="$target_dir/debug/libautomation_structures.rlib" \
        -L "dependency=$target_dir/debug/deps" \
        -o "$binary" "$@"; then
        if [ "$name" != registry_index_probe ] && ! "$binary"; then status=1; fi
    else
        status=1
    fi
done
exit "$status"
