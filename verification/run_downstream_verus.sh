#!/bin/sh
set -eu

run_gate() {
    script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
    repository_root=$(dirname "$script_dir")

    if [ -n "${VERUS_WORK_COPY:-}" ]; then
        mkdir -p "$VERUS_WORK_COPY"
        tar -C "$repository_root" \
            --exclude=.git \
            --exclude=target \
            -cf - . | tar -C "$VERUS_WORK_COPY" -xf -
        repository_root="$VERUS_WORK_COPY"
    fi

    if [ -n "${VERUS_DEPENDENCY_ROOT:-}" ]; then
        dependency_root=$(CDPATH='' cd -- "$VERUS_DEPENDENCY_ROOT" && pwd)
    else
        dependency_root="$repository_root"
    fi

    consumer_root=$(mktemp -d)
    cleanup() {
        rm -rf -- "$consumer_root"
    }
    trap cleanup EXIT HUP INT TERM
    sh "$repository_root/verification/prepare_path_consumer.sh" \
        "$repository_root/verification/downstream-verus" \
        "$consumer_root" \
        "$dependency_root"
    manifest_path="$consumer_root/Cargo.toml"
    cd "$repository_root"

    if [ -n "${CARGO_VENDOR_CONFIG:-}" ]; then
        cargo verus build \
            --manifest-path "$manifest_path" \
            --offline \
            --locked \
            --config "$CARGO_VENDOR_CONFIG"
    else
        cargo verus build --manifest-path "$manifest_path" --locked
    fi
}

if [ -n "${VERUS_EVIDENCE_DIR:-}" ]; then
    mkdir -p "$VERUS_EVIDENCE_DIR"
    if run_gate >"$VERUS_EVIDENCE_DIR/downstream-verus.log" 2>&1; then
        printf '0\n' >"$VERUS_EVIDENCE_DIR/downstream-verus.status"
    else
        status=$?
        printf '%s\n' "$status" >"$VERUS_EVIDENCE_DIR/downstream-verus.status"
        cat "$VERUS_EVIDENCE_DIR/downstream-verus.log"
        exit "$status"
    fi
    cat "$VERUS_EVIDENCE_DIR/downstream-verus.log"
else
    run_gate
fi
