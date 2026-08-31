#!/bin/sh
set -eu

source_root=$1
consumer_root=$2
dependency_root=$3

test -f "$source_root/Cargo.toml.template"
test -d "$source_root/src"
test -f "$dependency_root/Cargo.toml"

if command -v cygpath >/dev/null 2>&1; then
    dependency_root=$(cygpath -m "$dependency_root")
fi

mkdir -p "$consumer_root"
cp -R "$source_root/src" "$consumer_root/src"

escaped_dependency_root=$(printf '%s\n' "$dependency_root" | sed 's/[&|]/\\&/g')
sed \
    "s|path = \"../..\"|path = \"$escaped_dependency_root\"|" \
    "$source_root/Cargo.toml.template" \
    > "$consumer_root/Cargo.toml"

cargo generate-lockfile --manifest-path "$consumer_root/Cargo.toml"
