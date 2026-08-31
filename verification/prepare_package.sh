#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repository_root=$(dirname "$script_dir")

case "${CARGO_TARGET_DIR:-}" in
    "") target_dir="$repository_root/target" ;;
    /*) target_dir="$CARGO_TARGET_DIR" ;;
    *) target_dir="$repository_root/$CARGO_TARGET_DIR" ;;
esac

cd "$repository_root"
if [ "${PACKAGE_ALLOW_DIRTY:-0}" = "1" ]; then
    cargo package --locked --allow-dirty 1>&2
else
    cargo package --locked 1>&2
fi

package_id=$(cargo pkgid)
version=${package_id##*#}
version=${version##*@}
package_root="$target_dir/package/automation-structures-$version"
test -f "$package_root/Cargo.toml"
printf '%s\n' "$package_root"
