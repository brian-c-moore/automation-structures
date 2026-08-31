#!/bin/sh
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
package_root=$(sh "$script_dir/prepare_package.sh")

VERUS_DEPENDENCY_ROOT="$package_root"
export VERUS_DEPENDENCY_ROOT
sh "$package_root/verification/run_downstream_verus.sh"
