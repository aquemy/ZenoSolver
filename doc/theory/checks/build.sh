#!/usr/bin/env bash
# Build the check programs into bin/ next to this script.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$here/bin"
for prog in treedp theorychecks truth graph_truth scale_g waiting_search config_front simple_plans; do
    "${CXX:-c++}" -std=c++17 -O2 "$here/$prog.cpp" -o "$here/bin/$prog"
done
echo "built: $(ls "$here/bin" | tr '\n' ' ')"
