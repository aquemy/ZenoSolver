#!/usr/bin/env bash
# Benchmark the solver variants on fixed instances.
#
# Usage: bench/run.sh <build-dir> [runs]
#
# For each instance and variant, prints the median wall time over <runs> runs
# (default 3) and the solver's statistics line:
#   n t p PPPs evaluations front-size pareto-size solver-ms
# Uses hyperfine for timing when it is installed.
set -euo pipefail

build="${1:?usage: $0 <build-dir> [runs]}"
runs="${2:-3}"
variants=(zenoSolver zenoSolver_naive zenoSolver_noDuplicate)

# Instances from the baseline measurements (Release, Apple M4 Max):
# from about 0.5 s to about 1 min per variant.
instances=(
    "-n 10 -t 6 -p 3"
    "-n 20 -t 5 -p 2"
    "-n 10 -t 8 -p 4"
    "-n 12 -t 7 -p 3"
)

median() { sort -n | awk '{a[NR]=$1} END {print (NR % 2) ? a[(NR+1)/2] : (a[NR/2] + a[NR/2+1]) / 2}'; }

printf "%-22s %-18s %10s  %s\n" "variant" "instance" "median_s" "stats"
for instance in "${instances[@]}"; do
    for variant in "${variants[@]}"; do
        exe="$build/$variant"
        [ -x "$exe" ] || { echo "missing $exe" >&2; exit 1; }
        # shellcheck disable=SC2086
        stats=$("$exe" $instance 2>&1 >/dev/null | tail -n 1)
        if command -v hyperfine >/dev/null 2>&1; then
            json=$(mktemp)
            hyperfine --runs "$runs" --style none --export-json "$json" "$exe $instance" >/dev/null 2>&1
            seconds=$(python3 -c 'import json,sys; print(f"{json.load(open(sys.argv[1]))["results"][0]["median"]:.3f}")' "$json")
            rm -f "$json"
        else
            seconds=$(for _ in $(seq "$runs"); do
                start=$(python3 -c 'import time; print(time.time())')
                # shellcheck disable=SC2086
                "$exe" $instance >/dev/null 2>&1
                python3 -c "import time; print(f'{time.time() - $start:.3f}')"
            done | median)
        fi
        printf "%-22s %-18s %10s  %s\n" "$variant" "$instance" "$seconds" "$stats"
    done
done
