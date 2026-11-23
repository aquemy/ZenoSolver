#!/usr/bin/env bash
# Run zeno-check on the test certificates and compare the verdicts with the expected ones:
#   test/certificates/accepted/*  must be accepted (exit code 0)
#   test/certificates/rejected/*  must be rejected (exit code 1)
# Usage, from lean/: bash test/run.sh [path/to/zeno-check]
set -u
cd "$(dirname "$0")/.."
bin=${1:-.lake/build/bin/zeno-check}
status=0

expect() {
    local dir=$1 want=$2 f out code
    for f in test/certificates/"$dir"/*.cert; do
        out=$("$bin" "$f")
        code=$?
        if [ "$code" -eq "$want" ]; then
            echo "ok    $f: $out"
        else
            echo "FAIL  $f: exit $code, expected $want: $out"
            status=1
        fi
    done
}

expect accepted 0
expect rejected 1
exit $status
