#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 RunValidation.v|RunDerivationShrinking.v" >&2
  exit 2
fi

case "$1" in
  RunValidation.v|RunDerivationShrinking.v) ;;
  *)
    echo "refusing unrecognized runner: $1" >&2
    exit 2
    ;;
esac

task_dir=$(cd "$(dirname "$0")" && pwd)
rss_limit_kib=${SMUSNI_STEP0_RSS_LIMIT_KIB:-8388608}
wall_limit=${SMUSNI_STEP0_WALL_LIMIT:-300s}

cd "$task_dir"
ulimit -v "$rss_limit_kib"
exec /usr/bin/time -f \
  'bounded_runner real=%e user=%U sys=%S maxrss=%M exit=%x' \
  timeout --signal=TERM "$wall_limit" \
  opam exec --switch smusni-pilot-rocq -- coqc "$1"
