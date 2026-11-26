#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "$0")/.." && pwd)
project=$(mktemp -d)
trap 'rm -rf -- "$project"' EXIT
git -C "$root" archive HEAD:lean | tar -xf - -C "$project"
git -C "$root" archive HEAD:comparator Challenge Challenge.lean comparator.json lakefile.toml | tar -xf - -C "$project"
cd "$project"
export LEAN_NUM_THREADS=1
lake exe cache get
lake --no-cache comparator --config=comparator.json
