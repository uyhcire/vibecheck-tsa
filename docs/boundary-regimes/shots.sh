#!/bin/sh
# Takes the demo screenshots listed by `regimes demo` (*/*-shots.sh), from the repo root, then shrinks
# each to a 1600 px JPEG. `shots.sh 01a 04` takes only those slices.
set -e
cd "$(dirname "$0")/../.."
(cd flight && cargo build --release --features jsb --bin cityflight)
for f in docs/boundary-regimes/*/*-shots.sh; do
  key=$(basename "$f" -shots.sh)
  if [ $# -gt 0 ]; then
    hit=0
    for k in "$@"; do case "$key" in "$k"*) hit=1 ;; esac; done
    [ $hit = 1 ] || continue
  fi
  echo "$key"
  sh "$f" 2>&1 | grep -v '^perf:' || true
done
for p in docs/boundary-regimes/*/shots/*.png; do
  [ -e "$p" ] || continue
  sips -s format jpeg -s formatOptions 82 -Z 1600 "$p" --out "${p%.png}.jpg" >/dev/null && rm "$p"
done
