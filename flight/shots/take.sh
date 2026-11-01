#!/bin/sh
# Take the standard screenshot set: shots/take.sh <tag> [extra demo flags...]
# Writes full-size PNGs to /tmp/cfshots/<tag>_*.png and small JPEGs to shots/<tag>_*.jpg.
set -e
cd "$(dirname "$0")/.."
tag=$1; shift
mkdir -p /tmp/cfshots
for v in "a 1 0 120" "b 3 2 200" "c 2 1 90" "d 4 3 150"; do
  set -- $v "$@"
  name=$1; sc=$2; cam=$3; fr=$4; shift 4
  ./target/release/cityflight --shot /tmp/cfshots/${tag}_$name.png --frames $fr --scenario $sc --cam $cam "$@" 2>&1 | grep -E "fps|gpu|error|panic" || true
  sips -s format jpeg -s formatOptions 60 -Z 960 /tmp/cfshots/${tag}_$name.png --out shots/${tag}_$name.jpg >/dev/null
done
