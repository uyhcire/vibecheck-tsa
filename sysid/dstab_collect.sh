#!/bin/bash
set -e
OUT=${1:-/tmp/dstab}; mkdir -p $OUT; PY=.venv/bin/python
run() {
  n=$1; ns=$2; per=$3; s0=$4; shift 4
  for i in $(seq 0 $((ns-1))); do
    $PY -I sysid/collect.py $OUT/$n.$i.csv $per 900 $((s0+i)) rud0 ep0=$((i*per)) meta=$OUT/$n.$i.meta.csv "$@" > /dev/null &
  done
}
run main 12 100 100 style=regimes vmin=60 vmax=120 hmin=1000 hmax=8000
run base 4 100 200 style=mixed
run load 4 100 300 style=regimes vmin=60 vmax=120 hmin=1000 hmax=8000 load=1
wait
for n in main base load; do
  f=$(ls $OUT/$n.*.csv | grep -v meta | sort -V)
  head -1 $(echo $f | cut -d' ' -f1) > $OUT/$n.csv; for x in $f; do tail -n +2 $x >> $OUT/$n.csv; done
  m=$(ls $OUT/$n.*.meta.csv | sort -V); head -1 $(echo $m | cut -d' ' -f1) > $OUT/$n.meta.csv; for x in $m; do tail -n +2 $x >> $OUT/$n.meta.csv; done
  rm -f $f $m
done
