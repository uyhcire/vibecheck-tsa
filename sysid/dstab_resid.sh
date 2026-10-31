#!/bin/bash
# Lean residuals for OUT/NAME.csv in ~36k-row chunks (jsbresid is quadratic in rows); writes OUT/NAME.res.csv.
OUT=${1:-/tmp/dstab}; N=$2
D=$OUT/chunks.$N; rm -rf $D; mkdir -p $D
.venv/bin/python -I - $OUT/$N.csv $D <<'P'
import sys
src, d = sys.argv[1:3]
f = open(src); hdr = f.readline(); out = None; n = 0; last = None; idx = -1
for line in f:
    ep = line.split(',', 2)[0]
    if ep != last and (out is None or n > 36000):
        if out: out.close()
        idx += 1; out = open(f'{d}/c{idx}.csv', 'w'); out.write(hdr); n = 0
    out.write(line); n += 1; last = ep
out.close()
P
ls $D/c*.csv | xargs -P 12 -I{} sh -c '.lake/build/bin/jsbresid {} --dump {}.res > /dev/null'
K=$(ls $D/c*.csv | wc -l)
head -1 $D/c0.csv.res > $OUT/$N.res.csv
for i in $(seq 0 $((K-1))); do tail -n +2 $D/c$i.csv.res >> $OUT/$N.res.csv; echo >> $OUT/$N.res.csv; done
sed -i '' '/^$/d' $OUT/$N.res.csv
rm -rf $D; wc -l $OUT/$N.res.csv
