#!/bin/bash
# Fly the demo while sampling it, for offline analysis: Tools/profile-fly.sh OUTDIR FILTER [demo flags...]
# Writes OUTDIR/machine.txt (load, top CPU users), app.log (CITYGATE_STATS tick times), sample1..N.txt (macOS `sample`).
set -u
out=$1; filt=$2; shift 2
mkdir -p "$out"; rm -f "$out"/sample*.txt
cd "$(dirname "$0")/../flight"
{ echo "== start $(date)"; uptime; echo "cores $(sysctl -n hw.ncpu)"; ps -axo pcpu,command -r | head -12 | cut -c1-140; } > "$out/machine.txt"
CITYGATE_STATS=1 ./target/release/cityflight --safety-filter "$filt" "$@" > "$out/app.log" 2>&1 &
pid=$!
echo "cityflight running (pid $pid). Fly as usual for at least a minute, then close the window."
sleep 4
i=0
while kill -0 "$pid" 2>/dev/null; do
  i=$((i + 1)); sample "$pid" 15 1 -mayDie -file "$out/sample$i.txt" >/dev/null 2>&1 || true
  [ "$i" -ge 12 ] && break
done
wait "$pid" 2>/dev/null
{ echo "== end $(date)"; uptime; ps -axo pcpu,command -r | head -12 | cut -c1-140; } >> "$out/machine.txt"
echo "Profile written to $out ($i sample files)."
