#!/bin/bash
# The page's derived data, rebuilt from what is already recorded (no recording, no encoding); `make present` runs it.
# Each step runs only if its inputs exist (the recordings and replays `make present-media` leaves in REC and PROOF_DUMP).
cd "$(dirname "$0")"
PROOF_DUMP=${PROOF_DUMP:-/tmp/explainer-dump}
REC=${REC:-/tmp/explainer-rec}
skip() { echo "skipped: $1"; }

python3 -I cc_data.py --from-traces > /dev/null && echo "close-call charts: rebuilt from media/traces/cc-*.trace.jsonl"

for clip in towergap:showcase towergap-high:showcase dive:ep1001; do
  name=${clip%%:*} run=${clip#*:}
  trace=$REC/proof-$name/trace.jsonl
  settle=$([ "$name" = dive ] && echo "--settle 53.34")
  if [ ! -f "$trace" ]; then skip "proof clip $name (no $trace; make present-media)"
  elif [ ! -f "$PROOF_DUMP/$run/ticks.jsonl" ]; then skip "proof clip $name (no $PROOF_DUMP/$run; make present-media)"
  elif python3 -I proof_data.py "$name" "$trace" "$PROOF_DUMP/$run" $settle > "media/proof-$name.js.tmp"; then
    mv "media/proof-$name.js.tmp" "media/proof-$name.js" && echo "proof clip $name: rebuilt"
  else rm -f "media/proof-$name.js.tmp"; echo "proof clip $name: NOT rebuilt (the recording and the replay disagree; re-record with make present-media)"
  fi
done

if [ -f "$PROOF_DUMP/showcase/ticks.jsonl" ] && [ -f "$PROOF_DUMP/showcase-off/ticks.jsonl" ]; then
  python3 -I plate_data.py "$PROOF_DUMP/showcase" "$PROOF_DUMP/showcase-off" > /dev/null && echo "Tower gap plate: rebuilt"
else
  skip "Tower gap plate (no $PROOF_DUMP/showcase and showcase-off; make present-media)"
fi
