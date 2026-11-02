#!/bin/bash
# `make present`: open the explainer page; its media is built locally by `make present-media` (not committed).
cd "$(dirname "$0")"
PORT=${PORT:-8763}
MINUTES=${PRESENT_MEDIA_MINUTES:-?}
missing=$(grep -o 'media/[A-Za-z0-9_.-]*\.\(mp4\|jpg\)' index.html | sort -u | while read -r f; do [ -f "$f" ] || echo "$f"; done)
if [ -n "$missing" ]; then
  echo "run \`make present-media\` first (about $MINUTES min)"
  if [ -t 0 ]; then
    read -r -p "Run it now? [y/N] " answer
    case "$answer" in [yY]*) make -C ../.. present-media || exit 1 ;; *) exit 1 ;; esac
  else
    exit 1
  fi
fi
./build_data.sh
exec python3 -I ../../Tools/serve_range.py "$PORT" . --open index.html
