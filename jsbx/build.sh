#!/bin/sh
# usage: jsbx/build.sh [on|off]   (JSBSim build with -ffp-contract=on or off)
set -e
V=${1:-on}
D=$(cd "$(dirname "$0")/.." && pwd)
c++ -std=c++17 -O2 -ffp-contract=$V -I"$D/ext/jsbsim/src" -I"$D/ext/build-$V/src" \
  "$D/jsbx/harness.cpp" "$D/ext/build-$V/src/libJSBSim.a" -o "$D/ext/harness-$V"
