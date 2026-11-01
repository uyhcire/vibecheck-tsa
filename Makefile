# `make install && make run` must work from a fresh clone (see rules.md).
SHELL := /bin/bash
ELAN_HOME ?= $(HOME)/.elan
export PATH := $(ELAN_HOME)/bin:/opt/homebrew/bin:/usr/local/bin:$(PATH)

SDL_PREFIX = $(shell brew --prefix sdl3 2>/dev/null || echo /opt/homebrew/opt/sdl3)
LAKE_OPTS = -K sdl=$(SDL_PREFIX)

.PHONY: install run build verify proofs test filter-lib filter-test gate gate-example gate-check fly fly-lean fly-off showcase crashes crashes-lean adversary harness regimes plantcheck export pdf help clean

install:
	@if ! command -v elan >/dev/null 2>&1; then \
	  echo "Installing elan..."; \
	  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
	    | sh -s -- -y --default-toolchain none; \
	fi
	@if ! brew list sdl3 >/dev/null 2>&1; then \
	  if command -v brew >/dev/null 2>&1; then brew install sdl3; \
	  else echo "SDL3 is required: install Homebrew (https://brew.sh), then rerun make install."; exit 1; fi; \
	fi
	lake build $(LAKE_OPTS)

build:
	lake build $(LAKE_OPTS)

run: build
	.lake/build/bin/vibecheck

verify:
	lake build $(LAKE_OPTS) Vibecheck Envelope GateSafety CityGate
	lake env lean Tools/Audit.lean
	lake env lean Tools/EnvelopeAudit.lean
	lake env lean Tools/GateSafetyAudit.lean
	lake env lean Tools/CityGateAudit.lean
	lake build $(LAKE_OPTS) Spec.EndSetsExamples CityGate.EndSets
	lake env lean Tools/EndSetsAudit.lean
	lake build $(LAKE_OPTS) CityGate.SpecBridge SpecBridgeNative
	lake env lean Tools/SpecBridgeAudit.lean

proofs:
	cd proofs && lake exe cache get && lake build && lake env lean Proofs/Audit.lean

test: build
	lake build $(LAKE_OPTS) simtest
	.lake/build/bin/simtest 1 160

filter-lib:
	lake build $(LAKE_OPTS) libvcfilter libvcfilter_static

# needs .venv with jsbsim (sysid/README.md)
filter-test: filter-lib
	.venv/bin/python -I host/conformance.py --leak-ticks 200000
	.venv/bin/python -I host/lockstep.py --episodes 100

# libgate: the gatekeeper filter as a C library (gate/gate.h); dist/ holds libgate.dylib, libcityjsb.dylib, gate.h.
gate:
	lake build $(LAKE_OPTS) libcityjsb
	cargo build --release --manifest-path gate/Cargo.toml --lib
	mkdir -p dist && cp gate/target/release/libgate.dylib .lake/build/lib/libcityjsb.dylib gate/gate.h c/cityjsb.h dist/

gate-example: gate
	cc -O2 -Wall -Idist gate/examples/gate_example.c -Ldist -lgate -lcityjsb -Wl,-rpath,@executable_path -o dist/gate_example
	dist/gate_example

gate-check: gate
	cargo run --release --manifest-path gate/Cargo.toml --bin gatecheck -- 20 --threads 4

# The city flight demo (flight/, cityflight). FILTER picks the safety filter (exact-rollout, exact-rollout-lean,
# exact, fitted, fitted25); ARGS adds flags, e.g. `make fly ARGS="--episode 59 --paths"`.
FILTER ?= exact-rollout
ARGS ?=
N ?= 20
OUT ?= /tmp/$@
CITY = lake build $(LAKE_OPTS) libcityjsb && cd flight &&
CARGO_HEADLESS = cargo run --release --no-default-features --features jsb --bin

fly:
	$(CITY) cargo run --release --features jsb -- --safety-filter $(FILTER) $(ARGS)
fly-lean:
	$(MAKE) fly FILTER=exact-rollout-lean
fly-off:
	$(MAKE) fly ARGS="--off $(ARGS)"
# Tower gap with the scripted showcase pilot and the cinematic camera.
showcase:
	$(MAKE) fly ARGS="--showcase --cinematic --paths $(ARGS)"

# Headless crash test: N hostile episodes plus the kamikaze scenarios, results in OUT.
crashes:
	$(CITY) $(CARGO_HEADLESS) crashes -- $(OUT) $(N) --safety-filter $(FILTER) $(ARGS)
crashes-lean:
	$(MAKE) crashes FILTER=exact-rollout-lean
# Gap-guided adversary: N verified starts, results in OUT.
adversary:
	$(CITY) $(CARGO_HEADLESS) adversary -- $(OUT) $(FILTER) $(N) $(ARGS)
# Point-mass acceptance harness (Luis's original filters).
harness:
	cd flight && cargo run --release --no-default-features --bin harness -- $(N) $(ARGS)
# Boundary-regime slices (docs/boundary-regimes): regenerate every slice, then print the index table.
regimes:
	$(CITY) $(CARGO_HEADLESS) regimes -- run $(ARGS) && $(CARGO_HEADLESS) regimes -- index

# Plant and Lean-gate spot checks: the JsbExact plant, state import, the Lean gate's street escape, the 4 spec starts.
plantcheck:
	lake build $(LAKE_OPTS) cityplanttest cityimporttest citygatespot specbridgeinit
	.lake/build/bin/cityplanttest
	.lake/build/bin/cityimporttest
	.lake/build/bin/citygatespot
	.lake/build/bin/specbridgeinit

# The city as plain files for other simulators (docs/xplane-integration.md), checked bit for bit.
export:
	cargo run --release --manifest-path Tools/city-export/Cargo.toml -- map city-map
	cargo run --release --manifest-path Tools/city-export/Cargo.toml -- check city-map

# The informal TermSound proof (docs/termsound-proof.tex) as PDF; needs tectonic.
pdf:
	cd docs && tectonic termsound-proof.tex

help:
	@echo "Fly:      make fly | fly-lean | fly-off | showcase   (FILTER=..., ARGS=\"...\")"
	@echo "Test:     make crashes | crashes-lean | adversary | harness | regimes | plantcheck | test   (N=..., OUT=...)"
	@echo "Proofs:   make verify | proofs"
	@echo "Libs:     make gate | gate-example | gate-check | filter-lib | filter-test | export"
	@echo "Docs:     make pdf"
	@echo "Lean app: make install | build | run | clean"

clean:
	lake clean
