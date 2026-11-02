# `make install && make run` must work from a fresh clone (see rules.md).
SHELL := /bin/bash
ELAN_HOME ?= $(HOME)/.elan
export PATH := $(ELAN_HOME)/bin:/opt/homebrew/bin:/usr/local/bin:$(PATH)

SDL_PREFIX = $(shell brew --prefix sdl3 2>/dev/null || echo /opt/homebrew/opt/sdl3)
LAKE_OPTS = -K sdl=$(SDL_PREFIX)

.PHONY: install
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

.PHONY: build
build:
	lake build $(LAKE_OPTS)

.PHONY: run
run: build
	.lake/build/bin/vibecheck

.PHONY: verify
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

.PHONY: proofs
proofs:
	cd proofs && lake exe cache get && lake build && lake env lean Proofs/Audit.lean

# point-mass safe region against the spec's Crash (prints its axioms)
.PHONY: safe-region
safe-region:
	cd proofs && lake exe cache get && lake build Proofs.SafeRegion

.PHONY: test
test: build
	lake build $(LAKE_OPTS) simtest
	.lake/build/bin/simtest 1 160

.PHONY: filter-lib
filter-lib:
	lake build $(LAKE_OPTS) libvcfilter libvcfilter_static

# needs .venv with jsbsim (sysid/README.md)
.PHONY: filter-test
filter-test: filter-lib
	.venv/bin/python -I host/conformance.py --leak-ticks 200000
	.venv/bin/python -I host/lockstep.py --episodes 100

# libgate: the gatekeeper filter as a C library (gate/gate.h); dist/ holds libgate.dylib, libcityjsb.dylib, gate.h.
.PHONY: gate
gate:
	lake build $(LAKE_OPTS) libcityjsb
	cargo build --release --manifest-path gate/Cargo.toml --lib
	mkdir -p dist && cp gate/target/release/libgate.dylib .lake/build/lib/libcityjsb.dylib gate/gate.h c/cityjsb.h dist/

.PHONY: gate-example
gate-example: gate
	cc -O2 -Wall -Idist gate/examples/gate_example.c -Ldist -lgate -lcityjsb -Wl,-rpath,@executable_path -o dist/gate_example
	dist/gate_example

.PHONY: gate-check
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

.PHONY: fly
fly:
	$(CITY) cargo run --release --features jsb -- --safety-filter $(FILTER) $(ARGS)
.PHONY: fly-lean
fly-lean:
	$(MAKE) fly FILTER=exact-rollout-lean
.PHONY: fly-off
fly-off:
	$(MAKE) fly ARGS="--off $(ARGS)"
# Tower gap with the scripted showcase pilot and the cinematic camera.
.PHONY: showcase
showcase:
	$(MAKE) fly ARGS="--showcase --cinematic --paths $(ARGS)"

# Record the demo frame by frame into OUT (PNGs plus frames.csv), e.g.
# `make record OUT=/tmp/dive ARGS="--showcase --cinematic --frames 1800 --record-every 2 --record-scale 2"`.
.PHONY: record
record:
	$(MAKE) fly ARGS="--record $(OUT) $(ARGS)"

# Replay a run headless and log, per tick, the gate's verified path, failed rollout and end set, to draw over
# `make record` footage of the same run: RUN=showcase or ep<N> (as --episode N), results in OUT.
.PHONY: proofdump
proofdump:
	$(CITY) $(CARGO_HEADLESS) proofdump -- $(OUT) $(RUN) $(ARGS)

# Fly while sampling the process (macOS `sample`) and logging tick times, for later analysis: results in OUT.
.PHONY: profile
profile:
	lake build $(LAKE_OPTS) libcityjsb
	cd flight && cargo build --release --features jsb --bin cityflight
	Tools/profile-fly.sh $(OUT) $(FILTER) $(ARGS)
.PHONY: profile-lean
profile-lean:
	$(MAKE) profile FILTER=exact-rollout-lean OUT=/tmp/profile-lean

# Headless crash test: N hostile episodes plus the kamikaze scenarios, results in OUT.
.PHONY: crashes
crashes:
	$(CITY) $(CARGO_HEADLESS) crashes -- $(OUT) $(N) --safety-filter $(FILTER) $(ARGS)
.PHONY: crashes-lean
crashes-lean:
	$(MAKE) crashes FILTER=exact-rollout-lean
# Gap-guided adversary: N verified starts, results in OUT.
.PHONY: adversary
adversary:
	$(CITY) $(CARGO_HEADLESS) adversary -- $(OUT) $(FILTER) $(N) $(ARGS)
# Point-mass acceptance harness (Luis's original filters).
.PHONY: harness
harness:
	cd flight && cargo run --release --no-default-features --bin harness -- $(N) $(ARGS)
# Boundary-regime slices (docs/boundary-regimes): regenerate every slice, then print the index table.
.PHONY: regimes
regimes:
	$(CITY) $(CARGO_HEADLESS) regimes -- run $(ARGS) && $(CARGO_HEADLESS) regimes -- index

# Plant and Lean-gate spot checks: the JsbExact plant, state import, the Lean gate's street escape, the 4 spec starts.
# Run, not proof: the TermSoundR skeleton's Geo and Conf halves hold at the 4 spec starts' settled states.
.PHONY: termcheck
termcheck:
	lake build $(LAKE_OPTS) termskelcheck
	.lake/build/bin/termskelcheck

.PHONY: plantcheck
plantcheck:
	lake build $(LAKE_OPTS) cityplanttest cityimporttest citygatespot specbridgeinit
	.lake/build/bin/cityplanttest
	.lake/build/bin/cityimporttest
	.lake/build/bin/citygatespot
	.lake/build/bin/specbridgeinit

# Rust/Lean faithfulness of the escape law and end test: per-frame hashes and end-test verdicts from N starts must be
# identical, and the terminal law must reproduce docs/escape-law-terminal.md's reference hashes.
GF = /tmp/gatefaith
.PHONY: gatefaith
gatefaith:
	lake build $(LAKE_OPTS) libcityjsb gatefaith
	cd flight && cargo build --release --no-default-features --features jsb --bin gatefaith
	mkdir -p $(GF)
	flight/target/release/gatefaith starts $(GF)/starts.txt $(N)
	flight/target/release/gatefaith laws $(GF)/starts.txt $(GF)/rust.txt --threads 3
	.lake/build/bin/gatefaith laws $(GF)/starts.txt $(GF)/lean.txt
	cmp $(GF)/rust.txt $(GF)/lean.txt && echo "laws and end-test verdicts: identical"
	flight/target/release/gatefaith reftraj > $(GF)/ref-rust.txt
	.lake/build/bin/gatefaith reftraj > $(GF)/ref-lean.txt
	cmp $(GF)/ref-rust.txt $(GF)/ref-lean.txt && grep -q 2947c707944678e9 $(GF)/ref-lean.txt && grep -q dd0d6deef038f51a $(GF)/ref-lean.txt \
	  && echo "reference trajectories: both match the spec"

# End-test falsifiers: verified escapes flown on past their verdict (Rust: `termhunt N`, `trace I SEED ESC`, `trim`,
# `high`; Lean: `hunt SEED N`, `trace SEED I`, `witnesses FILE`, `pass SEED N`, `starts`).
.PHONY: termhunt
termhunt:
	$(CITY) $(CARGO_HEADLESS) termhunt -- $(ARGS)
.PHONY: termhunt-lean
termhunt-lean:
	lake build $(LAKE_OPTS) termhunt
	.lake/build/bin/termhunt $(ARGS)

# The city as plain files for other simulators (docs/xplane-integration.md), checked bit for bit.
.PHONY: export
export:
	cargo run --release --manifest-path Tools/city-export/Cargo.toml -- map city-map
	cargo run --release --manifest-path Tools/city-export/Cargo.toml -- check city-map

# The informal TermSound proof (docs/termsound-proof.tex) as PDF; needs tectonic.
.PHONY: pdf
pdf:
	cd docs && tectonic termsound-proof.tex

# Sufficiency of the plant-abstraction families of issue #58 (docs/termsound/abstractions.tex) as PDF; needs tectonic.
.PHONY: abstractions
abstractions:
	cd docs/termsound && tectonic abstractions.tex

# SLOW (tens of minutes, several GB of Mathlib per Mathlib-based project): build every archived experiment
# (experiments/README.md) from its own folder and print the axioms of the theorems each README names.
.PHONY: experiments
experiments:
	for d in continuous-pilot ci-proof; do \
	  (cd experiments/$$d && lake exe cache get && nice -n 10 lake build && lake env lean Audit.lean) || exit 1; \
	done
	for d in envelope-3d safety-filter; do \
	  (cd experiments/$$d && nice -n 10 lake build && lake env lean Audit.lean) || exit 1; \
	done

.PHONY: help
help:
	@echo "Fly:      make fly | fly-lean | fly-off | showcase | profile | profile-lean   (FILTER=..., ARGS=\"...\")"
	@echo "Record:   make record OUT=dir ARGS=\"--frames N --record-every K --record-scale K ...\"   (PNG frames + frames.csv)"
	@echo "          make proofdump OUT=dir RUN=showcase|ep<N> ARGS=\"--secs S --settle-secs S\"   (the gate's verified paths and end sets per tick)"
	@echo "Test:     make crashes | crashes-lean | adversary | harness | regimes | plantcheck | termcheck | test   (N=..., OUT=...)"
	@echo "Gate:     make gatefaith | termhunt | termhunt-lean   (N=..., ARGS=\"...\")"
	@echo "Proofs:   make verify | proofs | safe-region"
	@echo "Libs:     make gate | gate-example | gate-check | filter-lib | filter-test | export"
	@echo "Docs:     make pdf | abstractions"
	@echo "Archive:  make experiments   (SLOW: builds and audits every project under experiments/)"
	@echo "Lean app: make install | build | run | clean"

.PHONY: clean
clean:
	lake clean

# Numerical certificates of docs/termsound-proof.tex (straight-climb end set): builds `tsmap`, makes a Python venv
# with numpy, scipy and cvxpy under .lake/, recomputes the reference climb and prints every certificate (about 45 min).
TSVENV ?= .lake/tsvenv
.PHONY: certify
certify:
	lake build tsmap
	@test -x $(TSVENV)/bin/python || (python3 -m venv $(TSVENV) && $(TSVENV)/bin/pip install -q numpy scipy cvxpy)
	cd Tools/termsound && for s in ref cert nstep probe regime akink leveloff terminal reftraj level_param level_cert2 handover abstract abstract1s membership membership_verify; do nice -n 10 ../../$(TSVENV)/bin/python $$s.py || exit 1; done
