# `make install && make run` must work from a fresh clone (see rules.md).
SHELL := /bin/bash
ELAN_HOME ?= $(HOME)/.elan
export PATH := $(ELAN_HOME)/bin:/opt/homebrew/bin:/usr/local/bin:$(PATH)

SDL_PREFIX = $(shell brew --prefix sdl3 2>/dev/null || echo /opt/homebrew/opt/sdl3)
LAKE_OPTS = -K sdl=$(SDL_PREFIX)

.PHONY: install run build verify proofs test filter-lib filter-test gate gate-example gate-check clean

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

clean:
	lake clean
