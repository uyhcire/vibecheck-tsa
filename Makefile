# `make install && make run` must work from a fresh clone (see rules.md).
SHELL := /bin/bash
ELAN_HOME ?= $(HOME)/.elan
export PATH := $(ELAN_HOME)/bin:/opt/homebrew/bin:/usr/local/bin:$(PATH)

SDL_PREFIX = $(shell brew --prefix sdl3 2>/dev/null || echo /opt/homebrew/opt/sdl3)
LAKE_OPTS = -K sdl=$(SDL_PREFIX)

.PHONY: install run build verify proofs test clean

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
	lake build $(LAKE_OPTS) Vibecheck Envelope
	lake env lean Tools/Audit.lean
	lake env lean Tools/EnvelopeAudit.lean

proofs:
	cd proofs && lake exe cache get && lake build && lake env lean Proofs/Audit.lean

test: build
	lake build $(LAKE_OPTS) simtest
	.lake/build/bin/simtest 1 160

clean:
	lake clean
