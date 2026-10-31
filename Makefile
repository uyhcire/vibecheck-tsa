# `make install && make run` must work from a fresh clone (see rules.md).
SHELL := /bin/bash
ELAN_HOME ?= $(HOME)/.elan
export PATH := $(ELAN_HOME)/bin:$(PATH)

.PHONY: install run build clean

# Install elan (the Lean toolchain manager) if missing, then build.
# elan reads lean-toolchain and fetches the pinned Lean version on first use.
install:
	@if ! command -v elan >/dev/null 2>&1; then \
	  echo "Installing elan..."; \
	  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
	    | sh -s -- -y --default-toolchain none; \
	fi
	lake build

build:
	lake build

run:
	lake exe vibecheck

clean:
	lake clean
