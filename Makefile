# Setup, proof checking and re-extraction for AeneasArklib.
#
#   make setup     install everything the other targets need
#   make build     check the Lean proofs
#   make extract   regenerate hachi/lean/Generated.lean from hachi/src/
#   make run-bench time every operation
#
# `make setup` is idempotent and safe to re-run: it records what it did in
# ./.make/ and skips work already done. What it installs goes either inside this
# directory (./toolchain) or into the standard per-user toolchain roots that
# elan and rustup manage themselves (~/.elan, ~/.rustup, ~/.cargo). Nothing is
# installed system-wide.
#
# README.md says what the repository is; this file is how you drive it.

SHELL := /bin/bash

# --- Pins --------------------------------------------------------------------

# The Aeneas release the extraction binaries come from, and the upstream commit
# it was built at. That commit is the invariant worth protecting: the Lean
# backend required by hachi/lakefile.lean is this same commit, and
# hachi/lean/Generated.lean is only valid against the Aeneas version that
# produced it. The binaries self-report the commit, so `setup` and `extract`
# check it rather than assume it -- bumping one side without the other would
# otherwise silently invalidate the proofs.
#
# Unlike AeneasCompPoly, this repository tracks *upstream* aeneas and needs no
# fork: this nightly's Lean backend requires Lean/Mathlib v4.31.0, which is
# exactly ArkLib's pin. See NOTES.md § "Upstream aeneas, no fork".
AENEAS_TAG    := nightly-2026.07.26-3a8586f
AENEAS_COMMIT := 3a8586f

# Rust components charon needs on top of a bare toolchain. The *channel* is not
# pinned here: it is read from the `rust-toolchain` that ships beside charon,
# which is also where charon itself looks -- so overriding CHARON below moves
# the lookup with it.
RUST_COMPONENTS := rustc-dev llvm-tools-preview rust-src

# --- Layout ------------------------------------------------------------------

PKG       := $(CURDIR)/hachi
TOOLCHAIN := $(CURDIR)/toolchain
STAMPS    := $(CURDIR)/.make

# Overridable, for binaries kept somewhere else: `make extract CHARON=/path/to/charon`.
CHARON := $(TOOLCHAIN)/charon
AENEAS := $(TOOLCHAIN)/aeneas

# The extraction pipeline: charon writes the .llbc, aeneas turns it into a Lean
# module inside the library's srcDir. Aeneas names that module after the
# basename of the .llbc, so `generated.llbc` is what makes `import Generated`
# resolve -- renaming it renames the module the proofs import.
LLBC      := generated.llbc
GENERATED := $(PKG)/lean/Generated.lean

# charon resolves its rustc toolchain from a `rust-toolchain` beside its own
# executable, so this follows CHARON rather than assuming ./toolchain.
RUST_TOOLCHAIN_FILE := $(dir $(CHARON))rust-toolchain

# So that a freshly installed elan or rustup is usable within this same `make`
# run, without the user having to open a new shell first.
export PATH := $(HOME)/.elan/bin:$(HOME)/.cargo/bin:$(PATH)

OS    := $(shell uname -s | tr '[:upper:]' '[:lower:]' | sed 's/^darwin$$/macos/')
ARCH  := $(shell uname -m | sed -e 's/^arm64$$/aarch64/' -e 's/^amd64$$/x86_64/')
ASSET := aeneas-$(OS)-$(ARCH).tar.gz
URL   := https://github.com/AeneasVerif/aeneas/releases/download/$(AENEAS_TAG)/$(ASSET)

# Two halves of the setup, tracked separately so `build` does not drag in the
# extraction toolchain and vice versa. The tag is part of the toolchain stamp's
# name, so moving the pin above invalidates it on its own.
LEAN_STAMP := $(STAMPS)/lean-deps
TC_STAMP   := $(STAMPS)/toolchain-$(AENEAS_TAG)
BUILD_LOG  := $(STAMPS)/build.log

.DEFAULT_GOAL := help
.PHONY: help setup build test extract check-toolchain clean

# One synopsis, then targets, then variables -- the usual shape for a command's
# --help. No per-target variable subsections: a variable on the command line
# applies to the whole invocation whichever target ends up reading it, so which
# one that is belongs in its description, not in a heading.
#
# One line per entry, every list aligned on the same column, nothing past ~77
# characters. Anything that needs more than a line belongs in the comment above
# the target it describes, not here -- and a description must not promise what
# the target does not do.
help:
	@echo ''
	@echo '  Run `make setup` once after cloning; the other targets work from there.'
	@echo ''
	@echo '  Usage: make <target> [VAR=VALUE]...'
	@echo ''
	@echo '  Targets:'
	@echo '    setup          install elan, the Lean deps, charon/aeneas and rust'
	@echo '    build          check the Lean proofs -- fails on any error or `sorry`'
	@echo '    extract        regenerate hachi/lean/Generated.lean from hachi/src/'
	@echo '    test           run the Rust-side semantics tests'
	@echo '    run-bench      time every operation against its frozen first translation'
	@echo '    bench-check    check the frozen baseline against git, and bench coverage'
	@echo '    bench-stamp    re-derive the @genesis stamps after freezing a function'
	@echo '    bench-coverage report which mirrored items are benched, without failing'
	@echo '    ledger-check   validate logs/ledger.jsonl against the last commit'
	@echo '    clean          drop build output, keeping fetched dependencies'
	@echo ''
	@echo '  Variables:'
	@echo '    AENEAS=<path>  aeneas binary for `extract` (default ./toolchain/aeneas)'
	@echo '    BENCH=<regex>  bench only the cases whose id matches this regex'
	@echo '    CANDIDATE=1    also time the candidate slot, for the optimization loop'
	@echo '    CHARON=<path>  charon binary for `extract` (default ./toolchain/charon)'
	@echo '    JSON=<path>    also write the bench report as JSON, for an agent'
	@echo ''

# --- setup -------------------------------------------------------------------

setup: $(LEAN_STAMP) check-toolchain
	@echo '==> setup complete. `make build` checks the proofs, `make extract` regenerates the model.'

$(STAMPS):
	@mkdir -p $@

# Lean side: elan, then the dependency graph pinned in lake-manifest.json, then
# Mathlib's prebuilt oleans. Re-runs if either pin file moves -- notably after a
# `lake update`.
#
# The elan install is delegated to scripts/install-lean.sh rather than inlined,
# because it has a fallback worth explaining at length: elan's own host and Lean's
# release host are separate from GitHub, and a sandbox with an egress allowlist
# commonly permits GitHub and nothing else. The script tries the normal path first
# and unpacks the GitHub release assets if it is refused. It cannot do the same for
# the olean cache below -- there is no GitHub mirror of that -- which is why the
# failure there is a warning and not an error.
$(LEAN_STAMP): $(PKG)/lean-toolchain $(PKG)/lake-manifest.json | $(STAMPS)
	@echo '==> Lean toolchain and dependencies'
	@set -euo pipefail; \
	'$(CURDIR)/scripts/install-lean.sh' '$(PKG)/lean-toolchain'; \
	echo "    elan $$(elan --version | awk '{print $$2}'), toolchain $$(cat $(PKG)/lean-toolchain)"
	@set -euo pipefail; cd $(PKG); \
	if ! lake exe cache get; then \
	  echo 'warning: `lake exe cache get` failed. The build will still work, but it' >&2; \
	  echo '         will compile Mathlib (and ArkLib) from source, which takes hours.' >&2; \
	  echo '         Re-run `make setup` to retry the cache download.' >&2; \
	  echo '' >&2; \
	  echo '         If every object failed with a 403 or a refused CONNECT, this is' >&2; \
	  echo '         not a transient error: the cache lives on cache.lean-lang.org, and' >&2; \
	  echo '         an egress policy that allows only GitHub blocks all of it. There is' >&2; \
	  echo '         no mirror to fall back to (scripts/install-lean.sh handles the' >&2; \
	  echo '         toolchain that way, but cannot do it for oleans), so on such a host' >&2; \
	  echo '         the source build is the only route -- budget hours, and see' >&2; \
	  echo '         NOTES.md "What this environment could and could not check".' >&2; \
	fi
	@set -euo pipefail; \
	backend='$(PKG)/.lake/packages/aeneas'; \
	if [ ! -d "$$backend/.git" ]; then \
	  echo '    backend commit unchecked: no git history in .lake/packages/aeneas'; \
	elif git -C "$$backend" merge-base --is-ancestor '$(AENEAS_COMMIT)' HEAD 2>/dev/null; then \
	  echo "    backend is $(AENEAS_COMMIT) + $$(git -C "$$backend" rev-list --count '$(AENEAS_COMMIT)'..HEAD) commit(s)"; \
	else \
	  echo 'error: the pinned Aeneas backend is not a descendant of $(AENEAS_COMMIT), the' >&2; \
	  echo '       commit the extraction binaries are built from. lean/Generated.lean is' >&2; \
	  echo '       only valid against the Aeneas version that produced it, so move the' >&2; \
	  echo '       Makefile pins and the aeneas rev in lake-manifest.json together.' >&2; \
	  exit 1; \
	fi
	@touch $@

# Extraction side: the charon/aeneas release binaries, plus the rustc nightly
# charon needs. Skips the download when binaries at the right commit are already
# in place, so an existing ./toolchain is adopted rather than re-fetched.
$(TC_STAMP): | $(STAMPS)
	@echo '==> extraction binaries ($(AENEAS_TAG), $(OS)-$(ARCH))'
	@set -euo pipefail; \
	if [ -x '$(CHARON)' ] && [ -x '$(AENEAS)' ] && '$(AENEAS)' -version | grep -q -- '$(AENEAS_COMMIT)'; then \
	  echo "    already present: $$('$(AENEAS)' -version)"; \
	else \
	  mkdir -p '$(TOOLCHAIN)'; \
	  echo '    downloading $(ASSET) (~124 MB)'; \
	  curl -fL --retry 3 --progress-bar -o '$(TOOLCHAIN)/$(ASSET).part' '$(URL)'; \
	  tar xzf '$(TOOLCHAIN)/$(ASSET).part' -C '$(TOOLCHAIN)'; \
	  rm -f '$(TOOLCHAIN)/$(ASSET).part'; \
	fi
	@set -euo pipefail; \
	if ! command -v rustup >/dev/null; then \
	  echo '    installing rustup'; \
	  curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal; \
	fi; \
	channel=$$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' '$(RUST_TOOLCHAIN_FILE)' | head -1); \
	if [ -z "$$channel" ]; then \
	  echo 'error: no channel found in $(RUST_TOOLCHAIN_FILE)' >&2; exit 1; \
	fi; \
	echo "    rust $$channel + $(RUST_COMPONENTS) (for charon)"; \
	rustup toolchain install --profile minimal --no-self-update "$$channel" >/dev/null; \
	rustup component add --toolchain "$$channel" $(RUST_COMPONENTS) >/dev/null; \
	'$(CHARON)' toolchain-path >/dev/null
	@touch $@

# Enforces what the comment on AENEAS_TAG describes. Cheap enough to run before
# every extraction, which is exactly when a mismatch would do damage.
check-toolchain: $(TC_STAMP)
	@set -euo pipefail; \
	for bin in '$(CHARON)' '$(AENEAS)'; do \
	  if [ ! -x "$$bin" ]; then \
	    echo "error: $$bin missing. Run \`make setup\`." >&2; exit 1; \
	  fi; \
	done; \
	got=$$('$(AENEAS)' -version | awk '{print $$NF}'); \
	case "$$got" in \
	  *$(AENEAS_COMMIT)) ;; \
	  *) echo "error: aeneas binary is $$got, expected commit $(AENEAS_COMMIT)." >&2; \
	     echo "       Generated.lean is only valid against the Aeneas version that" >&2; \
	     echo "       produced it. Either restore the pinned binaries (rm -rf toolchain" >&2; \
	     echo "       && make setup) or move AENEAS_TAG, the aeneas rev in" >&2; \
	     echo "       hachi/lakefile.lean and Generated.lean together." >&2; \
	     exit 1 ;; \
	esac

# --- build, test, extract ----------------------------------------------------

# `lake build` alone is not enough to conclude the proofs go through: a `sorry`
# is a warning, not an error, so lake would still exit 0 on one. Hence the scan
# of the log, for both halves of the evidence -- Lean's per-declaration warning,
# and `sorryAx` turning up in an axiom dependency.
#
# Both halves are deliberately scoped to this development. Diagnostics from this
# library's own modules carry its srcDir, `lean/`, and a dependency's do not,
# which matters because Aeneas.Std ships a handful of `sorry`s of its own in
# definitions this development never reaches, and ArkLib carries `sorry`s in
# formalizations this development never imports. `sorryAx` needs no such
# qualifier: Check.lean's `#print axioms` is the only thing in the whole build
# that prints axioms, so any occurrence is about a headline spec here -- and that
# is also the half that rules out reaching those upstream `sorry`s indirectly.
#
# The quote character around `sorry` in Lean's warning has changed between
# versions, so the pattern does not commit to which one it is.
SORRY_PATTERN := lean/[A-Za-z0-9_]+\.lean:[0-9]+:[0-9]+: declaration uses .sorry.|sorryAx

build: $(LEAN_STAMP) | $(STAMPS)
	@echo '==> lake build'
	@set -euo pipefail; cd $(PKG) && lake build 2>&1 | tee '$(BUILD_LOG)'
	@set -euo pipefail; \
	if grep -qE '$(SORRY_PATTERN)' '$(BUILD_LOG)'; then \
	  echo 'error: the build went through, but it contains a `sorry`:' >&2; \
	  grep -nE '$(SORRY_PATTERN)' '$(BUILD_LOG)' >&2; \
	  exit 1; \
	fi
	@echo '==> proofs check out: no errors, no `sorry`'

test:
	@set -euo pipefail; \
	if ! command -v cargo >/dev/null; then \
	  echo 'error: cargo not found. Run `make setup`.' >&2; exit 1; \
	fi; \
	cd $(PKG) && cargo test

# `--preset=aeneas` is mandatory: aeneas rejects an llbc emitted without it.
# `-- --lib` keeps cargo off the test targets, which are not part of the model.
# The previous model is kept aside only so that the run can report whether the
# model actually moved.
#
# `--include 'cpoly::_'` is what makes the field layer a *dependency* rather than
# a copy. Charon's default whitelist is the local crate, so without it every
# `cpoly` item arrives as an `axiom` -- an uninterpreted `Fp` with an
# uninterpreted `+`, which is provably nothing and would poison the axiom audit
# in `lean/Check.lean`. With it, charon translates them transparently: `Fp`
# becomes `@[reducible] def cpoly.field.Fp := Std.U64` and its `add` the real
# `(self + rhs) % P`. Measured, not assumed -- NOTES.md § "The cpoly dependency"
# records both extractions.
#
# Note this is NOT `--extract-opaque-bodies`, which was the obvious first guess
# and is the wrong tool: that flag is global, so it also un-opaques `alloc::vec`
# and the rest of std, and aeneas then dies on mixed recursive declaration
# groups. The whitelist is scoped; the flag is not.
CHARON_INCLUDE := 'cpoly::_'

extract: check-toolchain | $(STAMPS)
	@echo '==> charon'
	@set -euo pipefail; cd $(PKG) && '$(CHARON)' cargo --preset=aeneas \
	  --include $(CHARON_INCLUDE) --dest-file '$(LLBC)' -- --lib
	@set -euo pipefail; \
	prev='$(STAMPS)/Generated.lean.prev'; \
	if [ -f '$(GENERATED)' ]; then cp '$(GENERATED)' "$$prev"; else rm -f "$$prev"; fi; \
	echo '==> aeneas'; \
	cd $(PKG) && '$(AENEAS)' -backend lean -dest lean '$(LLBC)'; \
	if [ -f "$$prev" ] && cmp -s "$$prev" '$(GENERATED)'; then \
	  echo '==> lean/Generated.lean unchanged'; \
	else \
	  echo '==> regenerated lean/Generated.lean'; \
	fi; \
	rm -f "$$prev"
	@echo '==> now re-check the proofs: make build'

# --- benchmarks ---------------------------------------------------------------

# Criterion wall-clock time for every translated operation. `hachi/benches/genesis`
# holds the frozen first translation of each one and is measured in the same
# session, so a "vs genesis" reading is a comparison made *now*, on this machine,
# rather than against a remembered number. Nothing is ever compared across runs:
# a cross-run comparison inherits the difference in machine conditions between
# two moments, and on an ordinary desktop that dwarfs anything the code does.
#
# The toolchain is pinned for the same reason the profile is (hachi/Cargo.toml
# § profile.bench): a number is only comparable to another number produced by the
# same compiler. This is charon's channel, which `make setup` installs anyway, so
# benchmarking adds no toolchain the repository did not already need. Moving it
# makes any number kept from before the move incomparable with any number after,
# so treat a change to it as a re-baseline.
#
# `make setup` writes the channel charon ships with to ./.make/, and the target
# below checks this pin against it: charon and the benchmarks must agree, or the
# pin is stale.
BENCH_TOOLCHAIN := nightly-2026-06-01
HARNESS         := $(PKG)/benches/harness.py

.PHONY: run-bench bench-check bench-stamp bench-coverage bench-toolchain ledger-check

# Statistics cannot rescue a corrupted baseline, so the integrity checks run
# before any measurement and are a hard gate.
#
# Three questions, in the order a wrong answer does damage:
#
#   check-genesis    is every frozen item byte-for-byte what hachi/src held at the
#                    commit its `@genesis` stamp names -- attributes included? An
#                    edited baseline makes every "vs genesis" number ever printed
#                    wrong, retroactively and silently.
#   check-candidate  is the A/B slot a null candidate (byte-copies of hachi/src),
#                    with no symlink, no extra file, and lib.rs/Cargo.toml pinned
#                    to git? A slot that diverged at rest means the next
#                    CANDIDATE=1 run benches a stale diff as the challenger.
#   coverage         is every item claiming to mirror an ArkLib definition either
#                    benched or excluded by name with a reason? Silence is not an
#                    exclusion: an operation nobody measures is one the loop
#                    cannot notice a regression in.
#
# Coverage is `--strict` here and merely reported by `run-bench`: an unmeasured
# operation makes the picture incomplete, while an edited genesis makes the
# picture wrong.
bench-check:
	@set -euo pipefail; \
	python3 '$(HARNESS)' check-genesis; \
	python3 '$(HARNESS)' check-candidate; \
	python3 '$(HARNESS)' coverage --strict

# Re-derive the `// @genesis <sha> <date>` annotations from git history, then
# re-check them. Run after copying a newly translated function into
# hachi/benches/genesis/src/ -- and note the ordering the stamps force: the text
# must already be in a commit, because the stamp records that commit's sha. So
# the sequence is commit the translation and the frozen copy together, run this,
# then commit the stamp lines *separately*. Never `--amend` the first commit
# instead: the stamp stores its sha, and an amend orphans it.
bench-stamp:
	@python3 '$(HARNESS)' stamp-genesis
	@python3 '$(HARNESS)' check-genesis

# The coverage report on its own, non-strict -- for reading, not for gating.
bench-coverage:
	@python3 '$(HARNESS)' coverage -v

# The ledger's gate: row schema, append-only against the last committed state.
# `logs/ledger.jsonl` is where candidate verdicts and verification campaigns are
# recorded; run this before writing any commit plan that touches it.
ledger-check:
	@python3 .claude/skills/skill-lab/references/ledger_check.py --against HEAD

bench-toolchain:
	@set -euo pipefail; \
	if ! command -v python3 >/dev/null; then \
	  echo 'error: python3 not found; benches/harness.py needs it (stdlib only).' >&2; \
	  exit 1; \
	fi; \
	if ! command -v rustup >/dev/null; then \
	  echo 'error: rustup not found. Run `make setup`.' >&2; exit 1; \
	fi; \
	if [ -f '$(RUST_TOOLCHAIN_FILE)' ]; then \
	  channel=$$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' '$(RUST_TOOLCHAIN_FILE)' | head -1); \
	  if [ -n "$$channel" ] && [ "$$channel" != '$(BENCH_TOOLCHAIN)' ]; then \
	    echo 'error: BENCH_TOOLCHAIN is $(BENCH_TOOLCHAIN) but charon ships' >&2; \
	    echo "       $$channel. Benchmarks must be built with the same compiler as" >&2; \
	    echo '       the extraction toolchain, so move the pin -- and treat that as a' >&2; \
	    echo '       re-baseline, since no earlier number stays comparable.' >&2; \
	    exit 1; \
	  fi; \
	fi; \
	if ! rustup run '$(BENCH_TOOLCHAIN)' rustc --version >/dev/null 2>&1; then \
	  echo '==> installing rust $(BENCH_TOOLCHAIN) (pinned for benchmarks)'; \
	  rustup toolchain install --profile minimal --no-self-update '$(BENCH_TOOLCHAIN)' >/dev/null; \
	fi

#   make run-bench                  every bench, one full-rigour pass
#   make run-bench BENCH=gadget     only cases whose id matches this regex
#   make run-bench JSON=out.json    also write the report as JSON, for an agent
#   make run-bench CANDIDATE=1      also time the candidate slot (benches/candidate)
#
# CANDIDATE=1 (exactly `1`: any other value, including 0, disables) is the
# optimization loop's mode: the slot holds a candidate's code (in the loop's
# worktree; at rest it is a byte-copy of hachi/src) so that a candidate and the
# champion are measured in the same criterion session, and the report gains
# `candidate` and `cand vs now` columns. The accept decision is made on the
# *recentered* `cand vs now`: each bench binary's own `_control` case measures
# the slot's signed identical-code lean in that same run, and it is divided out
# before any verdict. Pass BENCH='<op>|_control' alongside it -- a candidate case
# in a binary whose control did not run gets no verdict at all and the report
# exits 2, so the filter advice is enforced rather than hoped for.
#
# There is one mode and one pass. Reduced sampling is deliberately not offered:
# on byte-identical code it returns non-noise verdicts while printing exactly
# what a full run prints, and a mode whose output cannot be told apart from a
# trustworthy one is not a shortcut.
#
# Benchmarking needs the machine to itself. A build running alongside it -- from
# this repo or any other project -- corrupts the measurement, so check the machine
# before a run (`ps -eo command | grep -c "[b]in/lean"` plus the load average)
# and wait for someone else's build rather than racing it.
#
# The start time is stamped before cargo runs so the report contains only what
# this invocation measured. Without it a `BENCH=` filter would silently republish
# stale rows for everything it skipped, which is the most plausible way this
# harness could come to lie.
run-bench: bench-toolchain
	@set -euo pipefail; \
	python3 '$(HARNESS)' check-genesis
	@set -euo pipefail; \
	python3 '$(HARNESS)' check-candidate
	@set -euo pipefail; \
	python3 '$(HARNESS)' coverage || true
	@set -euo pipefail; \
	started=$$(date +%s); \
	( cd $(PKG) && rustup run '$(BENCH_TOOLCHAIN)' cargo bench --benches \
	    $(if $(filter 1,$(CANDIDATE)),--features candidate,) -- \
	    $(if $(BENCH),'$(BENCH)',) ); \
	python3 '$(HARNESS)' report \
	  --toolchain '$(BENCH_TOOLCHAIN)' \
	  --since "$$started" \
	  $(if $(JSON),--json '$(JSON)',)

# --- clean -------------------------------------------------------------------

# Build output only. Fetched dependencies (hachi/.lake/packages, ./toolchain,
# the elan and rustup toolchains) are deliberately left alone: they are
# expensive to re-obtain and `make setup` is what manages them.
clean:
	@echo '==> clean'
	@-cd $(PKG) && lake clean
	@-cd $(PKG) && cargo clean
	@rm -f '$(BUILD_LOG)' '$(PKG)/$(LLBC)'
