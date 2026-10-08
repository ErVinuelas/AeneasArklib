#!/usr/bin/env bash
# Commit gate for Claude Code -- a PreToolUse hook on the Bash tool.
#
# Every Bash command the agent runs passes through here. Anything that is not a
# `git commit` is let through untouched. A `git commit` is allowed only if the
# checks that guard this repository's invariants are green *for what the commit
# touches*:
#
#   hachi/lean/, hachi/src/, lakefile, lake-manifest, lean-toolchain
#       -> `make build`  (the Lean proofs; fails on any error or `sorry`)
#   hachi/src/, hachi/tests/, hachi/benches/, Cargo.toml, Cargo.lock
#       -> `make test`   (the Rust semantics tests)
#
# A commit that touches none of these (NOTES.md, a plan, a ledger row) is not
# gated. `make build` is incremental: when the proofs are already built it is a
# ~2 s no-op; when a Lean file changed it rebuilds that module and its
# dependents. It is never run while a benchmark is in flight, because a build
# alongside `make run-bench` corrupts the measurement (INSTRUCTIONS.md).
#
# Fails closed: a timeout, a missing tool, or a refused build all deny the
# commit with a reason. The full make output is kept in .make/commit-gate-*.log.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MAKE_DIR="$ROOT/.make"
LOG="$MAKE_DIR/commit-gate.log"
BUILD_BUDGET=3300   # seconds; the hook itself is capped at 3600 in settings.json
mkdir -p "$MAKE_DIR"

input="$(cat)"
cmd="$(jq -r '.tool_input.command // empty' <<<"$input" 2>/dev/null)"

# Only `git commit` (also `git -C dir commit`, `... && git commit ...`).
if ! grep -qE '(^|[^[:alnum:]_./-])git[[:space:]]+([^[:space:]]+[[:space:]]+)*commit([[:space:]]|$)' <<<"$cmd"; then
  exit 0
fi

log() { printf '%s  %s\n' "$(date '+%Y-%m-%dT%H:%M:%S%z')" "$(tr '\n' ' ' <<<"$*")" >>"$LOG"; }

deny() {
  log "DENY  $1  cmd=$(tr '\n' ' ' <<<"$cmd" | cut -c1-160)"
  jq -n --arg r "commit gate: $1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $r
    }
  }'
  exit 0
}

pass() {
  log "PASS  $1  cmd=$(tr '\n' ' ' <<<"$cmd" | cut -c1-160)"
  jq -n --arg m "commit gate: $1" '{ systemMessage: $m }'
  exit 0
}

# --- What is this commit going to contain? -----------------------------------
# Staged changes always. Working-tree changes too when the command stages them
# itself (-a, -am, --all, --include, --only, a pathspec after `commit`). For
# --amend, what HEAD already carries. Over-including only costs a build.
files="$(git -C "$ROOT" diff --cached --name-only 2>/dev/null)"
include_worktree=0
grep -qE '(^|[[:space:]])(-[a-zA-Z]*a[a-zA-Z]*|--all|--include|--only)([[:space:]=]|$)' <<<"$cmd" && include_worktree=1
if [ "$include_worktree" -eq 0 ]; then
  after="${cmd#*commit}"
  for tok in $after; do
    tok="${tok%\"}"; tok="${tok#\"}"; tok="${tok%\'}"; tok="${tok#\'}"
    case "$tok" in -*|'') continue ;; esac
    if [ -e "$ROOT/$tok" ] || [ -e "$tok" ]; then include_worktree=1; break; fi
  done
fi
if [ "$include_worktree" -eq 1 ]; then
  files="$files"$'\n'"$(git -C "$ROOT" diff --name-only 2>/dev/null)"
fi
if grep -qE '(^|[[:space:]])--amend([[:space:]]|$)' <<<"$cmd"; then
  files="$files"$'\n'"$(git -C "$ROOT" diff --name-only HEAD~1 HEAD 2>/dev/null)"
fi
files="$(sort -u <<<"$files" | sed '/^$/d')"

LEAN_RE='^hachi/(lean/|src/|lakefile\.lean$|lake-manifest\.json$|lean-toolchain$)'
RUST_RE='^hachi/(src/|tests/|benches/|Cargo\.toml$|Cargo\.lock$)'
need_build=0; need_test=0
grep -qE "$LEAN_RE" <<<"$files" && need_build=1
grep -qE "$RUST_RE" <<<"$files" && need_test=1

if [ "$need_build" -eq 0 ] && [ "$need_test" -eq 0 ]; then
  pass "no proof-relevant paths in this commit; not gated"
fi

# --- Never build alongside a benchmark ----------------------------------------
# (own shell and parent excluded: their argv may quote this very pattern)
if pgrep -f '(^|/)cargo bench|python3? [^ ]*benches/harness\.py|(^|/)make( -[^ ]+)* run-bench' \
     | grep -vxE "$$|$PPID" | grep -q .; then
  deny "a benchmark is running (make run-bench / cargo bench); a build alongside it corrupts the measurement. Retry when it has finished."
fi

command -v make >/dev/null || deny "make not found on PATH"
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"

run_target() {  # target, budget
  local target="$1" budget="$2" out="$MAKE_DIR/commit-gate-$1.log" t0 rc
  t0=$(date +%s)
  timeout "$budget" make -C "$ROOT" "$target" >"$out" 2>&1
  rc=$?
  echo "$(( $(date +%s) - t0 ))" >"$MAKE_DIR/commit-gate-$1.secs"
  if [ "$rc" -eq 124 ]; then
    deny "make $target exceeded ${budget}s (cold Mathlib cache?). Run \`make $target\` by hand, then retry. Log: $out"
  elif [ "$rc" -ne 0 ]; then
    deny "make $target FAILED (exit $rc). Fix it before committing. Log: $out. Tail:
$(grep -nE 'error|sorry|FAILED|panicked' "$out" | tail -12)
$(tail -4 "$out")"
  fi
}

summary=""
if [ "$need_build" -eq 1 ]; then
  run_target build "$BUILD_BUDGET"
  summary="make build green ($(cat "$MAKE_DIR/commit-gate-build.secs")s, no errors, no sorry)"
fi
if [ "$need_test" -eq 1 ]; then
  run_target test "$BUILD_BUDGET"
  summary="${summary:+$summary; }make test green ($(cat "$MAKE_DIR/commit-gate-test.secs")s)"
fi
pass "$summary"
