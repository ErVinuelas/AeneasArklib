#!/usr/bin/env bash
#
# Install elan and one pinned Lean toolchain, from GitHub releases if the usual
# hosts are unreachable.
#
# Usage:  scripts/install-lean.sh <toolchain-file>
#         scripts/install-lean.sh hachi/lean-toolchain
#
# Idempotent: if elan already resolves the toolchain the file names, it does
# nothing.
#
# WHY THIS EXISTS
#
# `make setup`'s normal path is the two-line one everybody uses:
#
#     curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh
#
# and then elan fetches Lean itself from `release.lean-lang.org`. That is the
# right first choice and this script tries it first. But both of those hosts are
# *separate* from GitHub, and a sandbox with an egress allowlist commonly permits
# github.com and nothing else -- which is exactly the environment this repository
# was first built in (NOTES.md § "What this environment could and could not
# check"). There, the normal path fails with a bare
#
#     curl: (22) The requested URL returned error: 403
#
# and the whole Lean side of the repository is unavailable for a reason that has
# nothing to do with Lean.
#
# The fallback below needs no host the normal path does not already need for the
# *rest* of `make setup`: elan and the Lean toolchains are published as release
# assets on github.com, which `make setup` must reach anyway for the charon and
# aeneas binaries. So if the aeneas half of setup can run at all, this can too.
#
# WHAT IT DOES NOT FIX
#
# The Mathlib **olean cache**. `lake exe cache get` downloads from
# `cache.lean-lang.org`, and there is no GitHub mirror of it, so on a host that
# cannot reach that domain Mathlib and ArkLib compile from source -- hours on a
# small machine. `make setup` already warns and continues in that case, which is
# the right behaviour: the build works, it is just slow. Nothing here changes it.
#
# HOW ELAN IS PERSUADED
#
# No elan flag or environment variable redirects its toolchain downloads. What it
# does do is *look before it fetches*: a directory in `$ELAN_HOME/toolchains`
# whose name is the toolchain's mangled form is adopted as an installed
# toolchain. The mangling replaces `/` with `--` and `:` with `---`, so
# `leanprover/lean4:v4.31.0` becomes `leanprover--lean4---v4.31.0`. Unpacking the
# release tarball there is therefore not a trick played on elan; it is the same
# layout elan itself would have produced.

set -euo pipefail

TOOLCHAIN_FILE="${1:?usage: install-lean.sh <toolchain-file>}"
ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
ELAN_VERSION="${ELAN_VERSION:-v4.2.3}"

TOOLCHAIN="$(tr -d '[:space:]' < "$TOOLCHAIN_FILE")"
if [ -z "$TOOLCHAIN" ]; then
  echo "error: $TOOLCHAIN_FILE is empty" >&2
  exit 1
fi

# `leanprover/lean4:v4.31.0` -> `leanprover--lean4---v4.31.0`, elan's own naming.
MANGLED="${TOOLCHAIN//\//--}"
MANGLED="${MANGLED//:/---}"
# `leanprover/lean4:v4.31.0` -> `v4.31.0`, the release tag.
TAG="${TOOLCHAIN##*:}"

case "$(uname -s)" in
  Darwin) LEAN_OS=darwin ;;
  Linux)  LEAN_OS=linux ;;
  *)      echo "error: unsupported OS $(uname -s)" >&2; exit 1 ;;
esac
case "$(uname -m)" in
  arm64|aarch64) LEAN_ARCH=aarch64; ELAN_ARCH=aarch64 ;;
  x86_64|amd64)  LEAN_ARCH=x86_64;  ELAN_ARCH=x86_64 ;;
  *)             echo "error: unsupported architecture $(uname -m)" >&2; exit 1 ;;
esac
if [ "$LEAN_OS" = linux ] && [ "$LEAN_ARCH" = x86_64 ]; then
  LEAN_ASSET="lean-${TAG#v}-linux.tar.zst"
else
  LEAN_ASSET="lean-${TAG#v}-${LEAN_OS}_${LEAN_ARCH}.tar.zst"
fi
if [ "$LEAN_OS" = darwin ]; then
  ELAN_ASSET="elan-${ELAN_ARCH}-apple-darwin.tar.gz"
else
  ELAN_ASSET="elan-${ELAN_ARCH}-unknown-linux-gnu.tar.gz"
fi

export PATH="$ELAN_HOME/bin:$PATH"

# --- Already done? ----------------------------------------------------------

if command -v elan >/dev/null 2>&1 &&
   elan toolchain list 2>/dev/null | grep -qx "$TOOLCHAIN"; then
  echo "    $TOOLCHAIN already installed"
  exit 0
fi

# --- elan itself ------------------------------------------------------------

if ! command -v elan >/dev/null 2>&1; then
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  echo '    installing elan (Lean toolchain manager)'
  if curl -fsSL --retry 2 --max-time 120 https://elan.lean-lang.org/elan-init.sh \
       -o "$tmp/elan-init.sh" 2>/dev/null; then
    sh "$tmp/elan-init.sh" -y --default-toolchain none >/dev/null
  else
    echo "    elan.lean-lang.org unreachable; falling back to the GitHub release"
    curl -fsSL --retry 3 -o "$tmp/elan.tar.gz" \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/${ELAN_ASSET}"
    tar xzf "$tmp/elan.tar.gz" -C "$tmp"
    "$tmp/elan-init" -y --default-toolchain none --no-modify-path >/dev/null
  fi
fi

# --- the toolchain ----------------------------------------------------------

# elan's own fetch first: it is the supported path, and it puts the toolchain
# exactly where the fallback would.
if elan toolchain install "$TOOLCHAIN" >/dev/null 2>&1; then
  echo "    $TOOLCHAIN installed by elan"
  exit 0
fi

echo "    release.lean-lang.org unreachable; falling back to the GitHub release"

dest="$ELAN_HOME/toolchains/$MANGLED"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
curl -fL --retry 3 --progress-bar -o "$tmp/lean.tar.zst" \
  "https://github.com/leanprover/lean4/releases/download/${TAG}/${LEAN_ASSET}"

mkdir -p "$dest"

# The tarball is zstd-compressed, and zstd is not everywhere. Three ways to open
# it, each *attempted* rather than detected -- which is the lesson of the second
# one: `tar --help` advertises `--zstd` on any modern tar, but tar implements it
# by exec'ing the `zstd` binary, so on a machine without that binary the flag is
# present and the extraction still fails with
#
#     tar (child): zstd: Cannot exec: No such file or directory
#
# Checking for the flag is therefore not a check for the capability. Each branch
# below runs and its exit status decides.
unpacked=0

if [ "$unpacked" -eq 0 ] && command -v zstd >/dev/null 2>&1; then
  if zstd -dc "$tmp/lean.tar.zst" | tar x -C "$dest" --strip-components=1; then
    unpacked=1
  fi
fi

if [ "$unpacked" -eq 0 ]; then
  if tar x --zstd -f "$tmp/lean.tar.zst" -C "$dest" --strip-components=1 2>/dev/null; then
    unpacked=1
  fi
fi

if [ "$unpacked" -eq 0 ] && command -v python3 >/dev/null 2>&1; then
  # Python has no zstd in the standard library before 3.14, so this may need the
  # `zstandard` package. Installing it is a smaller imposition than failing --
  # and it is announced, not silent.
  if ! python3 -c 'import zstandard' >/dev/null 2>&1; then
    echo '    installing the `zstandard` python package to unpack the toolchain'
    python3 -m pip install --quiet --break-system-packages zstandard >/dev/null 2>&1 ||
      python3 -m pip install --quiet zstandard >/dev/null 2>&1 || true
  fi
  if python3 - "$tmp/lean.tar.zst" "$dest" <<'PY'
import sys, tarfile
try:
    import zstandard
except ImportError:
    sys.exit(1)
src, dest = sys.argv[1], sys.argv[2]
with open(src, "rb") as f, zstandard.ZstdDecompressor().stream_reader(f) as r:
    with tarfile.open(fileobj=r, mode="r|") as t:
        for m in t:
            parts = m.name.split("/", 1)
            if len(parts) < 2:   # the tarball's single top-level directory
                continue
            m.name = parts[1]    # what --strip-components=1 does
            t.extract(m, dest, set_attrs=True, filter="tar")
PY
  then
    unpacked=1
  fi
fi

if [ "$unpacked" -eq 0 ]; then
  echo 'error: could not decompress the toolchain. Install `zstd` (apt install zstd,' >&2
  echo '       brew install zstd) or the python `zstandard` package, and re-run.' >&2
  exit 1
fi

if [ ! -x "$dest/bin/lean" ]; then
  echo "error: unpacked toolchain has no bin/lean at $dest" >&2
  exit 1
fi
echo "    $TOOLCHAIN unpacked from the GitHub release into $dest"
elan toolchain list
