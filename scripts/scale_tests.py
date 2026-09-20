#!/usr/bin/env python3
"""Classify the `#[ignore]`d tests, so `make test-scale` derives its list.

Every `#[ignore]` reason in `hachi/tests/` opens with one of three tags. The
tag is the whole point: an ignored test is either an *instrument* -- a timing
gate or a profile, which must never join a correctness sweep because putting
timing in the test suite is exactly what the bench harness's accept rule
exists to prevent -- or a *correctness test walled by scale*, in which case
the only question is whether this machine can hold it.

    instrument:  a timing gate, kill-gate, diagnostic or profile. Run by hand.
    scale:       a correctness test at the paper's constants, runnable here.
    scale-xl:    the same, but past this machine -- by resident memory or by
                 wall clock. Its reason carries the measurement that put it
                 there, so a bigger machine knows what it is taking on.

`make test-scale` runs the `scale:` set. `scale-xl:` is what a bigger machine
would add. A new `#[ignore]`
without a tag fails `--check`, which is the point -- the choice should be
made when the attribute is written, not rediscovered a month later.
"""
import re
import sys
from pathlib import Path

TESTS = Path(__file__).resolve().parent.parent / "hachi" / "tests"
TAGS = ("instrument:", "scale:", "scale-xl:")
IGNORE = re.compile(r'^\s*#\[ignore\s*=\s*"(.*?)"\s*\]\s*$')
FN = re.compile(r"^\s*(?:pub\s+)?fn\s+([A-Za-z0-9_]+)")


def scan():
    """(file, test name, tag, rest of reason) for every `#[ignore]`d test."""
    out = []
    for path in sorted(TESTS.glob("*.rs")):
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            m = IGNORE.match(line)
            if not m:
                continue
            reason = m.group(1)
            name = None
            for nxt in lines[i + 1 : i + 12]:
                f = FN.match(nxt)
                if f:
                    name = f.group(1)
                    break
            tag = next((t for t in TAGS if reason.startswith(t)), None)
            out.append((path.name, name, tag, reason[len(tag):].strip() if tag else reason))
    return out


def main() -> int:
    rows = scan()
    mode = sys.argv[1] if len(sys.argv) > 1 else "--list"

    if mode == "--check":
        bad = [(f, n, r) for f, n, t, r in rows if t is None or n is None]
        for f, n, r in bad:
            what = "no tag" if n else "no fn found after the attribute"
            print(f"  - {f}::{n}: {what} -- {r[:60]}", file=sys.stderr)
        if bad:
            print(
                f"==> {len(bad)} untagged `#[ignore]`(s). Open each reason with one of "
                + ", ".join(f"`{t}`" for t in TAGS),
                file=sys.stderr,
            )
            return 1
        counts = {t: sum(1 for *_, tag, _ in rows if tag == t) for t in TAGS}
        print(
            "==> ignore tags: "
            + ", ".join(f"{counts[t]} {t.rstrip(':')}" for t in TAGS)
            + f" ({len(rows)} total)"
        )
        return 0

    if mode == "--list":            # what `make test-scale` runs
        for f, n, t, _ in rows:
            if t == "scale:":
                print(f"{f[:-3]} {n}")
        return 0

    if mode == "--all":
        for f, n, t, r in rows:
            print(f"{t or 'UNTAGGED':<12} {f[:-3]:<20} {n:<56} {r[:58]}")
        return 0

    print(f"usage: {sys.argv[0]} [--list|--all|--check]", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
