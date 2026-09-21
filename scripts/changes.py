#!/usr/bin/env python3
"""From a ledger row to the code change behind it.

A ledger row records what a candidate did and what it bought, but it cannot
name the commit it landed in: the row is written before that commit exists,
and the file is append-only, so nothing may edit it in afterwards. What closes
the loop is the house rule that a row *rides the work it describes* -- row and
champion enter history in the same commit -- which makes `git blame` on the
row's line the pointer the row itself cannot carry. This script follows that
pointer and shows the part of the commit that made the code faster: the diff
under `hachi/src/`, with `hachi/lean/Opt.lean` (the change stated as
mathematics, with its proved `opt_eq_spec`) on request. Everything else in a
champion commit -- regenerated `Generated.lean`, restated specs, docs, tests --
is the price of the change, not the change.

    make changes                  every accepted row: description, commit, diffstat
    make changes ARGS='--diff'    the full patch under hachi/src/ instead of a stat
    make changes ARGS='--lean'    also the Opt.lean part (works with --diff)
    make changes ARGS='--all'     every row, whatever its verdict or kind
    make changes ARGS=zerocheck   only rows whose op matches this regex

Reads only. Exits 0 unless the inputs are unreadable, or `--strict` is given
and some accepted row is not yet in history or landed without any change under
hachi/src/ -- which means the row did not ride its work, and the pointer above
is broken for it.
"""
from __future__ import annotations
import argparse, json, pathlib, re, subprocess, sys, textwrap

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEDGER = ROOT / "logs" / "ledger.jsonl"
CODE = ["hachi/src"]
LEAN = sorted(str(p.relative_to(ROOT)) for p in (ROOT / "hachi" / "lean").glob("Opt*.lean"))
UNCOMMITTED = "0" * 40


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout


def blame_commits() -> list[str]:
    """The full commit hash that introduced each line of the ledger, in order.
    Uncommitted lines come back as forty zeros."""
    out = git("blame", "-l", "-s", "--", str(LEDGER.relative_to(ROOT)))
    return [line.split(" ", 1)[0].lstrip("^") for line in out.splitlines()]


def load_rows() -> list[tuple[int, dict]]:
    rows = []
    for n, line in enumerate(LEDGER.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            rows.append((n, json.loads(line)))
        except json.JSONDecodeError as e:
            sys.exit(f"changes: {LEDGER.relative_to(ROOT)}:{n}: not valid JSON ({e})")
    return rows


def is_accepted(row: dict) -> bool:
    return "kind" not in row and str(row.get("verdict", "")).startswith("accepted")


MODULE_RE = re.compile(r"\bhachi::([a-z_]+)::")


def row_paths(row: dict) -> list[str]:
    """The source files a row's `item` names (`hachi::<module>::…` →
    hachi/src/<module>.rs), so two champions that landed in one commit each
    show their own diff. Falls back to the whole of hachi/src/ when the row
    names no module."""
    mods = sorted(set(MODULE_RE.findall(str(row.get("item", "")))))
    files = [f"hachi/src/{m}.rs" for m in mods if (ROOT / "hachi/src" / f"{m}.rs").exists()]
    return files or CODE


def changed_files(commit: str, paths: list[str]) -> list[str]:
    out = git("show", "--name-only", "--format=", commit, "--", *paths)
    return [l for l in out.splitlines() if l.strip()]


def wrap(label: str, text: str, width: int = 88) -> str:
    body = textwrap.fill(" ".join(str(text).split()), width=width,
                         initial_indent=f"  {label:<10}", subsequent_indent=" " * 12)
    return body


def show(commit: str, paths: list[str], diff: bool) -> str:
    fmt = ["--format="]
    args = ["show", *fmt, commit, "--"] if diff else ["show", "--stat", *fmt, commit, "--"]
    out = git(*args, *paths)
    return out.rstrip("\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("pattern", nargs="?", default=".",
                    help="regex over the row's `op`; default every row")
    ap.add_argument("--all", action="store_true",
                    help="every row, not just accepted candidates")
    ap.add_argument("--diff", action="store_true",
                    help="the full patch instead of a diffstat")
    ap.add_argument("--lean", action="store_true",
                    help="also show the hachi/lean/Opt.lean part of the commit")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 if an accepted row is uncommitted or landed with no code change")
    a = ap.parse_args()

    if not LEDGER.exists():
        print(f"changes: no ledger at {LEDGER.relative_to(ROOT)}")
        return 0
    try:
        pattern = re.compile(a.pattern)
    except re.error as e:
        sys.exit(f"changes: bad regex {a.pattern!r}: {e}")

    rows = load_rows()
    if not rows:
        print("changes: the ledger is empty -- nothing has been accepted yet")
        return 0
    try:
        commits = blame_commits()
    except subprocess.CalledProcessError:
        # A ledger that exists on disk but was never committed has no blame.
        commits = []

    broken = 0
    shown = 0
    for n, row in rows:
        if not (a.all or is_accepted(row)):
            continue
        if not pattern.search(row.get("op", "")):
            continue
        shown += 1
        kind = row.get("kind", "candidate")
        verdict = row.get("verdict") or row.get("result") or "—"
        print("=" * 88)
        print(f"{row.get('ts', '?')}  {row.get('op', '?')}  [{kind}: {verdict}]"
              + (f"  run {row['run']}" if row.get("run") else ""))
        if row.get("strategy"):
            print(f"  {'strategy':<10}{row['strategy']}")
        what = row.get("candidate") or row.get("champion") or ""
        if what:
            print(wrap("change", what))
        if row.get("item"):
            print(wrap("rust", row["item"]))

        commit = commits[n - 1] if n - 1 < len(commits) else UNCOMMITTED
        if commit == UNCOMMITTED:
            print("  commit    (not yet committed -- the row is staged or unstaged; it must land in the same commit as its work)")
            if is_accepted(row):
                broken += 1
            continue
        subject = git("log", "-1", "--format=%h %ad  %s", "--date=short", commit).strip()
        print(f"  {'commit':<10}{subject}")

        if kind == "campaign":
            # The proof side of an accepted champion: specs restated, Opt.lean
            # lemmas. Generated.lean is regenerated output, not the change.
            lean = [p for p in changed_files(commit, ["hachi/lean"]) if not p.endswith("Generated.lean")]
            print(f"  {'proof':<10}" + (", ".join(lean) if lean else "(no Lean change in this commit)"))
            continue
        if kind != "candidate" or not is_accepted(row):
            # Rejected / unusable candidates and experiment rows land no code;
            # the commit that carries the row may carry someone else's champion.
            print("  code      (none: this row lands no code change; its slot_sha fingerprints the discarded diff)")
            continue

        own = row_paths(row) + (LEAN if a.lean else [])
        code = show(commit, own, a.diff)
        if not code.strip():
            print(f"  code      NONE under {', '.join(own)} -- this row did not ride its work")
            broken += 1
            continue
        print(f"  {'code':<10}git show {commit[:7]} -- {' '.join(own)}")
        print(textwrap.indent(code, "    "))
        others = [p for p in changed_files(commit, CODE) if p not in own]
        if others:
            print(f"  {'also':<10}same commit, outside the row's modules: {', '.join(others)}")

    if shown == 0:
        print("changes: no row matches" + ("" if a.all else " (accepted candidates only; --all for every row)"))
    if broken:
        print("=" * 88)
        print(f"changes: {broken} accepted row(s) cannot be traced to a code change -- see above")
        return 1 if a.strict else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
