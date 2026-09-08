#!/usr/bin/env python3
"""Which mirrored items have an equivalence statement, and which do not.

`make bench-check`'s `coverage` gate asks whether every item claiming to mirror
an ArkLib definition is *benched or excluded* -- whether anyone measures it.
Nothing asked the other question: whether anyone has *stated* what it computes.
That asymmetry is how `lean-wip/README.md` came to claim coverage of
`quadeval::rel_out` and `quadeval::paper_rel_out` that does not exist (the
theorem named `paper_rel_out_implies_rel_out_spec` is about `vec_in_sb`), and
how eleven `quadeval` items sat unspecified without anything noticing.

An item counts as specified when a file under `hachi/lean/` or
`hachi/lean-wip/` mentions its extracted Lean name (`<module>.<path>`), with two
files deliberately excluded from the search:

* `Generated.lean`, which is the model itself -- every item is in it by
  construction, so counting it would make the check vacuous;
* `Check.lean`, whose section 2b holds one type ascription per item. Those pin
  the model's *shape*, not what it computes, so counting them would also make
  the check vacuous -- and that is exactly the trap this script exists to avoid:
  the first version of it reported "0 owed" for that reason.

Reports, and never fails: an unspecified item is proof debt to schedule, not a
broken invariant. `--strict` is available for a future policy that wants it.
"""
from __future__ import annotations
import argparse, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
HARNESS = ROOT / "hachi" / "benches" / "harness.py"
SPEC_DIRS = (ROOT / "hachi" / "lean", ROOT / "hachi" / "lean-wip")
NOT_A_SPEC = {"Generated.lean", "Check.lean"}


def mirrored_items() -> list[tuple[str, str]]:
    """`(item path, ArkLib name)` for every item the coverage gate knows about."""
    out = subprocess.run([sys.executable, str(HARNESS), "coverage", "-v"],
                         capture_output=True, text=True, cwd=ROOT).stdout
    return re.findall(r"^\s+\S+\s+(\S+::\S+)\s+->\s+(\S+)", out, re.M)


def spec_text() -> tuple[str, list[str]]:
    files = [p for d in SPEC_DIRS if d.is_dir() for p in sorted(d.glob("*.lean"))
             if p.name not in NOT_A_SPEC]
    return "".join(p.read_text() for p in files), [p.name for p in files]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict", action="store_true",
                    help="exit non-zero when anything is unspecified")
    args = ap.parse_args()

    items = mirrored_items()
    text, files = spec_text()
    owed = [(it, ark) for it, ark in items if it.replace("::", ".") not in text]

    print(f"==> spec coverage: {len(items)} mirrored item(s), "
          f"{len(items) - len(owed)} stated, {len(owed)} OWED")
    print(f"    searched: {', '.join(files)}")
    by_mod: dict[str, list[tuple[str, str]]] = {}
    for it, ark in owed:
        by_mod.setdefault(it.split("::")[0], []).append((it, ark))
    for mod in sorted(by_mod):
        print(f"\n  {mod} ({len(by_mod[mod])} owed)")
        for it, ark in by_mod[mod]:
            print(f"    {it:34} -> {ark}")
    if owed and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
