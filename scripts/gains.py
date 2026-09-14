#!/usr/bin/env python3
"""The optimization scoreboard: every row's cumulative gain, run by run.

Two files carry the loop's numbers and neither sums them. `logs/runs/*.json` are
`make run-bench` reports (one per run, named by run id); each row's `vs_genesis`
is the current champion against the frozen first translation, both measured in
the *same* criterion session, so it is the cumulative gain of every accepted
champion on that row, valid on any date. `logs/ledger.jsonl` holds one row per
candidate verdict with that candidate's within-run increment (`cand_vs_now_adj`).
This script lays the two side by side and adds nothing of its own: it never
subtracts across runs, never compares absolute times, and skips reports the
harness marked `unusable` (their file names carry `-UNUSABLE`).

    make gains                 every row, every usable run, newest run last
    make gains ARGS=zerocheck     only rows whose case matches this regex (quote shell
                                  metacharacters: ARGS="'zerocheck/(c_w|zc)'")
    make gains ARGS='--ledger'    also the ledger's accepted increments per row

Reads only; exits 0 unless the inputs are unreadable.
"""
from __future__ import annotations
import argparse, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
RUNS = ROOT / "logs" / "runs"
LEDGER = ROOT / "logs" / "ledger.jsonl"


def load_runs() -> list[dict]:
    out = []
    for p in sorted(RUNS.glob("*.json")):
        if "UNUSABLE" in p.name:
            continue
        try:
            d = json.loads(p.read_text())
        except json.JSONDecodeError as e:
            sys.exit(f"gains: {p}: not valid JSON ({e})")
        if not d.get("usable", True):
            continue
        d["_file"] = p.name
        out.append(d)
    out.sort(key=lambda d: d.get("run", ""))
    return out


def pct(x) -> str:
    return "      ·" if x is None else f"{x * 100:+6.1f}%"


def scoreboard(runs: list[dict], pattern: re.Pattern) -> None:
    cases: dict[str, dict[str, float]] = {}
    for d in runs:
        for r in d.get("rows", []):
            case = r["case"]
            if case.startswith("_control") or not pattern.search(case):
                continue
            # In a CANDIDATE=1 run `now` is the champion *before* the swap, so the
            # cumulative figure of interest is the candidate's `cand_vs_genesis`;
            # it is shown with a trailing `c` to say which variant was measured.
            if r.get("cand_vs_genesis") is not None:
                cases.setdefault(case, {})[d["run"]] = (r["cand_vs_genesis"], "c")
            else:
                cases.setdefault(case, {})[d["run"]] = (r.get("vs_genesis"), " ")
    if not cases:
        print("gains: no rows match")
        return
    ids = [d["run"] for d in runs]
    print("cumulative gain over the frozen genesis, per row and run -- a within-run ratio.")
    print("plain = the champion (`now`) of a full run; `c` = the candidate slot of a")
    print("CANDIDATE=1 run, i.e. the champion that run accepted; blank = not measured.\n")
    head = f"{'case':<40}" + "".join(f"{i[:13]:>15}" for i in ids)
    print(head)
    print("-" * len(head))
    for case in sorted(cases):
        cells = []
        for i in ids:
            v = cases[case].get(i)
            cells.append(f"{'      ·':>15}" if v is None else f"{pct(v[0]) + v[1]:>15}")
        print(f"{case:<40}" + "".join(cells))
    print("\nruns:")
    for d in runs:
        src = d.get("source", {})
        print(f"  {d['run']}  source {src.get('sha', '?')}{' +uncommitted' if src.get('src_dirty') else ''}"
              f"  A/B bias {d.get('ab_bias', 0) * 100:.1f}%  rows {len([r for r in d.get('rows', []) if not r['case'].startswith('_control')])}"
              f"  ({d['_file']})")


def ledger(pattern: re.Pattern) -> None:
    if not LEDGER.exists():
        return
    print("\naccepted candidates and their within-run increment (`cand_vs_now_adj`), from the ledger\n")
    for n, line in enumerate(LEDGER.read_text().splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        if row.get("kind") is not None or row.get("verdict") != "accepted":
            continue
        rows = [r for r in row.get("rows", []) if pattern.search(r.get("case", ""))]
        if not rows:
            continue
        print(f"  {row['ts']}  {row['op']}  run {row.get('run', '?')}  [{row['strategy']}]")
        print(f"    {row['candidate'][:110]}")
        for r in rows:
            print(f"    {r['case']:<40} {pct(r.get('cand_vs_now_adj')):>9}  {r.get('verdict', '')}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pattern", nargs="?", default=".", help="regex on the case id")
    ap.add_argument("--ledger", action="store_true", help="also list the ledger's accepted increments")
    a = ap.parse_args()
    pattern = re.compile(a.pattern)
    runs = load_runs()
    if not runs:
        print(f"gains: no usable reports under {RUNS.relative_to(ROOT)}/ -- run `make run-bench JSON=logs/runs/<id>.json`")
    else:
        scoreboard(runs, pattern)
    if a.ledger:
        ledger(pattern)
    return 0


if __name__ == "__main__":
    sys.exit(main())
