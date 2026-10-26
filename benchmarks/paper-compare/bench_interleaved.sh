#!/usr/bin/env bash
#
# bench_interleaved.sh -- alternate our profile and the reference, N pairs, then
# summarize each side and the PAIRED ratios.
#
# Why: the two programs are timed minutes apart on a laptop whose speed drifts
# (thermals, power profile). Running all of one and then all of the other leaves
# that drift inside the comparison. Here each pair is adjacent in time, and the
# order alternates (ours-first, reference-first, ...) so a systematic "second run
# is hotter" effect cancels instead of favouring one side.
#
# Usage:
#   bash bench_interleaved.sh                  # 10 pairs, alternating order
#   N=3 BLOCKS=64 L=26 bash bench_interleaved.sh   # smoke test (matching sizes: L = 20 + log2(BLOCKS) )
#   ORDER=ours-first bash bench_interleaved.sh     # or ref-first; default: alternate
#
# Environment (all optional; the rest are read by the two single-side scripts):
#   REPO      AeneasArklib checkout          (default: the one holding this script)
#   WORK      reference working dir          (default: benchmarks/paper-compare/work)
#   N         number of pairs                (default: 10)
#   BLOCKS    ours: instance size            (default: 1024)
#   L         reference: variables           (default: 30; must match BLOCKS: L = 20 + log2 BLOCKS)
#   AVX512    1 = reference nightly AVX-512 build   (default: 0)
#   COOLDOWN  seconds between runs           (default: 0)
#   ROOT      output directory               (default: benchmarks/paper-compare/results/interleaved-<timestamp>)
#
# Cost at the paper's scale: ~9.5 min (ours) + ~9-10 min (reference) per pair,
# i.e. ~3.3 hours for 10 pairs, plus the one-time reference setup (clone, 4 GiB
# witness file, one extra ~10 min generation run). Keep the machine idle and on mains.
#
# Output: $ROOT/ours/ and $ROOT/ref/ (per-run logs, runs.csv, summary.csv) and
# $ROOT/paired.csv. The paired ratios are ours / reference, per pair, for the same
# five rows as the comparison image.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OURS="$HERE/bench_ours.sh"
REF="$HERE/bench_reference.sh"
[[ -f "$OURS" && -f "$REF" ]] || { echo "bench_ours.sh and bench_reference.sh must sit next to this script" >&2; exit 1; }

N="${N:-10}"
ORDER="${ORDER:-alternate}"
COOLDOWN="${COOLDOWN:-0}"
BLOCKS="${BLOCKS:-1024}"
L="${L:-30}"
ROOT="${ROOT:-$HERE/results/interleaved-$(date +%Y%m%d-%H%M%S)}"
case "$ORDER" in alternate|ours-first|ref-first) ;; *) echo "ORDER must be alternate, ours-first or ref-first" >&2; exit 2 ;; esac

# Sanity: the two sizes must describe the same problem (2^30 coefficients = 1024 blocks x 2^20 / ...).
EXPECTED_L=$(python3 -c "import math,sys; b=int(sys.argv[1]); print(20+int(round(math.log2(b))))" "$BLOCKS")
if [[ "$EXPECTED_L" != "$L" ]]; then
    echo "BLOCKS=$BLOCKS corresponds to L=$EXPECTED_L, but L=$L was given; the two sides would not match." >&2
    echo "Set both consistently (the paper's scale is BLOCKS=1024, L=30)." >&2
    exit 2
fi

OURS_OUT="$ROOT/ours"
REF_OUT="$ROOT/ref"
mkdir -p "$OURS_OUT" "$REF_OUT"
export REPO="${REPO:-$(cd "$HERE/../.." && pwd)}" WORK="${WORK:-$HERE/work}" BLOCKS L AVX512="${AVX512:-0}" N COOLDOWN

echo "=== setup (neither side is timed here) ==="
OUT="$OURS_OUT" bash "$OURS" --prepare
OUT="$REF_OUT"  bash "$REF"  --prepare

run_ours() { OUT="$OURS_OUT" bash "$OURS" --run-one "$OURS_OUT/run_$1.log"; }
run_ref()  { OUT="$REF_OUT"  bash "$REF"  --run-one "$REF_OUT/run_$1.log"; }

echo "=== $N interleaved pair(s), order: $ORDER ==="
for ((i = 1; i <= N; i++)); do
    printf -v idx '%02d' "$i"
    if [[ "$ORDER" == ours-first || ( "$ORDER" == alternate && $((i % 2)) -eq 1 ) ]]; then
        first=ours; second=ref
    else
        first=ref; second=ours
    fi
    echo "[$(date +%T)] pair $i/$N: $first, then $second"
    "run_$first" "$idx"
    if (( COOLDOWN > 0 )); then sleep "$COOLDOWN"; fi
    "run_$second" "$idx"
    if (( i < N && COOLDOWN > 0 )); then sleep "$COOLDOWN"; fi
done

echo; echo "=== each side, averaged over its $N runs ==="
bash "$OURS" --summarize "$OURS_OUT"
bash "$REF"  --summarize "$REF_OUT"

echo; echo "=== paired comparison (ours / reference, one ratio per pair) ==="
python3 - "$OURS_OUT/runs.csv" "$REF_OUT/runs.csv" "$ROOT/paired.csv" <<'PY'
import csv, statistics as st, sys

def load(p):
    with open(p, newline='') as f:
        return list(csv.DictReader(f))

ours, ref, outp = load(sys.argv[1]), load(sys.argv[2]), sys.argv[3]
n = min(len(ours), len(ref))
if len(ours) != len(ref):
    print(f'warning: {len(ours)} ours vs {len(ref)} reference runs; pairing the first {n}')
ROWS = [  # label, ours column, reference column
    ('Commit',                   'commit',            'commit'),
    ('Prove (excl. commit)',     'prove_excl_commit', 'prove'),
    ('  of which sumcheck',      'sumcheck',          'sumcheck'),
    ('  of which everything else', 'rest',            'rest'),
    ('Verify (core check)',      'verify_core',       'verify'),
]
print(f'{"Row":<28}{"ours (mean s)":>14}{"ref (mean s)":>14}{"mean ratio":>12}{"min":>8}{"max":>8}{"ours<ref":>10}')
print('-' * 94)
with open(outp, 'w', newline='') as f:
    w = csv.writer(f)
    w.writerow(['row', 'pair', 'ours_s', 'ref_s', 'ratio_ours_over_ref'])
    for label, co, cr in ROWS:
        a = [float(r[co]) for r in ours[:n]]
        b = [float(r[cr]) for r in ref[:n]]
        ratios = [x / y for x, y in zip(a, b)]
        for i, (x, y, q) in enumerate(zip(a, b, ratios), 1):
            w.writerow([label.strip(), i, f'{x:.6f}', f'{y:.6f}', f'{q:.6f}'])
        wins = sum(1 for q in ratios if q < 1)
        print(f'{label:<28}{st.mean(a):>14.3f}{st.mean(b):>14.3f}{st.mean(ratios):>12.3f}'
              f'{min(ratios):>8.3f}{max(ratios):>8.3f}{f"{wins}/{n}":>10}')
print('\nratio < 1 means ours is faster in that pair; "ours<ref" counts the pairs where it was.')
print(f'Wrote {outp}')
PY
