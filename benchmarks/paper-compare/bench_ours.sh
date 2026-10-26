#!/usr/bin/env bash
#
# bench_ours.sh -- run this repo's pin-scale profile N times and average each phase.
#
# Usage:
#   ./bench_ours.sh                       # 10 runs at the paper's scale (BLOCKS=1024)
#   N=3 BLOCKS=64 ./bench_ours.sh         # quick smoke test
#   ./bench_ours.sh --summarize DIR       # re-summarize logs of an earlier run
#   ./bench_ours.sh --prepare             # checks + build only (used by bench_interleaved.sh)
#   ./bench_ours.sh --run-one LOGFILE     # one timed run into LOGFILE (after --prepare)
#
# Environment:
#   REPO      path to the AeneasArklib checkout            (default: the one holding this script)
#   N         number of runs                               (default: 10)
#   BLOCKS    instance size for `make run-profile`         (default: 1024)
#   COOLDOWN  seconds to sleep between runs                (default: 0)
#   OUT       output directory   (default: benchmarks/paper-compare/results/ours-<timestamp>)
#
# Cost: ~9.5 min per run at BLOCKS=1024 (about 6 min of that is untimed test
# scaffolding), so 10 runs is ~1.6 hours. Keep the machine idle and on mains power.
#
# What is averaged (same rows as the comparison image):
#   Commit                  = "committed N block(s)" line
#   Prove (excl. commit)    = prover total - commit
#   sumcheck                = honest_round_messages + alpha_public_table + c_w_table_mle
#   everything else         = prove (excl. commit) - sumcheck
#   Verify (core check)     = statement thread + round_verify_loop + final_check
# Prover total = sum of every timed prover phase in the profile (dense_eval, which is
# untimed test scaffolding, and the verifier lines are excluded). This sum reproduces
# the 183.2 s in NOTES.md for the 9/25 log ONLY IF the two table lines are counted
# separately from honest_round_messages (as done here), although that line's label
# says "incl. its own two tables". The "sumcheck rounds only" extra row lets you
# check the alternative.

set -euo pipefail

summarize() {
python3 - "$1" <<'PY'
import csv, glob, os, re, statistics as st, sys

out = sys.argv[1]
UNIT = {'ns': 1e-9, 'us': 1e-6, 'µs': 1e-6, 'μs': 1e-6, 'ms': 1e-3, 's': 1.0}
NUM = r'([0-9]+(?:\.[0-9]+)?)\s*(ns|[µμ]s|ms|s)(?![A-Za-z])'
TIMED = re.compile(r'\+\s*' + NUM + r'\s+peak\s+\d+\s+live\s+\d+\s+MiB\s+(.*?)\s*$')
PROF = re.compile(r'^\[profile\]\s+(.+?):\s+' + NUM)
SPREAD = re.compile(r'control CPU spread within run:\s*([+-]?[0-9.]+)%')

TIMED_KEYS = [
    ('commit', 'committed '), ('statement', 'statement built'),
    ('carrier', 'carrier_decomp_from_raw'), ('v_decomp', 'honest_compute_v_from_decomp'),
    ('resp', 'honest_compute_resp'), ('dropped', 'raw message dropped'),
    ('rlin', 'R^lin statement assembled'), ('mzeta', 'M zeta = y SKIPPED'),
    ('lifted', 'lifted witness built'),
]
PROF_KEYS = [
    ('lift_commit', 'lift_commit'), ('c_w_table', 'c_w_table_mle'),
    ('alpha_table', 'alpha_public_table'), ('rounds', 'honest_round_messages'),
    ('y', 'honest_compute_y'),
    ('v_stmt', 'verifier: rlin_stmt + statement thread'),
    ('v_loop', 'verifier: round_verify_loop'), ('v_final', 'verifier: final_check'),
    ('v_end', 'verifier: end_piece_check'), ('v_whole', 'chain_verify (whole)'),
]
PROVER = ['commit', 'statement', 'carrier', 'v_decomp', 'resp', 'dropped', 'rlin',
          'mzeta', 'lifted', 'lift_commit', 'c_w_table', 'alpha_table', 'rounds', 'y']
OPTIONAL = {'mzeta', 'dropped', 'spread'}

def parse(text, name):
    if re.search(r'(final_check|end_piece_check|chain_verify \(whole\)) = false', text):
        raise SystemExit(f'{name}: a verifier check printed "false"')
    d = {}
    for line in text.splitlines():
        m = TIMED.search(line)
        if m:
            v = float(m.group(1)) * UNIT[m.group(2)]
            for key, pat in TIMED_KEYS:
                if pat in m.group(3):
                    d[key] = v
                    break
            continue
        m = PROF.match(line)
        if m:
            v = float(m.group(2)) * UNIT[m.group(3)]
            for key, pat in PROF_KEYS:
                if pat in m.group(1):
                    d[key] = v
                    break
            continue
        m = SPREAD.search(line)
        if m:
            d['spread'] = float(m.group(1))
    need = [k for k, _ in TIMED_KEYS + PROF_KEYS if k not in d and k not in OPTIONAL]
    if need:
        raise SystemExit(f'{name}: could not find phase(s): {", ".join(need)}')
    d['prover_total'] = sum(d.get(k, 0.0) for k in PROVER)
    d['prove_excl_commit'] = d['prover_total'] - d['commit']
    d['tables'] = d['alpha_table'] + d['c_w_table']
    d['sumcheck'] = d['rounds'] + d['tables']
    d['rest'] = d['prove_excl_commit'] - d['sumcheck']
    d['verify_core'] = d['v_stmt'] + d['v_loop'] + d['v_final']
    return d

logs = sorted(glob.glob(os.path.join(out, 'run_*.log')))
if not logs:
    raise SystemExit(f'no run_*.log files in {out}')
runs = [parse(open(p, encoding='utf-8', errors='replace').read(), os.path.basename(p)) for p in logs]

ROWS = [('Commit', 'commit'), ('Prove (excl. commit)', 'prove_excl_commit'),
        ('  of which sumcheck (rounds + tables)', 'sumcheck'),
        ('  of which everything else', 'rest'), ('Verify (core check)', 'verify_core')]
EXTRA = [('Prover total (commit + prove)', 'prover_total'), ('  sumcheck rounds only', 'rounds'),
         ('  sumcheck setup tables', 'tables'), ('Verify closing step (end_piece_check)', 'v_end'),
         ('chain_verify (whole)', 'v_whole'), ('control CPU spread within run (%)', 'spread')]

def stats(key):
    xs = [r[key] for r in runs if key in r]
    if not xs:
        return None
    return (st.mean(xs), min(xs), max(xs), st.stdev(xs) if len(xs) > 1 else 0.0)

def fmt(label, key):
    s = stats(key)
    if s is None:
        return f'{label:<42}{"n/a":>10}'
    return f'{label:<42}{s[0]:>10.3f}{s[1]:>10.3f}{s[2]:>10.3f}{s[3]:>10.3f}'

print(f'\nOurs: {len(runs)} run(s) from {out}\n')
print(f'{"Phase (seconds)":<42}{"mean":>10}{"min":>10}{"max":>10}{"stdev":>10}')
print('-' * 82)
for l, k in ROWS:
    print(fmt(l, k))
print('-' * 82)
for l, k in EXTRA:
    print(fmt(l, k))
print('\nPer run (s):  run   commit   prove   verify_core')
for i, r in enumerate(runs, 1):
    print(f'              {i:>3}  {r["commit"]:>7.1f}  {r["prove_excl_commit"]:>6.1f}  {r["verify_core"]:>10.3f}')

with open(os.path.join(out, 'runs.csv'), 'w', newline='') as f:
    keys = sorted({k for r in runs for k in r})
    w = csv.writer(f); w.writerow(['run'] + keys)
    for i, r in enumerate(runs, 1):
        w.writerow([i] + [f'{r[k]:.6f}' if k in r else '' for k in keys])
with open(os.path.join(out, 'summary.csv'), 'w', newline='') as f:
    w = csv.writer(f); w.writerow(['phase', 'mean_s', 'min_s', 'max_s', 'stdev_s'])
    for l, k in ROWS + EXTRA:
        s = stats(k)
        if s:
            w.writerow([l.strip(), *[f'{x:.6f}' for x in s]])
print(f'\nWrote {out}/runs.csv and {out}/summary.csv')
PY
}

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="${REPO:-$(cd "$HERE/../.." && pwd)}"
N="${N:-10}"
BLOCKS="${BLOCKS:-1024}"
COOLDOWN="${COOLDOWN:-0}"
OUT="${OUT:-$HERE/results/ours-$(date +%Y%m%d-%H%M%S)}"

prepare() {
    for tool in make cargo python3; do
        command -v "$tool" >/dev/null || { echo "missing required tool: $tool" >&2; exit 1; }
    done
    [[ -f "$REPO/Makefile" && -d "$REPO/hachi" ]] || { echo "REPO=$REPO is not an AeneasArklib checkout" >&2; exit 1; }
    mkdir -p "$OUT"
    {
        echo "date:     $(date -Is)"
        echo "kernel:   $(uname -sr)"
        echo "cpu:      $(lscpu 2>/dev/null | sed -n 's/^Model name:[[:space:]]*//p' | head -1)"
        echo "governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
        echo "loadavg:  $(cut -d' ' -f1-3 /proc/loadavg)"
        echo "cargo:    $(cargo --version)"
        echo "git rev:  $(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo unknown) (dirty files: $(git -C "$REPO" status --porcelain 2>/dev/null | wc -l))"
        echo "N=$N BLOCKS=$BLOCKS COOLDOWN=$COOLDOWN"
    } | tee "$OUT/env.txt"
    echo "[$(date +%T)] building the profile test once (compile time is not part of any run)..."
    (cd "$REPO/hachi" && cargo test --release --test chain_semantics --no-run) >"$OUT/build.log" 2>&1 \
        || { echo "build failed, see $OUT/build.log" >&2; tail -20 "$OUT/build.log" >&2; exit 1; }
}

run_one() {
    local log="$1"
    if ! make -C "$REPO" run-profile BLOCKS="$BLOCKS" >"$log" 2>&1; then
        echo "profile run failed, see $log" >&2; tail -20 "$log" >&2; exit 1
    fi
    grep -q 'profile done' "$log" || { echo "profile run did not finish, see $log" >&2; exit 1; }
    grep -m1 'committed' "$log" | sed 's/  */ /g' | sed 's/^/    ours: /'
}

case "${1:-}" in
    --summarize) summarize "${2:?usage: $0 --summarize DIR}"; exit 0 ;;
    --prepare)   prepare; exit 0 ;;
    --run-one)   run_one "${2:?usage: $0 --run-one LOGFILE}"; exit 0 ;;
    "")          ;;
    *)           echo "usage: $0 [--summarize DIR | --prepare | --run-one LOGFILE]" >&2; exit 2 ;;
esac

prepare
for ((i = 1; i <= N; i++)); do
    printf -v idx '%02d' "$i"
    echo "[$(date +%T)] run $i/$N ..."
    run_one "$OUT/run_$idx.log"
    if (( i < N && COOLDOWN > 0 )); then sleep "$COOLDOWN"; fi
done

summarize "$OUT"
