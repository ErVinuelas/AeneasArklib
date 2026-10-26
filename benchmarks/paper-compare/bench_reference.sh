#!/usr/bin/env bash
#
# bench_reference.sh -- build the paper's reference implementation (hachi-pcs),
# run it N times at l = 30 and average each phase.
#
# Usage:
#   ./bench_reference.sh                     # 10 runs, standard (stable) build
#   AVX512=1 ./bench_reference.sh            # nightly build with tfhe-ntt AVX-512
#   N=3 L=24 ./bench_reference.sh            # quick smoke test at a smaller size
#   ./bench_reference.sh --summarize DIR     # re-summarize logs of an earlier run
#   ./bench_reference.sh --prepare           # clone, witness file, build (used by bench_interleaved.sh)
#   ./bench_reference.sh --run-one LOGFILE   # one timed run into LOGFILE (after --prepare)
#
# Environment:
#   WORK      working directory (clone, witness file)  (default: benchmarks/paper-compare/work)
#   N         number of timed runs                              (default: 10)
#   L         number of variables, witness has 2^L u32 values   (default: 30 -> 4 GiB file)
#   AVX512    1 = `cargo +nightly build --features=nightly`     (default: 0, stable)
#   COOLDOWN  seconds to sleep between runs                     (default: 0)
#   OUT       output directory   (default: benchmarks/paper-compare/results/ref-<build>-<timestamp>)
#
# Cost: ~9-10 min per run at L=30, plus one extra untimed run that GENERATES the
# witness file (the reference's own generator also runs the whole pipeline).
# Needs ~4 GiB of disk and ~14 GiB of RAM. Keep the machine idle, on mains power.
#
# The reference is pinned to the commit used for the paper-impl baseline in
# logs/paper-impl/README.md. It prints its timings as a Graphviz DOT graph at the
# end of each run; spans are read from that output:
#   Commit               = the large `commit::commit` span (the top-level witness commit)
#   Prove                = `prove::prove`            (excludes the commit above)
#   sumcheck             = `sumcheck_proof`
#   everything else      = Prove - sumcheck
#   Verify               = `verify::verify`
#   (extra) prove-internal re-commit = the small second `commit::commit` span

set -euo pipefail

summarize() {
python3 - "$1" <<'PY'
import csv, glob, os, re, statistics as st, sys

out = sys.argv[1]
UNIT = {'ns': 1e-9, 'us': 1e-6, 'µs': 1e-6, 'μs': 1e-6, 'ms': 1e-3, 's': 1.0}
NUM = r'([0-9]+(?:\.[0-9]+)?)\s*(ns|[µμ]s|ms|s)(?![A-Za-z])'
SPAN = re.compile(r'(\S+) ran for ' + NUM + r', called (\d+) times')

def parse(text, name):
    spans = [(m.group(1).strip('"'), float(m.group(2)) * UNIT[m.group(3)])
             for m in SPAN.finditer(text)]
    if not spans:
        raise SystemExit(f'{name}: no time-graph spans found (did the run finish?)')
    def pick(suffix):
        xs = [t for n, t in spans if n.endswith(suffix)]
        if not xs:
            raise SystemExit(f'{name}: span "{suffix}" not found')
        return xs
    commits = pick('commit::commit')
    d = {
        'commit': max(commits),                       # top-level witness commit
        'recommit': min(commits) if len(commits) > 1 else 0.0,
        'prove': pick('prove::prove')[0],
        'sumcheck': pick('sumcheck_proof')[0],
        'verify': pick('verify::verify')[0],
    }
    d['rest'] = d['prove'] - d['sumcheck']
    d['commit_plus_prove'] = d['commit'] + d['prove']
    return d

logs = sorted(p for p in glob.glob(os.path.join(out, 'run_*.log'))
              if 'discard' not in os.path.basename(p))
if not logs:
    raise SystemExit(f'no run_*.log files in {out}')
runs = [parse(open(p, encoding='utf-8', errors='replace').read(), os.path.basename(p)) for p in logs]

ROWS = [('Commit', 'commit'), ('Prove (excl. commit)', 'prove'),
        ('  of which sumcheck', 'sumcheck'), ('  of which everything else', 'rest'),
        ('Verify', 'verify')]
EXTRA = [('Commit + prove', 'commit_plus_prove'), ('Prove-internal re-commit', 'recommit')]

def stats(key):
    xs = [r[key] for r in runs]
    return (st.mean(xs), min(xs), max(xs), st.stdev(xs) if len(xs) > 1 else 0.0)

def fmt(label, key):
    s = stats(key)
    return f'{label:<42}{s[0]:>10.3f}{s[1]:>10.3f}{s[2]:>10.3f}{s[3]:>10.3f}'

print(f'\nReference: {len(runs)} run(s) from {out}\n')
print(f'{"Phase (seconds)":<42}{"mean":>10}{"min":>10}{"max":>10}{"stdev":>10}')
print('-' * 82)
for l, k in ROWS:
    print(fmt(l, k))
print('-' * 82)
for l, k in EXTRA:
    print(fmt(l, k))
print('\nPer run (s):  run   commit   prove   verify')
for i, r in enumerate(runs, 1):
    print(f'              {i:>3}  {r["commit"]:>7.1f}  {r["prove"]:>6.1f}  {r["verify"]:>7.3f}')

with open(os.path.join(out, 'runs.csv'), 'w', newline='') as f:
    keys = sorted(runs[0])
    w = csv.writer(f); w.writerow(['run'] + keys)
    for i, r in enumerate(runs, 1):
        w.writerow([i] + [f'{r[k]:.6f}' for k in keys])
with open(os.path.join(out, 'summary.csv'), 'w', newline='') as f:
    w = csv.writer(f); w.writerow(['phase', 'mean_s', 'min_s', 'max_s', 'stdev_s'])
    for l, k in ROWS + EXTRA:
        w.writerow([l.strip(), *[f'{x:.6f}' for x in stats(k)]])
print(f'\nWrote {out}/runs.csv and {out}/summary.csv')
PY
}

REF_URL="https://github.com/georgeorourke/hachi-pcs"
REF_COMMIT="6d90caca64386e506bdd5d0097f87ccb98fc0926"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${WORK:-$HERE/work}"
N="${N:-10}"
L="${L:-30}"
AVX512="${AVX512:-0}"
COOLDOWN="${COOLDOWN:-0}"
BUILD=$([[ "$AVX512" == 1 ]] && echo avx512 || echo std)
OUT="${OUT:-$HERE/results/ref-$BUILD-$(date +%Y%m%d-%H%M%S)}"
SRC="$WORK/hachi-pcs"
WITNESS="${WITNESS:-$WORK/witness_l$L.bin}"
EXPECTED_BYTES=$(( 4 * (1 << L) ))                 # 2^L u32 coefficients
if [[ "$AVX512" == 1 ]]; then
    BIN="$SRC/target-avx512/release/hachi"
    BUILD_CMD=(cargo +nightly build --release --features=nightly --target-dir target-avx512)
else
    BIN="$SRC/target-std/release/hachi"
    BUILD_CMD=(cargo build --release --target-dir target-std)
fi

prepare() {
    for tool in git cargo python3; do
        command -v "$tool" >/dev/null || { echo "missing required tool: $tool" >&2; exit 1; }
    done
    if [[ "$AVX512" == 1 ]] && ! cargo +nightly --version >/dev/null 2>&1; then
        echo "AVX512=1 needs a nightly toolchain (rustup toolchain install nightly)" >&2; exit 1
    fi
    mkdir -p "$WORK" "$OUT"
    if [[ ! -d "$SRC/.git" ]]; then
        git clone "$REF_URL" "$SRC"
    fi
    git -C "$SRC" checkout -q "$REF_COMMIT"
    {
        echo "date:     $(date -Is)"
        echo "kernel:   $(uname -sr)"
        echo "cpu:      $(lscpu 2>/dev/null | sed -n 's/^Model name:[[:space:]]*//p' | head -1)"
        echo "governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
        echo "loadavg:  $(cut -d' ' -f1-3 /proc/loadavg)"
        echo "cargo:    $(cargo --version)   (nightly: $(cargo +nightly --version 2>/dev/null || echo none))"
        echo "ref rev:  $(git -C "$SRC" rev-parse HEAD)"
        echo "build=$BUILD N=$N L=$L witness=$WITNESS"
    } | tee "$OUT/env.txt"

    # 1. Witness file. The reference's `gen_file` feature writes it, then runs the
    #    whole pipeline once; that run is kept only as a discarded log.
    if [[ ! -f "$WITNESS" || "$(stat -c %s "$WITNESS")" -ne "$EXPECTED_BYTES" ]]; then
        echo "[$(date +%T)] generating the $((EXPECTED_BYTES >> 20)) MiB witness file (one extra untimed run)..."
        (cd "$SRC" && cargo build --release --features=gen_file --target-dir target-gen) >"$OUT/build_gen.log" 2>&1 \
            || { echo "gen build failed, see $OUT/build_gen.log" >&2; tail -20 "$OUT/build_gen.log" >&2; exit 1; }
        "$SRC/target-gen/release/hachi" "$WITNESS" "$L" >"$OUT/run_00_generate_discard.log" 2>&1 \
            || { echo "witness generation run failed, see $OUT/run_00_generate_discard.log" >&2; exit 1; }
    fi

    # 2. The timed build: the same source WITHOUT gen_file, so the file is never rewritten.
    echo "[$(date +%T)] building the timed binary ($BUILD)..."
    if ! (cd "$SRC" && "${BUILD_CMD[@]}") >"$OUT/build.log" 2>&1; then
        echo "build failed, see $OUT/build.log" >&2; tail -20 "$OUT/build.log" >&2; exit 1
    fi
    [[ -x "$BIN" ]] || { echo "binary not found at $BIN" >&2; exit 1; }
}

run_one() {
    local log="$1"
    [[ -x "$BIN" ]] || { echo "no binary at $BIN; run --prepare first" >&2; exit 1; }
    cat "$WITNESS" >/dev/null          # warm page cache, as in the baseline
    if ! "$BIN" "$WITNESS" "$L" >"$log" 2>&1; then
        echo "reference run failed, see $log" >&2; tail -20 "$log" >&2; exit 1
    fi
    grep -q 'ran for' "$log" || { echo "reference run printed no timing graph, see $log" >&2; exit 1; }
    grep -E 'commit::commit ran for|prove::prove ran for' "$log" | sed -E 's/^.*"(.*)".*$/    ref:  \1/' | head -2
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
