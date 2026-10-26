#!/usr/bin/env python3
"""Fresh-process, separately-built Rayon commitment campaign runner."""
import argparse, csv, json, os, platform, random, shutil, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HACHI = ROOT / "hachi"
HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
RAW = RESULTS / "raw"
TEST = "raw_streamed_commit_breakdown_profile"

def out(cmd, **kw):
    return subprocess.run(cmd, text=True, capture_output=True, **kw)

def first(cmd):
    p = out(cmd)
    return p.stdout.strip() if p.returncode == 0 else None

def metadata(config):
    cpuinfo = Path("/proc/cpuinfo").read_text(errors="replace") if Path("/proc/cpuinfo").exists() else ""
    models = [x.split(":", 1)[1].strip() for x in cpuinfo.splitlines() if x.startswith("model name")]
    physical = {(p.split(":",1)[1].strip(), c.split(":",1)[1].strip())
                for chunk in cpuinfo.split("\n\n") for p, c in [(next((x for x in chunk.splitlines() if x.startswith("physical id")), "physical id: 0"), next((x for x in chunk.splitlines() if x.startswith("core id")), "core id: 0"))]}
    governor = first(["bash", "-lc", "cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null"])
    return {"captured_at": datetime.now(timezone.utc).isoformat(), "git_sha": first(["git", "rev-parse", "HEAD"]),
            "git_dirty": bool(first(["git", "status", "--porcelain"])), "rustc": first(["rustc", "--version"]),
            "cargo": first(["cargo", "--version"]), "kernel": platform.release(), "os": platform.platform(),
            "cpu_model": models[0] if models else None, "logical_cpus": os.cpu_count(), "physical_cores": len(physical) or None,
            "cpu_governor": governor, "memory": first(["bash", "-lc", "grep MemTotal /proc/meminfo 2>/dev/null"]),
            "build_profile": "release (Cargo release defaults; no profile override)", "timing_scope": "commit_streamed_32 only; fixture construction excluded from Rust phase timing; whole-process wall/RSS include fixture construction",
            "dimensions": {"message_rows": 1024, "inner_rows": 1, "gadget_digits": 8, "outer_rows": 1}, "config": config}

def build(variant, target):
    env = os.environ | {"CARGO_TARGET_DIR": str(target)}
    cmd = ["cargo", "test", "--release", "--no-run", "--test", "commit_semantics"]
    if variant == "rayon": cmd[3:3] = ["--features", "parallel"]
    p = out(cmd, cwd=HACHI, env=env)
    if p.returncode: raise RuntimeError("build failed for %s:\n%s" % (variant, p.stderr))

def parse_breakdown(stderr):
    import re
    match = re.search(r"\[commit-breakdown\].*?prep=([0-9.]+)(ms|s).*?blocks=([0-9.]+)(ms|s).*?flatten_outer=([0-9.]+)(ms|s).*?total=([0-9.]+)(ms|s)", stderr)
    if not match: return {}
    def sec(x, unit): return float(x) / 1000 if unit == "ms" else float(x)
    return dict(zip(("phase_prep_s", "phase_blocks_s", "phase_outer_s", "commit_total_s"), [sec(match.group(i), match.group(i+1)) for i in range(1, 9, 2)]))

def proc_rss(pid):
    try:
        values = dict(line.split(":", 1) for line in Path(f"/proc/{pid}/status").read_text().splitlines() if ":" in line)
        return int(values.get("VmHWM", values.get("VmRSS", "0")).split()[0])
    except (FileNotFoundError, ProcessLookupError, ValueError): return 0

def process_tree_rss(root):
    """Resident memory of the cargo process and its current descendants."""
    parents = {}
    for stat in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = stat.read_text().rsplit(") ", 1)[1].split()
            parents[int(stat.parent.name)] = int(fields[1])
        except (FileNotFoundError, IndexError, ValueError): pass
    family = {root}; changed = True
    while changed:
        changed = False
        for pid, parent in parents.items():
            if parent in family and pid not in family: family.add(pid); changed = True
    return sum(proc_rss(pid) for pid in family)

def run_one(item, target, timeout, affinity):
    variant, workers, blocks, rep = item
    ident = f"{variant}-w{workers if workers else 0}-b{blocks}-r{rep}-{int(time.time()*1e6)}"
    stdout, stderr = RAW / f"{ident}.stdout.log", RAW / f"{ident}.stderr.log"
    env = os.environ | {"CARGO_TARGET_DIR": str(target), "HACHI_COMMIT_BLOCKS": str(blocks)}
    if workers: env["RAYON_NUM_THREADS"] = str(workers)
    cmd = ["cargo", "test", "--release", "--test", "commit_semantics"]
    if variant == "rayon": cmd += ["--features", "parallel"]
    cmd += ["--", "--ignored", "--nocapture", TEST]
    if affinity: cmd = ["taskset", "-c", affinity] + cmd
    started = time.monotonic(); status = "ok"; rc = None; peak = 0
    try:
        p = subprocess.Popen(cmd, cwd=HACHI, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        while p.poll() is None:
            peak = max(peak, process_tree_rss(p.pid)); time.sleep(0.05)
            if time.monotonic() - started > timeout:
                p.kill(); raise subprocess.TimeoutExpired(cmd, timeout)
        stdout_text, stderr_text = p.communicate(); rc = p.returncode
        if rc: status = "failed"
        stdout.write_text(stdout_text); stderr.write_text(stderr_text)
    except subprocess.TimeoutExpired:
        status = "timeout"; stdout.write_text(""); stderr.write_text("")
    wall = time.monotonic() - started
    row = {"id": ident, "timestamp": datetime.now(timezone.utc).isoformat(), "variant": variant, "workers": workers or 0, "blocks": blocks, "repetition": rep, "status": status, "returncode": rc, "wall_s": wall, "stdout_log": str(stdout.relative_to(RESULTS)), "stderr_log": str(stderr.relative_to(RESULTS))}
    row.update(parse_breakdown(stderr.read_text(errors="replace")))
    row["peak_rss_kib"] = peak or None
    return row

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--mode", choices=["pilot", "full", "custom"], default="pilot"); ap.add_argument("--blocks", type=int); ap.add_argument("--repetitions", type=int); ap.add_argument("--timeout", type=int); ap.add_argument("--affinity"); ap.add_argument("--no-build", action="store_true"); ap.add_argument("--resume", action="store_true", help="retain completed matching runs and execute only missing plan entries"); args = ap.parse_args()
    config = json.loads((HERE / "config.json").read_text()); RAW.mkdir(parents=True, exist_ok=True)
    blocks = [args.blocks] if args.blocks else config["pilot_blocks" if args.mode == "pilot" else "full_blocks"]
    reps = args.repetitions if args.repetitions is not None else config["pilot_repetitions" if args.mode == "pilot" else "full_repetitions"]
    timeout, affinity = args.timeout or config["timeout_seconds"], args.affinity or config.get("cpu_affinity")
    (RESULTS / "metadata.json").write_text(json.dumps(metadata(config), indent=2) + "\n")
    targets = {v: ROOT / "target" / f"rayon-{v}" for v in ("serial", "rayon")}
    if not args.no_build:
        for v, target in targets.items(): build(v, target)
    plan = [("serial", None, b, r) for b in blocks for r in range(reps)] + [("rayon", w, b, r) for b in blocks for w in config["workers"] for r in range(reps)]
    random.Random(config["seed"]).shuffle(plan)
    rows = []
    if args.resume and (RESULTS / "measurements.csv").exists():
        with (RESULTS / "measurements.csv").open() as f: rows = list(csv.DictReader(f))
        completed = {(r["variant"], int(r["workers"]) or None, int(r["blocks"]), int(r["repetition"])) for r in rows}
        plan = [item for item in plan if item not in completed]
        print(f"Resuming: {len(rows)} existing record(s), {len(plan)} planned run(s) remaining.", flush=True)
    for n, item in enumerate(plan, 1):
        print(f"[{n}/{len(plan)}] {item}", flush=True); rows.append(run_one(item, targets[item[0]], timeout, affinity))
        fields = sorted({k for x in rows for k in x}); path = RESULTS / "measurements.csv"
        with path.open("w", newline="") as f: w = csv.DictWriter(f, fieldnames=fields); w.writeheader(); w.writerows(rows)
    print("Run `python3 benchmarks/rayon/report.py` to summarize and plot.")
if __name__ == "__main__": main()
