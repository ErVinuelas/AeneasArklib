"""Run serial controlled comparisons in a prepared baseline/candidate worktree.

Run on the host (not inside an isolated PID namespace), with other builds stopped.
All raw Criterion JSON produced by each invocation is archived. No timing is
accepted if another Lean/Rust build or harness appears during measurement.
"""
import argparse
import json, os, re, signal, subprocess, tarfile, time
from pathlib import Path
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("worktree", type=Path)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--label", required=True)
parser.add_argument("--cpu", type=int)
parser.add_argument("modules", nargs="+")
args = parser.parse_args()
if not re.fullmatch(r"[A-Za-z0-9_.-]+", args.label) or any(
        not re.fullmatch(r"[a-z][a-z0-9_]*", module) for module in args.modules):
    parser.error("Use a simple run label and Rust module names")
ROOT = args.worktree.resolve()
OUT = args.output.resolve()
OUT.mkdir(parents=True, exist_ok=True)
run_label = args.label
modules = args.modules
allowed = sorted(os.sched_getaffinity(0))
cpu = args.cpu if args.cpu is not None else (4 if 4 in allowed else allowed[0])
if cpu not in allowed:
    raise SystemExit("Requested CPU is outside the allowed affinity set")

def active_work(own_group=None):
    processes = subprocess.check_output(
        ["ps", "-eo", "pgid=,stat=,comm=,args="], text=True)
    competing = []
    for line in processes.splitlines():
        fields = line.split(maxsplit=3)
        if len(fields) < 4:
            continue
        group, state, executable, command = fields
        if state.startswith("Z") or int(group) == own_group:
            continue
        if executable in ("lean", "lake", "rustc") or (
            executable == "cargo" and re.search(r"\b(bench|build|test)\b", command)
        ) or (executable.startswith("python") and "harness.py" in command):
            competing.append(line)
    return competing

for module in modules:
    name = run_label + "-" + module
    report = OUT / (name + ".json")
    artifacts = [report, OUT / (name + ".log"),
                 OUT / (name + "-samples.tar.gz"), OUT / (name + "-execution.json")]
    if any(path.exists() for path in artifacts):
        raise SystemExit("Refusing to overwrite an existing run: " + name)
    competing_at_start = active_work()
    if competing_at_start:
        raise SystemExit("Competing build/benchmark detected; postponing: " + str(competing_at_start))
    start = time.time()
    command = ["taskset", "-c", str(cpu), "make", "run-bench", "CANDIDATE=1",
               "BENCH=^(" + module + "/|_control/" + module + "/)", "JSON=" + str(report)]
    print("START", name, "cpu", cpu, flush=True)
    with (OUT / (name + ".log")).open("w") as log:
        result = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                  start_new_session=True)
        interference = []
        while result.poll() is None:
            time.sleep(2)
            interference = active_work(result.pid)
            if interference:
                print("INTERRUPTED", name, "competing build/benchmark started", flush=True)
                try:
                    os.killpg(result.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass  # The child finished between poll and termination.
                try:
                    result.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(result.pid, signal.SIGKILL)
                    result.wait()
                break
    artifact = OUT / (name + "-samples.tar.gz")
    with tarfile.open(artifact, "w:gz") as archive:
        for file in sorted((ROOT / "hachi/target/criterion").rglob("*.json")):
            if file.stat().st_mtime >= start:
                archive.add(file, arcname=str(file.relative_to(ROOT / "hachi/target/criterion")))
    report_error = None
    usable = False
    try:
        data = json.loads(report.read_text())
        if not isinstance(data, dict) or not isinstance(data.get("usable"), bool):
            raise ValueError("Report has no Boolean usability status")
        usable = data["usable"]
    except (OSError, ValueError) as error:
        report_error = str(error)
    (OUT / (name + "-execution.json")).write_text(json.dumps({
        "command": command, "cpu_affinity": [cpu], "start_epoch": start,
        "end_epoch": time.time(), "exit_code": result.returncode,
        "competing_processes_at_start": competing_at_start, "interference": interference,
        "report_usable": usable, "report_error": report_error,
    }, indent=2) + "\n")
    print("END", name, "exit", result.returncode, flush=True)
    # GNU Make returns 2 for any recipe failure, including compile/gate failures.
    # A report plus a successful exit are both necessary; neither substitutes
    # for the other. Retain unusable reports but stop the campaign fail-closed.
    if result.returncode != 0 or interference or report_error or not usable:
        raise SystemExit("Benchmark did not produce a successful usable report: " + name)
