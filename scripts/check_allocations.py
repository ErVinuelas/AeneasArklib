"""Count heap calls in a staged baseline/candidate worktree; no timing claims."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import tomllib

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("worktree", type=Path)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
worktree = args.worktree.resolve()

def identities():
    return {
        variant: {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in sorted(directory.glob("*.rs"))}
        for variant, directory in (("baseline", worktree / "hachi/src"),
                                   ("candidate", worktree / "hachi/benches/candidate/src"))
    }

source_identities = identities()
cpoly = tomllib.loads((worktree / "hachi/Cargo.toml").read_text())["dependencies"]["cpoly"]
if not isinstance(cpoly, dict) or not {"git", "rev"} <= cpoly.keys():
    raise SystemExit("Expected an explicitly git/revision-pinned cpoly dependency")

with tempfile.TemporaryDirectory(prefix="hachi-allocation-audit-") as temporary:
    project = Path(temporary)
    # JSON strings are also valid TOML basic strings for these absolute paths.
    manifest = '''[package]
name = "hachi-allocation-audit"
version = "0.0.0"
edition = "2021"
[[bin]]
name = "hachi-allocation-audit"
path = "main.rs"
[dependencies]
CPOLY_DEPENDENCY
[profile.release]
lto = "fat"
codegen-units = 1
'''
    manifest = manifest.replace("CPOLY_DEPENDENCY", "cpoly = { git = " +
        json.dumps(cpoly["git"]) + ", rev = " + json.dumps(cpoly["rev"]) + " }")
    manifest = manifest.replace("[profile.release]", "\n".join([
        "hachi = { path = " + json.dumps(str(worktree / "hachi")) + " }",
        "hachi-candidate = { path = " + json.dumps(str(worktree / "hachi/benches/candidate")) + " }",
        "[profile.release]",
    ]))
    (project / "Cargo.toml").write_text(manifest)
    (project / "main.rs").write_bytes((root / "docs/optimization/allocation-audit/main.rs").read_bytes())
    subprocess.run(["cargo", "+nightly-2026-06-01", "build", "--offline", "--release"],
                   cwd=project, check=True)
    repetitions = []
    for _ in range(3):
        text = subprocess.check_output([str(project / "target/release/hachi-allocation-audit")], text=True)
        repetitions.append([json.loads(line) for line in text.splitlines()])
    if any(rows != repetitions[0] for rows in repetitions[1:]):
        raise SystemExit("Allocation counts were not repeatable")
    if identities() != source_identities:
        raise SystemExit("Sources changed during the allocation audit")
    rows = repetitions[0]
    for case in {row["case"] for row in rows}:
        pair = [row for row in rows if row["case"] == case]
        assert len(pair) == 2 and pair[0]["checksum"] == pair[1]["checksum"], case
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        "note": "Allocation calls, not timings or peak memory. Reduced shapes; see source. Zero-check checksum is not an oracle.",
        "repetitions": 3, "identical_repetitions": True, "rows": rows,
        "source_sha256": source_identities,
        "instrument_sha256": hashlib.sha256((project / "main.rs").read_bytes()).hexdigest(),
        "rustc": subprocess.check_output(["rustc", "+nightly-2026-06-01", "--version", "--verbose"], text=True),
    }, indent=2) + "\n")
    print(args.output)
