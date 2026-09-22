"""Positive and adversarial fixtures for the Lean model-preservation checker."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
LEAN = ["elan", "run", (ROOT / "hachi/lean-toolchain").read_text().strip(), "lean"]
FOUNDATION = """import Lean
namespace Model
def empty : List Nat := []
def with_capacity (_ : Nat) : List Nat := empty
end Model
"""
BASELINE = """import Foundation
namespace hachi
structure State where
  values : List Nat
def table (_n : Nat) : List Nat := Model.empty
private def hidden : Nat := 42
def answer : Nat := hidden
end hachi
def outside_namespace : Nat := 7
"""
CANDIDATE = BASELINE.replace(":= Model.empty", ":= Model.with_capacity _n")


class PreservationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.baseline = self.directory / "baseline"
        self.candidate = self.directory / "candidate"
        self.compile(self.baseline, BASELINE)

    def compile(self, path, source, foundation=FOUNDATION):
        path.mkdir(exist_ok=True)
        for name, text in (("Foundation", foundation), ("Generated", source)):
            (path / f"{name}.lean").write_text(text)
            result = subprocess.run(
                LEAN + ["-o", f"{name}.olean", f"{name}.lean"], cwd=path,
                env={**os.environ, "LEAN_PATH": str(path)},
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            self.assertEqual(result.returncode, 0, result.stdout)

    def check(self, source=CANDIDATE, foundation=FOUNDATION):
        self.compile(self.candidate, source, foundation)
        return subprocess.run(
            LEAN + [str(ROOT / "scripts/CheckAllocationPreservation.lean")],
            cwd=self.candidate,
            env={**os.environ, "LEAN_PATH": str(self.candidate),
                 "HACHI_BASELINE_LEAN_PATH": str(self.baseline)},
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )

    def test_definitionally_equal_allocation_passes(self):
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Kernel checked", result.stdout)

    def test_changed_result_fails(self):
        result = self.check(CANDIDATE.replace("private def hidden : Nat := 42",
                                              "private def hidden : Nat := 43"))
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_outside_namespace_change_fails(self):
        result = self.check(CANDIDATE.replace("outside_namespace : Nat := 7",
                                              "outside_namespace : Nat := 8"))
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_added_declaration_fails(self):
        result = self.check(CANDIDATE + "\ndef unaccounted : Nat := 1\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("declaration counts differ", result.stdout)

    def test_missing_baseline_cannot_fall_back_to_candidate(self):
        self.baseline = self.directory / "missing"
        result = self.check()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Baseline Generated.olean does not exist", result.stdout)

    def test_changed_imported_model_fails(self):
        result = self.check(foundation=FOUNDATION.replace(":= empty", ":= [1]"))
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Imported kernel declaration changed", result.stdout)


if __name__ == "__main__":
    unittest.main()
