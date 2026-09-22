"""Regression checks for the candidate measurement gate, using isolated fixtures."""

import argparse
import contextlib
import io
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "hachi/benches"))
import harness


class CandidateGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for relative in ("hachi/src", "hachi/benches/candidate", "hachi/benches/genesis"):
            shutil.copytree(REPO / relative, self.root / relative)
        self.src = self.root / "hachi/src"
        self.slot = self.root / "hachi/benches/candidate/src"
        # The fixture is a null slot even after a future champion is installed.
        for module in harness.MODULES:
            shutil.copy2(self.src / f"{module}.rs", self.slot / f"{module}.rs")
        self.pinned = {
            p: (self.root / p).read_text()
            for p in ("hachi/benches/candidate/src/lib.rs", "hachi/benches/candidate/Cargo.toml")
        }

    def gate(self, active):
        def git(*args, **kwargs):
            return self.pinned[args[1].removeprefix("HEAD:").removeprefix(":")]

        output = io.StringIO()
        with patch.multiple(harness, ROOT=self.root, SRC=self.src, CANDIDATE_SRC=self.slot), \
             patch.object(harness, "git", git), \
             contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            result = harness.cmd_check_candidate(argparse.Namespace(active=active))
        return result, output.getvalue()

    def change(self, relative, old, new):
        path = self.slot / relative
        source = path.read_text()
        self.assertIn(old, source)
        path.write_text(source.replace(old, new, 1))

    def test_null_slot_passes_both_modes(self):
        self.assertEqual(self.gate(False)[0], 0)
        self.assertEqual(self.gate(True)[0], 0)

    def test_real_candidate_allowed_only_during_measurement(self):
        self.change("gadget.rs", "rest = rest / b;", "rest = rest / b; // candidate fixture")
        self.assertEqual(self.gate(False)[0], 1)
        self.assertEqual(self.gate(True)[0], 0)

    def test_changed_control_is_rejected_before_measurement(self):
        self.change("ring.rs", "Vec::new()", "Vec::with_capacity(n)")
        code, message = self.gate(True)
        self.assertEqual(code, 1)
        self.assertIn("ring::Rq::zero: fairness control", message)

    def test_equal_live_and_candidate_control_cannot_drift_from_genesis(self):
        self.change("linalg.rs", "Vec::new()", "Vec::with_capacity(k)")
        shutil.copy2(self.slot / "linalg.rs", self.src / "linalg.rs")
        self.assertEqual(self.gate(False)[0], 0)
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_keeps_module_graph_pinned(self):
        self.change("lib.rs", "extern crate alloc;", "extern crate alloc;\nmod surprise;")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_changed_control_layout(self):
        self.change("ring.rs", "pub struct Rq", "#[repr(align(4096))]\npub struct Rq")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_changed_control_attributes(self):
        self.change("ring.rs", "    pub fn zero()", "    #[inline(never)]\n    pub fn zero()")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_multiline_control_attribute(self):
        self.change("ring.rs", "pub struct Rq", "#[repr(\n align(4096)\n)]\npub struct Rq")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_attribute_separated_by_comment(self):
        self.change("ring.rs", "    pub fn zero()",
                    "    #[inline(never)]\n    // allocation\n    pub fn zero()")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_extra_files(self):
        (self.slot / "surprise.rs").write_text("pub fn injected() {}\n")
        self.assertEqual(self.gate(True)[0], 1)

    def test_active_mode_rejects_symlinked_module(self):
        (self.slot / "ring.rs").unlink()
        (self.slot / "ring.rs").symlink_to(self.src / "ring.rs")
        self.assertEqual(self.gate(True)[0], 1)


if __name__ == "__main__":
    unittest.main()
