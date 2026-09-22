"""Exercise failure handling without running real benchmarks or processes."""
import contextlib
import io
import json
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("run_optimization_benchmarks.py")

class BenchmarkRunnerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.out = self.root / "evidence"
        self.out.mkdir()
        self.report = self.out / "fixture-ring.json"

    def run_fixture(self, code=0, report=None, processes=""):
        def launch(*args, **kwargs):
            if report is not None:
                self.report.write_text(report)
            class Completed:
                pid = 777
                returncode = code
                def poll(self):
                    return code
            return Completed()
        argv = [str(SCRIPT), str(self.root), "--output", str(self.out),
                "--label", "fixture", "ring"]
        with patch("sys.argv", argv), patch("os.sched_getaffinity", return_value={4}), \
             patch("subprocess.check_output", return_value=processes), \
             patch("subprocess.Popen", side_effect=launch) as spawn, \
             contextlib.redirect_stdout(io.StringIO()):
            try:
                runpy.run_path(str(SCRIPT), run_name="__main__")
                outcome = 0
            except SystemExit as error:
                outcome = error.code
            return outcome, spawn.call_count

    def test_success_requires_usable_report(self):
        self.assertEqual(self.run_fixture(report=json.dumps({"usable": True}))[0], 0)

    def test_make_failure_is_not_unusable_measurement_success(self):
        self.assertNotEqual(self.run_fixture(code=2)[0], 0)
        metadata = json.loads((self.out / "fixture-ring-execution.json").read_text())
        self.assertEqual(metadata["exit_code"], 2)
        self.assertIsNotNone(metadata["report_error"])

    def test_missing_report_fails_even_with_zero_exit(self):
        self.assertNotEqual(self.run_fixture()[0], 0)

    def test_invalid_report_fails(self):
        self.assertNotEqual(self.run_fixture(report="not json")[0], 0)

    def test_unusable_report_fails(self):
        self.assertNotEqual(self.run_fixture(report=json.dumps({"usable": False}))[0], 0)

    def test_failure_with_valid_report_still_fails(self):
        self.assertNotEqual(self.run_fixture(code=2, report=json.dumps({"usable": True}))[0], 0)

    def test_every_retained_artifact_prevents_overwrite(self):
        for suffix in [".json", ".log", "-execution.json", "-samples.tar.gz"]:
            with self.subTest(suffix=suffix):
                path = self.out / ("fixture-ring" + suffix)
                path.write_bytes(b"prior evidence")
                result, calls = self.run_fixture()
                self.assertNotEqual(result, 0)
                self.assertEqual(calls, 0)
                self.assertEqual(path.read_bytes(), b"prior evidence")
                path.unlink()

    def test_other_checkout_cargo_bench_blocks_start(self):
        result, calls = self.run_fixture(processes="123 S cargo cargo bench --manifest-path /other/Cargo.toml")
        self.assertNotEqual(result, 0)
        self.assertEqual(calls, 0)

    def test_runtime_interference_terminates_own_group(self):
        class Running:
            pid = 777
            returncode = None
            def poll(self):
                return None
            def wait(self, timeout=None):
                self.returncode = -15
                return -15
        argv = [str(SCRIPT), str(self.root), "--output", str(self.out),
                "--label", "fixture", "ring"]
        processes = ["", "777 S cargo cargo bench\n123 S lean lean Other.lean"]
        with patch("sys.argv", argv), patch("os.sched_getaffinity", return_value={4}), \
             patch("subprocess.check_output", side_effect=processes), \
             patch("subprocess.Popen", return_value=Running()), \
             patch("time.sleep"), patch("os.killpg") as kill, \
             contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit):
                runpy.run_path(str(SCRIPT), run_name="__main__")
        kill.assert_called_once_with(777, 15)
        metadata = json.loads((self.out / "fixture-ring-execution.json").read_text())
        self.assertEqual(metadata["interference"], ["123 S lean lean Other.lean"])

if __name__ == "__main__":
    unittest.main()
