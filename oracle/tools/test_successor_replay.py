"""Adversarial process and comparison controls for successor evidence."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("replay_successor", REPO / "tools/d3/replay_successor.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

class Results(unittest.TestCase):
    def row(self, case="a", **kw):
        return json.dumps(dict(case=case, verdict="accept", reason="", tier="signed") | kw) + "\n"

    def test_valid(self):
        self.assertEqual(len(runner.parse_rows(self.row(), ["a"], "signed")), 1)

    def test_bad_populations_and_rows(self):
        for output, cases in [
            ("", []), (self.row(), ["a", "./a"]), ("", ["a"]),
            (self.row() * 2, ["a"]), (self.row("foreign"), ["a"]),
            ("noise\n" + self.row(), ["a"]), (self.row(verdict="io_error"), ["a"]),
            (self.row(tier="genesis"), ["a"]), (self.row(reason=None), ["a"]),
        ]:
            with self.subTest(output=output, cases=cases), self.assertRaises(ValueError):
                runner.parse_rows(output, cases, "signed")

    def test_baseline_parser_rejects_incomplete_or_ambiguous_results(self):
        baseline = runner.load_compare()
        for output in ("", self.row() * 2, self.row("foreign"), "noise"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                baseline.parse_results(output.splitlines(), ["a"])

    def test_preflight_failure_invalidates_old_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            report = Path(tmp) / "report.json"
            report.write_text('{"status":"pass"}')
            with self.assertRaises(ValueError):
                runner.replay(sys.executable, "signed", [], tmp)
            self.assertEqual(json.loads(report.read_text())["status"], "fail")

    def test_process_failure_after_valid_output(self):
        with patch.object(runner.subprocess, "run", side_effect=subprocess.CalledProcessError(1, [])):
            with self.assertRaises(subprocess.CalledProcessError):
                runner.run_batch(["checker"], ["a"], 1)

    def test_timeout(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            runner.run_batch([sys.executable, "-c", "import time; time.sleep(60)"], ["a"], .05)

    def test_failed_replay_records_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = Path(tmp) / "case"
            case.mkdir()
            (case / "claim.bin").write_bytes(b"claim")
            (case / "witness.bin").write_bytes(b"witness")
            (case / "meta.json").write_text(json.dumps({"expected_rel": True, "in_d3": True}))
            with patch.object(runner, "run_batch", side_effect=ValueError("missing output")):
                with self.assertRaises(ValueError):
                    runner.replay(sys.executable, "signed", [case], Path(tmp) / "out")
            report = json.loads((Path(tmp) / "out/report.json").read_text())
            self.assertEqual(report["status"], "fail")
            self.assertEqual(report["failure"], "ValueError")
            self.assertEqual(len(report["package"]["sha256"]), 64)
            self.assertEqual(report["inputs"][0]["files"]["claim.bin"],
                             runner.sha256(case / "claim.bin"))

class Expectations(unittest.TestCase):
    def compare(self, violations, widen, verdict, reason=""):
        mod = runner.load_compare()
        return mod.compare("test", ["a"], {"a": {
            "expected_rel": True, "in_d3": False, "d3_violations": violations,
        }}, {"a": {"verdict": verdict, "reason": reason}},
            domain="successor", widen=widen)[1]

    def test_protocol_gas_can_widen_old_capacity(self):
        self.assertFalse(self.compare(["e.g_alpha"], ["e.g_alpha"], "accept"))
        self.assertTrue(self.compare(["e.g_alpha"], [], "accept"))

    def test_combined_exclusions_only_license_remaining_family(self):
        self.assertFalse(self.compare(["e.float", "e.secp"], ["e.float"],
                                      "out_of_domain", "out of domain (e.secp)"))
        self.assertTrue(self.compare(["e.float", "e.secp"], ["e.float"],
                                     "out_of_domain", "out of domain (e.wasm-α): float"))
        self.assertTrue(self.compare(["e.float"], ["e.float"],
                                     "out_of_domain", "out of domain (e.wasm-α): float"))

if __name__ == "__main__":
    unittest.main()
