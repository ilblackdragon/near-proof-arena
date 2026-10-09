"""Fail-closed process/output checks for the D2 differential runner."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest
from unittest.mock import patch

from difftest_v3_d2 import main, run_checker


class CheckerOutputTests(unittest.TestCase):
    def run_output(self, output, cases=("a", "b")):
        with patch("difftest_v3_d2.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)) as run:
            result = run_checker([sys.executable, "checker.py"], list(cases), 100, 1)
            self.assertTrue(run.call_args.kwargs["check"])
            return result

    def row(self, case):
        return json.dumps({"case": case, "verdict": "reject", "reason": "invalid"}) + "\n"

    def test_complete_results(self):
        self.assertEqual(set(self.run_output(self.row("a") + self.row("b"))), {"a", "b"})

    def test_missing_result_fails(self):
        with self.assertRaises(ValueError):
            self.run_output(self.row("a"))

    def test_duplicate_result_fails(self):
        with self.assertRaises(ValueError):
            self.run_output(self.row("a") * 2 + self.row("b"))

    def test_unknown_result_fails(self):
        with self.assertRaises(ValueError):
            self.run_output(self.row("a") + self.row("other"))

    def test_non_json_fails(self):
        with self.assertRaises(ValueError):
            self.run_output("checker crashed\n" + self.row("a") + self.row("b"))

    def test_duplicate_input_across_batches_fails(self):
        with self.assertRaises(ValueError):
            run_checker(["checker"], ["a", "./a"], 1, 1)

    def test_process_failure_propagates(self):
        with patch("difftest_v3_d2.subprocess.run", side_effect=subprocess.CalledProcessError(1, [])):
            with self.assertRaises(subprocess.CalledProcessError):
                run_checker(["checker"], ["a"], 100, 1)


class SavedResultsTests(unittest.TestCase):
    def run_extension(self, disagrees=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            d2 = root / "d2corpus" / "d2" / "case"
            d1 = root / "d1corpus" / "d1" / "case"
            for case in (d2, d1):
                case.mkdir(parents=True)
                (case / "meta.json").write_text(json.dumps({
                    "expected_rel": True, "expected_rel_d1": not disagrees,
                    "expected_rel_d2": True,
                }))
            def row(case):
                return {"case": str(case), "verdict": "accept", "reason": ""}
            for name, case in (("lean", d2), ("python", d2), ("d1lean", d1)):
                (root / name).write_text(json.dumps(row(case)) + "\n")
            args = ["difftest", "--cases", str(d2.parent.parent), "--python", "checker.py",
                    "--lean-from", str(root / "lean"), "--python-from", str(root / "python"),
                    "--d1-corpus", str(d1.parent.parent), "--d1-lean-from", str(root / "d1lean"),
                    "--save", str(root / "saved")]
            with patch.object(sys, "argv", args), contextlib.redirect_stdout(io.StringIO()), \
                    patch("difftest_v3_d2.run_checker", return_value={str(d1): {**row(d1), "verdict": "reject" if disagrees else "accept"}}) as run:
                with self.assertRaises(SystemExit) as result:
                    main()
                self.assertEqual(result.exception.code, int(disagrees))
                run.assert_called_once()
                self.assertEqual(run.call_args.args[1], [str(d1)])
            report = json.loads((root / "saved" / "report.json").read_text())
            self.assertEqual(report["d1_corpus_check"]["issues"], int(disagrees))
            for name in ("lean_from", "python_from", "d1_lean_from"):
                self.assertEqual(len(report[name]["sha256"]), 64)
            self.assertTrue((root / "saved" / "d1corpus-lean.jsonl").is_file())
            self.assertTrue((root / "saved" / "d1corpus-python.jsonl").is_file())

    def test_d1_extension_reuses_complete_d2_baselines(self):
        self.run_extension()

    def test_d2_disagreement_outside_d1_is_rejected(self):
        self.run_extension(disagrees=True)


if __name__ == "__main__":
    unittest.main()
