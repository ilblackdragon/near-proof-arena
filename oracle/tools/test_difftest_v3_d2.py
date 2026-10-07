"""Fail-closed process/output checks for the D2 differential runner."""
import json
import subprocess
import sys
import unittest
from unittest.mock import patch

from difftest_v3_d2 import run_checker


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


if __name__ == "__main__":
    unittest.main()
