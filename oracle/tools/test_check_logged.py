"""The regression driver must never turn truncated checker output into a pass."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_logged import parse_results, run_batch


def result(case="case-a", **changes):
    return json.dumps({"case": case, "verdict": "accept", "reason": "", **changes})


class CheckerOutputTests(unittest.TestCase):
    def test_all_results_can_arrive_out_of_order(self):
        rows = parse_results(result("b") + "\n" + result("a"), ["a", "b"])
        self.assertEqual(set(rows), {"a", "b"})

    def test_missing_result_fails(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            parse_results(result(), ["case-a", "case-b"])

    def test_duplicate_result_fails(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            parse_results(result() + "\n" + result(), ["case-a"])

    def test_unknown_case_fails(self):
        with self.assertRaisesRegex(ValueError, "unknown"):
            parse_results(result("unexpected"), ["case-a"])

    def test_truncated_json_fails(self):
        with self.assertRaises(json.JSONDecodeError):
            parse_results(result()[:-1], ["case-a"])

    def test_invalid_verdict_fails(self):
        with self.assertRaisesRegex(ValueError, "verdict"):
            parse_results(result(verdict="missing"), ["case-a"])

    def test_nonzero_exit_fails_even_with_complete_output(self):
        with tempfile.TemporaryDirectory() as directory:
            checker = Path(directory) / "checker"
            checker.write_text(f"#!{sys.executable}\nprint({result()!r})\nraise SystemExit(1)\n")
            checker.chmod(0o755)
            with self.assertRaises(subprocess.CalledProcessError):
                run_batch(checker, "d3", ["case-a"])


if __name__ == "__main__":
    unittest.main()
