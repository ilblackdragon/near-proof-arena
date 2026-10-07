"""Regression checks for missing, extra, crashed and reordered harness output."""
import subprocess
import sys
import unittest

from harness_io import run_lines, run_shards


class HarnessTests(unittest.TestCase):
    def cmd(self, code):
        return [sys.executable, "-c", code]

    def test_nonzero_exit_with_complete_output_fails(self):
        with self.assertRaises(subprocess.CalledProcessError):
            run_lines(self.cmd('print("ok"); raise SystemExit(7)'), ["input"])

    def test_missing_line_fails(self):
        with self.assertRaises(ValueError):
            run_lines(self.cmd('print("ok")'), ["a", "b"])

    def test_extra_line_fails(self):
        with self.assertRaises(ValueError):
            run_lines(self.cmd('print("ok\\nextra")'), ["a"])

    def test_shards_preserve_order(self):
        inputs = [str(i) for i in range(7)]
        self.assertEqual(run_shards(self.cmd('import sys; print(sys.stdin.read(), end="")'),
                                    inputs, 3), inputs)

    def test_variable_calls_per_chunk_preserve_order(self):
        command = self.cmd('import sys\nfor line in sys.stdin:\n for item in line.strip().split(","):\n  if item: print(item)')
        self.assertEqual(run_shards(command, ["a,b", "c", "", "d,e,f"], 3, [2, 1, 0, 3]),
                         list("abcdef"))

    def test_zero_shards_fails(self):
        with self.assertRaises(ValueError):
            run_shards([], ["a"], 0)

    def test_short_count_list_fails(self):
        with self.assertRaises(ValueError):
            run_shards([], ["a", "b"], 1, [1])


if __name__ == "__main__":
    unittest.main()
