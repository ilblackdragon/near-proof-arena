"""Validate trie trace framing before invoking the differential checker."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "difftest_ttn", Path(__file__).resolve().parents[1] / "d3-ttn/difftest_ttn.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class TraceTests(unittest.TestCase):
    def line(self):
        return "C root 1 node 1 alice 1000 - ok " + " ".join(["0"] * 13)

    def test_complete_profile(self):
        rows = driver.parse_trace([self.line()])
        self.assertEqual(rows, [[("alice", "ok " + " ".join(["0"] * 13))]])

    def test_truncated_call_fails(self):
        with self.assertRaises(ValueError):
            driver.parse_trace([self.line().rsplit(" ", 1)[0]])

    def test_extra_call_data_fails(self):
        with self.assertRaises(ValueError):
            driver.parse_trace([self.line() + " 0"])

    def test_bad_header_fails(self):
        with self.assertRaises(ValueError):
            driver.parse_trace([self.line().replace("C root", "bad root")])

    def test_negative_node_count_fails(self):
        with self.assertRaises(ValueError):
            driver.parse_trace(["C root -1 0"])


if __name__ == "__main__":
    unittest.main()
