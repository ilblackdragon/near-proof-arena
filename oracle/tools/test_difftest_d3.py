"""Tests for oracle/v3-d3/tools/difftest_d3.py's exhaustive comparison partition.

The D3 difftest used to short-circuit on the g_alpha and code_cache classifier paths before the
accept/reject verdict test, leaving 1,259 out-of-domain cases in the `ood` family compared to
nothing (workplan W01, docs/logs/lean-chunk-L7-2026-10-23.md §4.4b). These tests pin the replacement:

  * every input lands in exactly one partition bucket and the buckets sum to the input count;
  * an out-of-domain verdict without a reason the oracle's own `d3_violations` licenses is a failure;
  * a licensed exclusion passes and is reported per case;
  * wrong verdicts, missing lines, malformed verdicts, exclusions on in-domain cases and accepting
    above G_alpha still fail (the controlled-breakage controls);
  * baseline and successor expectations are separate runs with distinct records.

The synthetic fixture reproduces the real population *shape* (1,010 g_alpha + 279 code_cache +
1,259 plain exclusions = 2,548) so the accounting is exercised without the corpora. A separate
optional test re-derives the same accounting from the pinned corpora when NEAR_CORPORA_DIR is set.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[2]
MODULE = REPO / "oracle/v3-d3/tools/difftest_d3.py"


def load_module():
    spec = importlib.util.spec_from_file_location("difftest_d3_under_test", MODULE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


d3 = load_module()


def meta(expected_rel=True, in_d3=False, violations=(), family="ood", **extra):
    m = {
        "expected_rel": expected_rel,
        "expected_rel_d3": bool(expected_rel) and bool(in_d3),
        "in_d3": in_d3,
        "d3_violations": list(violations),
        "features": {},
        "nearcore": "ok" if expected_rel else "reject",
    }
    m.update(extra)
    return m


def row(case, verdict, reason=""):
    return {"case": case, "verdict": verdict, "reason": reason}


def build_population(root):
    """Reproduce the real out-of-domain population shape:
       1,010 g_alpha  +  279 code_cache  +  1,259 plain exclusions  =  2,548.

    The 1,259 split into the five reason families the L7 log records:
       710 e.wasm-alpha, 373 w.shape, 137 c.not_genesis, 36 e.secp, 3 c.segment.
    """
    dirs, metas, got = [], {}, {}
    plan = (
        ["ood", "e.g_alpha", "out of domain (e.g_alpha): chunk function-call gas exceeds G_alpha", 1010],
        ["mutants", "e.code_cache",
         "out of domain (e.wasm-\u03b1): pre-state contract served only by the in-chunk compiled-contract cache", 279],
        ["ood", "e.wasm-\u03b1", "out of domain (e.wasm-\u03b1): float type or operator in a function body", 710],
        ["ood", "w.shape", "out of domain (w.shape): ML-DSA-65 public key", 373],
        ["ood", "c.not_genesis", "out of domain (c.not_genesis)", 137],
        ["ood", "e.secp", "out of domain (e.secp): SECP256K1 delegate signature verification", 36],
        ["ood", "c.segment", "out of domain (c.segment)", 3],
    )
    for fam, viol, reason, count in plan:
        for i in range(count):
            d = os.path.join(root, fam, f"case-{fam}-{viol}-{i:05d}")
            dirs.append(d)
            metas[d] = meta(expected_rel=True, in_d3=False, violations=[viol], family=fam)
            got[d] = row(d, "out_of_domain", reason)
    return dirs, metas, got


class PartitionAccounting(unittest.TestCase):
    """The 2,548-case population and its exhaustive partition."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dirs, self.metas, self.got = build_population(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def test_population_shape_matches_the_real_corpora(self):
        self.assertEqual(len(self.dirs), 2548)
        fams = {}
        for d in self.dirs:
            fams[os.path.basename(os.path.dirname(d))] = fams.get(
                os.path.basename(os.path.dirname(d)), 0) + 1
        self.assertEqual(fams, {"ood": 2269, "mutants": 279})

    def test_every_exclusion_is_asserted_and_partitioned_once(self):
        stats, bad, partition, records = d3.compare("lean", self.dirs, self.metas, self.got)
        self.assertEqual(bad, [], "licensed exclusions must not be reported as disagreements")
        self.assertEqual(dict(partition), {"domain_exclusion_asserted": 2548})
        self.assertEqual(sum(partition.values()), len(self.dirs))
        self.assertEqual(len(records), len(self.dirs))
        self.assertEqual({r["classification"] for r in records}, {"domain_exclusion_asserted"})
        self.assertTrue(all(r["exclusion_asserted"] is True for r in records))
        self.assertTrue(all(r["verdict_compared"] is False for r in records))

    def test_the_1259_are_the_ones_that_used_to_be_skipped(self):
        """The 1,259 = 2,269 ood-family exclusions minus the 1,010 with an e.g_alpha mark."""
        skipped_before = [
            d for d in self.dirs
            if os.path.basename(os.path.dirname(d)) == "ood"
            and "e.g_alpha" not in (self.metas[d]["d3_violations"] or [])
        ]
        self.assertEqual(len(skipped_before), 1259)
        _, _, partition, records = d3.compare("lean", self.dirs, self.metas, self.got)
        asserted = [r for r in records if r["classification"] == "domain_exclusion_asserted"]
        self.assertEqual(len(asserted), 2548)
        # Every one of the 1,259 now carries an asserted classification and a licensed code.
        for r in asserted:
            if os.path.basename(os.path.dirname(r["case"])) == "ood":
                self.assertTrue(r["exclusion_asserted"])
                self.assertTrue(r["exclusion_codes"])

    def test_undefined_verdict_is_partitioned_and_fails(self):
        """A verdict outside the contract is a failure, not a silent bucket."""
        dirs = list(self.dirs[:3])
        metas = {d: self.metas[d] for d in dirs}
        got = {d: dict(self.got[d]) for d in dirs}
        got[dirs[0]]["verdict"] = "maybe"
        _, bad, partition, records = d3.compare("lean", dirs, metas, got)
        self.assertEqual(sum(partition.values()), len(dirs))
        self.assertEqual(partition["malformed_verdict"], 1)
        self.assertEqual(len(bad), 1)
        self.assertEqual(len(records), len(dirs))

    def test_dropped_verdict_line_is_a_missing_output_failure(self):
        """A dropped line is its own bucket and a failure, so the invariant still holds."""
        dirs = list(self.dirs[:3])
        metas = {d: self.metas[d] for d in dirs}
        got = {d: dict(self.got[d]) for d in dirs}
        del got[dirs[0]]
        _, bad, partition, records = d3.compare("lean", dirs, metas, got)
        self.assertEqual(partition["missing_output"], 1)
        self.assertEqual(sum(partition.values()), len(dirs))
        self.assertEqual(len(bad), 1)
        self.assertEqual(sum(1 for r in records if r["classification"] == "missing_output"), 1)


class ControlledBreakage(unittest.TestCase):
    """Deliberate wrongness must still fail the appropriate gate."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dirs, self.metas, self.got = build_population(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def compare(self, mutate):
        got = {d: dict(r) for d, r in self.got.items()}
        mutate(got)
        return d3.compare("lean", self.dirs, self.metas, got)

    def first(self, family):
        for d in self.dirs:
            if os.path.basename(os.path.dirname(d)) == family:
                return d
        raise AssertionError(f"no {family} case")

    def test_wrong_reject_verdict_fails(self):
        """A reject where nearcore accepts must be a disagreement."""
        target = self.first("mutants")
        self.metas[target] = meta(expected_rel=False, in_d3=True, violations=[])
        _, bad, partition, _ = self.compare(lambda g: g[target].update(verdict="accept"))
        self.assertEqual(partition["verdict_compared_disagree"], 1)
        self.assertEqual(len(bad), 1)

    def test_wrong_accept_verdict_fails(self):
        target = self.first("mutants")
        self.metas[target] = meta(expected_rel=True, in_d3=True, violations=[])
        _, bad, partition, _ = self.compare(lambda g: g[target].update(verdict="reject"))
        self.assertEqual(partition["verdict_compared_disagree"], 1)
        self.assertEqual(len(bad), 1)

    def test_unasserted_exclusion_reason_fails(self):
        """out_of_domain whose reason the oracle does not license must fail."""
        target = self.first("ood")
        _, bad, partition, records = self.compare(
            lambda g: g[target].update(reason="out of domain (made.up): invented reason"))
        self.assertEqual(partition["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)
        row0 = next(r for r in records if r["case"] == target)
        self.assertFalse(row0["exclusion_asserted"])
        self.assertEqual(row0["classification"], "domain_exclusion_unasserted")

    def test_exclusion_with_no_reason_fails(self):
        target = self.first("ood")
        _, bad, partition, _ = self.compare(
            lambda g: g[target].update(reason=""))
        self.assertEqual(partition["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)

    def test_missing_output_fails(self):
        target = self.first("ood")
        _, bad, partition, _ = self.compare(lambda g: g.pop(target))
        self.assertEqual(partition["missing_output"], 1)
        self.assertEqual(len(bad), 1)

    def test_exclusion_on_in_domain_case_fails(self):
        """Refusing a case the relation under test includes is a domain error."""
        target = self.first("mutants")
        self.metas[target] = meta(expected_rel=True, in_d3=True, violations=[])
        _, bad, partition, _ = self.compare(
            lambda g: g[target].update(verdict="out_of_domain",
                                       reason="out of domain (c.not_genesis)"))
        self.assertEqual(partition["domain_exclusion_where_in_domain"], 1)
        self.assertEqual(len(bad), 1)

    def test_accept_above_g_alpha_fails(self):
        target = self.first("ood")
        # first ood case in the population carries e.g_alpha
        self.assertIn("e.g_alpha", self.metas[target]["d3_violations"])
        _, bad, partition, _ = self.compare(lambda g: g[target].update(verdict="accept", reason=""))
        self.assertEqual(partition["accept_above_g_alpha"], 1)
        self.assertEqual(len(bad), 1)

    def test_missing_code_cache_exclusion_fails(self):
        target = self.first("mutants")
        _, bad, partition, _ = self.compare(
            lambda g: g[target].update(verdict="accept", reason=""))
        self.assertEqual(partition["missing_code_cache_exclusion"], 1)
        self.assertEqual(len(bad), 1)

    def test_wrong_reason_for_a_code_cache_case_fails(self):
        """A code-cache case whose exclusion reason omits the cache condition is not licensed."""
        target = self.first("mutants")
        _, bad, partition, _ = self.compare(
            lambda g: g[target].update(reason="out of domain (c.not_genesis)"))
        self.assertEqual(partition["missing_code_cache_exclusion"], 1)
        self.assertEqual(len(bad), 1)

    def widened(self, mutate):
        got = {d: dict(r) for d, r in self.got.items()}
        mutate(got)
        return d3.compare("lean", self.dirs, self.metas, got, domain="successor",
                          widen=("e.code_cache",))

    def test_widened_code_cache_compares_verdict(self):
        """With `e.code_cache` widened, a decided cache case is compared against nearcore."""
        target = self.first("mutants")
        self.assertEqual(self.metas[target]["d3_violations"], ["e.code_cache"])
        near = "accept" if self.metas[target]["expected_rel"] else "reject"
        wrong = "reject" if near == "accept" else "accept"
        _, bad, partition, _ = self.widened(lambda g: g[target].update(verdict=near, reason=""))
        self.assertEqual(partition["missing_code_cache_exclusion"], 0)
        self.assertNotIn(target, [b[0] for b in bad])
        _, bad, partition, _ = self.widened(lambda g: g[target].update(verdict=wrong, reason=""))
        self.assertIn(target, [b[0] for b in bad])

    def test_widened_code_cache_keeps_cache_exclusion(self):
        """A rolled-back deploy may still report the cache exclusion when widened."""
        target = self.first("mutants")
        _, bad, _, records = self.widened(lambda g: None)
        self.assertNotIn(target, [b[0] for b in bad])
        row = next(r for r in records if r["case"] == target)
        self.assertEqual(row["classification"], "domain_exclusion_asserted")


class TimeoutIsAFailure(unittest.TestCase):
    """A hung checker shard must fail the run, not silently shorten the population."""

    def test_shard_timeout_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = os.path.join(tmp, "case")
            os.makedirs(case)
            # A checker that sleeps well past the deadline.
            sleeper = os.path.join(tmp, "sleeper.py")
            with open(sleeper, "w") as f:
                f.write("import sys, time\ntime.sleep(60)\n")
            saved = d3.PY
            try:
                d3.PY = sleeper
                with self.assertRaises(d3.CheckerTimeout):
                    d3.run_checker("python", [case], 1, tmp, timeout=0.5)
            finally:
                d3.PY = saved

    def test_timeout_message_names_the_shard(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = os.path.join(tmp, "case")
            os.makedirs(case)
            sleeper = os.path.join(tmp, "sleeper.py")
            with open(sleeper, "w") as f:
                f.write("import time\ntime.sleep(60)\n")
            saved = d3.PY
            try:
                d3.PY = sleeper
                with self.assertRaises(d3.CheckerTimeout) as ctx:
                    d3.run_checker("python", [case], 1, tmp, timeout=0.5)
                self.assertIn("shard 0", str(ctx.exception))
                self.assertIn("1 cases", str(ctx.exception))
            finally:
                d3.PY = saved


class DomainSeparation(unittest.TestCase):
    """Baseline and successor expectations must not be conflated."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = self.tmp.name
        self.dirs, self.metas, self.got = [], {}, {}
        # A case the baseline excludes for e.float and a plain in-domain accept.
        for i in range(4):
            d = os.path.join(root, "ood", f"float-{i}")
            self.dirs.append(d)
            self.metas[d] = meta(expected_rel=True, in_d3=False, violations=["e.float"])
            self.got[d] = row(d, "out_of_domain",
                              "out of domain (e.wasm-\u03b1): float type or operator in a function body")
        for i in range(3):
            d = os.path.join(root, "d3", f"plain-{i}")
            self.dirs.append(d)
            self.metas[d] = meta(expected_rel=True, in_d3=True, violations=[])
            self.got[d] = row(d, "accept")

    def tearDown(self):
        self.tmp.cleanup()

    def test_baseline_excludes_floats(self):
        _, bad, partition, records = d3.compare("lean", self.dirs, self.metas, self.got)
        self.assertEqual(bad, [])
        self.assertEqual(partition["domain_exclusion_asserted"], 4)
        self.assertEqual(partition["verdict_compared_agree"], 3)
        self.assertEqual({r["expectation_domain"] for r in records}, {"baseline"})

    def test_successor_widening_requires_verdicts_for_float_cases(self):
        """With e.float widened, the successor must decide those cases, not exclude them."""
        # The checker still excludes: that is now an in-domain exclusion -> failure.
        _, bad, partition, records = d3.compare(
            "lean", self.dirs, self.metas, self.got, domain="successor", widen=["e.float"])
        self.assertEqual(partition["domain_exclusion_where_in_domain"], 4)
        self.assertEqual(len(bad), 4)
        self.assertEqual({r["expectation_domain"] for r in records}, {"successor"})

        # A successor that accepts them agrees with nearcore and passes.
        got = {d: dict(r) for d, r in self.got.items()}
        for d in self.dirs:
            if "float" in d:
                got[d] = row(d, "accept")
        _, bad, partition, records = d3.compare(
            "lean", self.dirs, self.metas, got, domain="successor", widen=["e.float"])
        self.assertEqual(bad, [])
        self.assertEqual(partition["verdict_compared_agree"], 7)
        self.assertEqual({r["expectation_domain"] for r in records}, {"successor"})


class EndToEnd(unittest.TestCase):
    """main(): exit status and machine-readable report, without running a checker."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.corpus = self.root / "corpus"
        self.dirs, self.metas, self.got = build_population(str(self.corpus))
        # Truncate to a small, fast population for an end-to-end run.
        self.dirs = self.dirs[:40]
        for d in self.dirs:
            Path(d).mkdir(parents=True, exist_ok=True)
            (Path(d) / "meta.json").write_text(json.dumps(self.metas[d]))
            (Path(d) / "claim.bin").write_bytes(b"")
            (Path(d) / "witness.bin").write_bytes(b"")
        self.lean_jsonl = self.root / "lean.jsonl"
        self.lean_jsonl.write_text("".join(json.dumps(self.got[d]) + "\n" for d in self.dirs))

    def tearDown(self):
        self.tmp.cleanup()

    def run_main(self, extra):
        report = self.root / "report.json"
        argv = [str(MODULE), str(self.corpus), "--lean-from", str(self.lean_jsonl),
                "--report", str(report)] + extra
        proc = subprocess.run([sys.executable] + argv, capture_output=True, text=True)
        return proc, report

    def test_licensed_exclusions_exit_zero_and_write_per_case_records(self):
        proc, report = self.run_main([])
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        doc = json.loads(report.read_text())
        self.assertEqual(doc["schema"], "near-d3-difftest-report-v1")
        self.assertEqual(doc["inputs"], len(self.dirs))
        self.assertEqual(doc["total_disagreements"], 0)
        self.assertEqual(sum(doc["checkers"]["lean"]["partition"].values()), len(self.dirs))
        self.assertEqual(len(doc["cases"]), len(self.dirs))
        for row0 in doc["cases"]:
            self.assertEqual(row0["classification"], "domain_exclusion_asserted")
            self.assertTrue(row0["exclusion_asserted"])
            self.assertEqual(row0["expectation_domain"], "baseline")
        self.assertIn("verdict", doc["observables"]["checked"])
        self.assertIn("gas_burnt", doc["observables"]["unavailable"])

    def test_wrong_checker_exits_nonzero(self):
        """The controlled-breakage control at the process boundary."""
        wrong = self.root / "wrong.jsonl"
        rows = []
        for d in self.dirs:
            r = dict(self.got[d])
            # Flip every exclusion into an unlicensed one; a real wrong checker cannot cite the oracle.
            if r["verdict"] == "out_of_domain":
                r["reason"] = "out of domain (e.wasm-\u03b1): whatever"
            rows.append(json.dumps(r))
        wrong.write_text("\n".join(rows) + "\n")
        report = self.root / "wrong-report.json"
        proc = subprocess.run(
            [sys.executable, str(MODULE), str(self.corpus), "--lean-from", str(wrong),
             "--report", str(report)], capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0, "an unlicensed exclusion must fail")
        doc = json.loads(report.read_text())
        self.assertEqual(doc["checkers"]["lean"]["partition"]["domain_exclusion_unasserted"], len(self.dirs))
        self.assertEqual(doc["total_disagreements"], len(self.dirs))

    def test_dropped_line_exits_nonzero(self):
        short = self.root / "short.jsonl"
        lines = self.lean_jsonl.read_text().splitlines()[:-1]
        short.write_text("\n".join(lines) + "\n")
        proc = subprocess.run(
            [sys.executable, str(MODULE), str(self.corpus), "--lean-from", str(short)],
            capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0, "a missing verdict line must fail")


@unittest.skipUnless(os.environ.get("NEAR_CORPORA_DIR"), "NEAR_CORPORA_DIR not set")
class RealCorpora(unittest.TestCase):
    """Re-derive the accounting from the pinned corpora when they are available.

    Runs the real compare() against saved Lean verdicts (--lean-from), so it needs the corpora and a
    complete saved JSONL in NEAR_CORPORA_DIR/../l7-saved or L7_D3_SAVED. It is skipped in CI; the
    local verification records its measured output in the lane log."""

    def test_real_population_partition(self):
        corpora = os.environ["NEAR_CORPORA_DIR"]
        saved = os.environ.get("L7_D3_SAVED")
        if not saved:
            self.skipTest("L7_D3_SAVED (saved lean.jsonl directory) not set")
        total = 0
        partition = {}
        for corpus in ("d3c7", "d3c8", "d3c9", "d3c10"):
            dirs = []
            for fam in ("d3", "mutants", "ood"):
                p = os.path.join(corpora, corpus, fam)
                if os.path.isdir(p):
                    dirs += [os.path.join(p, d) for d in sorted(os.listdir(p))]
            metas = {}
            for d in dirs:
                with open(os.path.join(d, "meta.json")) as f:
                    metas[d] = json.load(f)
            got = {}
            with open(os.path.join(saved, corpus, "lean.jsonl")) as f:
                for line in f:
                    j = json.loads(line)
                    got[j["case"]] = j
            _, bad, part, _ = d3.compare("lean", dirs, metas, got)
            self.assertEqual(bad, [], f"{corpus} has disagreements")
            self.assertEqual(sum(part.values()), len(dirs))
            total += len(dirs)
            for k, v in part.items():
                partition[k] = partition.get(k, 0) + v
        self.assertEqual(total, 115284)
        self.assertEqual(partition["domain_exclusion_asserted"], 2548)
        self.assertEqual(partition["verdict_compared_agree"] + partition["verdict_agree_outside_domain"],
                         115284 - 2548)


if __name__ == "__main__":
    unittest.main()
