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
        # The unavailable list names what no driver emits. The default run's plain driver emits only
        # verdict+reason, so the consensus outputs stay unavailable and the claim-comparable subset
        # stays out of `checked`. (This assertion used to demand "gas_burnt" here, which no version of
        # the script ever listed — the base commit's test was red before this change.)
        self.assertIn("refunds", doc["observables"]["unavailable"])
        self.assertIn("tx_results", doc["observables"]["unavailable"])
        self.assertNotIn("stateRoot", doc["observables"]["checked"])
        self.assertNotIn("gasBurnt", doc["observables"]["unavailable"])
        # Additive report key: absent without --lean-out.
        self.assertNotIn("observable_comparison", doc)

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


# ---- Gate-B freeze rules (2026-10-31) ------------------------------------------------------------
_rspec = importlib.util.spec_from_file_location("replay_successor_under_test",
                                                REPO / "tools/d3/replay_successor.py")
replay = importlib.util.module_from_spec(_rspec)
_rspec.loader.exec_module(replay)

RACE = ("out of domain (e.code_prep_race): contract preparation pipelined before the in-chunk "
        "deploy that serves its code")
CODE = ("e.code_cache", "e.code_deploy_served")
SCHED_RACES = {"eager": "validate: StorageError(MissingTrieValue(... hash: A))",
               "lazy": "validate: StorageError(MissingTrieValue(... hash: B))"}


def stub(licensed, calls=None):
    """An independent classifier that answers `licensed` and records what it was asked."""
    def f(case, reason):
        if calls is not None:
            calls.append((case, reason))
        return {"licensed": licensed, "predicate": "stub", "detail": "stub"}
    return f


def one(m, verdict, reason="", **kw):
    """Compare a single case; returns (bad, partition, record)."""
    kw.setdefault("licenses", replay.licenses(d3))
    _, bad, part, recs = d3.compare("t", ["c"], {"c": m}, {"c": row("c", verdict, reason)}, **kw)
    assert sum(part.values()) == 1
    return bad, part, recs[0]


def successor(m, verdict, reason="", **kw):
    return one(m, verdict, reason, domain="successor", widen=CODE, **kw)


class RaceExclusion(unittest.TestCase):
    """Rule 1: `out of domain (e.code_prep_race)` is the cache exclusion, licensed only by a race
    label: `e.code_cache` on the pre-W08 corpora, `e.code_prep_race` on the successor corpora."""

    def test_race_reason_on_old_code_cache_label_is_asserted(self):
        bad, part, rec = successor(meta(False, violations=["e.code_cache"], family="mutants"),
                                   "out_of_domain", RACE)
        self.assertEqual(bad, [])
        self.assertEqual(rec["classification"], "domain_exclusion_asserted")

    def test_race_reason_on_new_race_label_is_asserted(self):
        bad, _, rec = successor(meta(False, violations=["e.code_prep_race"]), "out_of_domain", RACE)
        self.assertEqual(bad, [])
        self.assertEqual(rec["classification"], "domain_exclusion_asserted")

    def test_race_reason_on_unwidened_code_cache_is_the_cache_exclusion(self):
        bad, part, _ = one(meta(False, violations=["e.code_cache"]), "out_of_domain", RACE)
        self.assertEqual(bad, [])
        self.assertEqual(part["missing_code_cache_exclusion"], 0)

    def test_other_reason_on_code_cache_case_still_fails(self):
        for reason in ("out of domain (e.wasm-α): float type or operator in a function body",
                       "out of domain (e.code_prep_racy): typo", ""):
            with self.subTest(reason=reason):
                bad, part, _ = successor(meta(False, violations=["e.code_cache"]), "out_of_domain", reason)
                self.assertEqual(part["domain_exclusion_where_in_domain"], 1)
                self.assertEqual(len(bad), 1)

    def test_race_reason_with_another_unlicensed_violation_fails(self):
        bad, part, _ = successor(meta(False, violations=["e.code_cache", "e.secp"]), "out_of_domain", RACE)
        self.assertEqual(part["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)

    def test_deploy_served_label_does_not_license_the_race_reason(self):
        self.assertNotIn("e.code_deploy_served", replay.licenses(d3)["e.code_prep_race"])
        bad, part, _ = one(meta(False, violations=["e.code_deploy_served"]), "out_of_domain", RACE)
        self.assertEqual(part["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)

    def test_race_reason_on_unlabelled_case_without_independent_fails(self):
        bad, part, _ = successor(meta(True, violations=["w.shape"]), "out_of_domain", RACE)
        self.assertEqual(part["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)


class DeployServedRace(unittest.TestCase):
    """Rule 1 (W08's conservative exclusions): the race exclusion on an in-domain
    `e.code_deploy_served` case passes only as `race_exclusion_conservative`, and only when nearcore's
    forced schedules give one verdict at two failure points and the decode finds a deploy-served call."""

    def m(self, sched=SCHED_RACES):
        return meta(False, violations=["e.code_deploy_served"], nearcore_schedule=sched)

    def test_failure_point_race_with_independent_decode_is_conservative(self):
        bad, part, rec = successor(self.m(), "out_of_domain", RACE, independent=stub(True))
        self.assertEqual(bad, [])
        self.assertEqual(rec["classification"], "race_exclusion_conservative")
        self.assertTrue(rec["nearcore_schedule_failure_point_races"])
        self.assertIn("race_exclusion_conservative", d3.PASS_BUCKETS)

    def test_deterministic_schedules_fail(self):
        same = {"eager": SCHED_RACES["eager"], "lazy": SCHED_RACES["eager"]}
        for sched in (same, None, {"eager": "ok"}, {"eager": "ok", "lazy": SCHED_RACES["lazy"]},
                      {"eager": "ok", "lazy": "ok"}):
            with self.subTest(sched=sched):
                bad, part, _ = successor(self.m(sched), "out_of_domain", RACE, independent=stub(True))
                self.assertEqual(part["domain_exclusion_where_in_domain"], 1)
                self.assertEqual(len(bad), 1)

    def test_without_independent_decode_fails(self):
        for ind in (None, stub(False)):
            bad, part, _ = successor(self.m(), "out_of_domain", RACE, independent=ind)
            self.assertEqual(part["domain_exclusion_where_in_domain"], 1)
            self.assertEqual(len(bad), 1)

    def test_other_reason_on_deploy_served_fails(self):
        bad, part, _ = successor(self.m(), "out_of_domain", "out of domain (code_cache)",
                                 independent=stub(True))
        self.assertEqual(part["domain_exclusion_where_in_domain"], 1)
        self.assertEqual(len(bad), 1)

    def test_deploy_served_label_alone_never_licenses_the_race(self):
        """`e.code_deploy_served` is compared, not excluded: a decided verdict is still compared."""
        bad, part, _ = successor(self.m(), "reject", independent=stub(True))
        self.assertEqual(part["verdict_compared_agree"], 1)
        bad, part, _ = successor(self.m(), "accept", independent=stub(True))
        self.assertEqual(part["verdict_compared_disagree"], 1)

    def test_schedule_failure_point_races(self):
        self.assertTrue(d3.schedule_failure_point_races({"nearcore_schedule": SCHED_RACES}))
        self.assertFalse(d3.schedule_failure_point_races({}))
        self.assertFalse(d3.schedule_failure_point_races({"nearcore_schedule": {"eager": "ok", "lazy": "x"}}))


class IndependentLicence(unittest.TestCase):
    """Rule 2: an exclusion the oracle does not label passes only when the independent decode
    establishes the named predicate, and only on a case outside the domain under test."""

    def test_licensed_by_independent_decode(self):
        calls = []
        bad, part, rec = one(meta(True, violations=[]), "out_of_domain",
                             "out of domain (c.not_genesis)", independent=stub(True, calls))
        self.assertEqual(bad, [])
        self.assertEqual(rec["classification"], "domain_exclusion_independently_asserted")
        self.assertEqual(calls, [("c", "out of domain (c.not_genesis)")])

    def test_not_licensed_by_independent_decode_fails(self):
        bad, part, rec = one(meta(True, violations=[]), "out_of_domain",
                             "out of domain (c.not_genesis)", independent=stub(False))
        self.assertEqual(part["domain_exclusion_unasserted"], 1)
        self.assertEqual(len(bad), 1)
        self.assertFalse(rec["independent"]["licensed"])

    def test_independent_never_overrides_an_in_domain_case(self):
        calls = []
        bad, part, _ = one(meta(True, in_d3=True, violations=[]), "out_of_domain",
                           "out of domain (c.not_genesis)", independent=stub(True, calls))
        self.assertEqual(part["domain_exclusion_where_in_domain"], 1)
        self.assertEqual(len(bad), 1)
        self.assertEqual(calls, [])

    def test_independent_not_consulted_when_oracle_licenses(self):
        calls = []
        bad, _, rec = one(meta(True, violations=["c.not_genesis"]), "out_of_domain",
                          "out of domain (c.not_genesis)", independent=stub(False, calls))
        self.assertEqual(bad, [])
        self.assertEqual(rec["classification"], "domain_exclusion_asserted")
        self.assertEqual(calls, [])

    def test_real_classifier_on_committed_cases(self):
        """The harness's own classifier, on committed fixtures with an empty `d3_violations`."""
        ind = replay.load_independent()
        ev = REPO / "docs/evidence/lean-chunk-completion"
        mldsa = str(ev / "key-family-fixtures/cases/00-h10098-s0")
        secp = str(ev / "key-family-fixtures/cases/00-h10007-s3")
        m = meta(True, violations=[])
        for case, reason, want in (
                (mldsa, "out of domain (w.shape): ML-DSA-65 public key", "domain_exclusion_independently_asserted"),
                (secp, "out of domain (w.shape): non-ED25519 transaction key", "domain_exclusion_independently_asserted"),
                # wrong reason for the case: the predicate does not hold
                (mldsa, "out of domain (w.shape): non-ED25519 transaction key", "domain_exclusion_unasserted"),
                (secp, "out of domain (w.shape): ML-DSA-65 public key", "domain_exclusion_unasserted"),
                (secp, "out of domain (c.not_genesis)", "domain_exclusion_unasserted")):
            with self.subTest(case=case, reason=reason):
                _, bad, part, recs = d3.compare("signed", [case], {case: m}, {case: row(case, "out_of_domain", reason)},
                                                licenses=replay.licenses(d3), independent=ind.classifier("signed"))
                self.assertEqual(recs[0]["classification"], want)
                self.assertEqual(bool(bad), want == "domain_exclusion_unasserted")


class SignedGAlpha(unittest.TestCase):
    """Rule 3: the signed tier's hand-over path has no G_alpha (`D3.checkD3_cases`), so an accept
    above G_alpha is compared with nearcore; without the flag it still fails."""

    def test_agreeing_accept_passes(self):
        for viol in (["e.g_alpha"], ["w.size", "e.g_alpha"]):
            bad, part, rec = one(meta(True, violations=viol), "accept", g_alpha_accepts_compared=True)
            self.assertEqual(bad, [])
            self.assertEqual(rec["classification"], "accept_above_g_alpha_agree")
            self.assertTrue(rec["verdict_agrees"])

    def test_disagreeing_accept_fails(self):
        bad, part, rec = one(meta(False, violations=["e.g_alpha"]), "accept", g_alpha_accepts_compared=True)
        self.assertEqual(part["accept_above_g_alpha"], 1)
        self.assertEqual(len(bad), 1)
        self.assertFalse(rec["verdict_agrees"])

    def test_without_the_flag_accept_above_g_alpha_still_fails(self):
        bad, part, _ = one(meta(True, violations=["e.g_alpha"]), "accept")
        self.assertEqual(part["accept_above_g_alpha"], 1)
        self.assertEqual(len(bad), 1)

    def test_replay_sets_the_flag_only_on_the_signed_tier(self):
        m = {"c": meta(True, violations=["e.g_alpha"])}
        got = {"c": row("c", "accept")}
        _, bad, part, _ = replay.compare_tier(d3, "signed", m, got)
        self.assertEqual((bad, dict(part)), ([], {"accept_above_g_alpha_agree": 1}))
        _, bad, part, _ = replay.compare_tier(d3, "genesis", m, got)
        self.assertEqual(part["accept_above_g_alpha"], 1)
        self.assertEqual(len(bad), 1)


class Rescore(unittest.TestCase):
    """`replay_successor.py --rescore`: re-compares stored verdicts, bound to the inputs' hashes."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.case = root / "cases" / "c0"
        self.case.mkdir(parents=True)
        (self.case / "claim.bin").write_bytes(b"claim")
        (self.case / "witness.bin").write_bytes(b"witness")
        (self.case / "meta.json").write_text(json.dumps(meta(True, violations=["e.g_alpha"])))
        self.run = root / "run"
        self.run.mkdir()
        res = self.run / "results.jsonl"
        res.write_text(json.dumps({"case": str(self.case), "verdict": "accept", "reason": "",
                                   "tier": "signed"}) + "\n")
        inputs = [{"case": str(self.case), "files": {n: replay.sha256(self.case / n)
                                                      for n in ("claim.bin", "witness.bin", "meta.json")}}]
        self.report = {"status": "fail", "package": {"tier": "signed", "sha256": "x", "binary": "b"},
                       "inputs": inputs, "output_sha256": replay.sha256(res),
                       "partition": {"accept_above_g_alpha": 1},
                       "comparisons": [{"case": str(self.case), "classification": "accept_above_g_alpha"}]}
        (self.run / "report.json").write_text(json.dumps(self.report))
        self.out = root / "out"

    def tearDown(self):
        self.tmp.cleanup()

    def test_rescore_writes_a_new_report_with_the_reclassification(self):
        rep = replay.rescore(self.run, self.out)
        self.assertEqual(rep["status"], "pass")
        self.assertEqual(rep["reclassification"],
                         [{"before": "accept_above_g_alpha", "after": "accept_above_g_alpha_agree", "rows": 1}])
        self.assertEqual(json.loads((self.run / "report.json").read_text())["status"], "fail")
        self.assertEqual(json.loads((self.out / "report.json").read_text())["mode"], "rescore")

    def test_rescore_refuses_a_changed_input(self):
        (self.case / "witness.bin").write_bytes(b"other")
        with self.assertRaises(ValueError):
            replay.rescore(self.run, self.out)

    def test_rescore_refuses_tampered_results(self):
        (self.run / "results.jsonl").write_text(json.dumps({"case": str(self.case), "verdict": "reject",
                                                            "reason": "", "tier": "signed"}) + "\n")
        with self.assertRaises(ValueError):
            replay.rescore(self.run, self.out)

    def test_rescore_refuses_a_run_without_verdicts(self):
        (self.run / "results.jsonl").unlink()
        with self.assertRaises(ValueError):
            replay.rescore(self.run, self.out)

    def test_rescore_never_overwrites_the_run(self):
        with self.assertRaises(ValueError):
            replay.rescore(self.run, self.run)

    def test_rescore_still_fails_a_real_disagreement(self):
        (self.case / "meta.json").write_text(json.dumps(meta(False, violations=["e.g_alpha"])))
        self.report["inputs"][0]["files"]["meta.json"] = replay.sha256(self.case / "meta.json")
        (self.run / "report.json").write_text(json.dumps(self.report))
        rep = replay.rescore(self.run, self.out)
        self.assertEqual(rep["status"], "fail")
        self.assertEqual(rep["partition"], {"accept_above_g_alpha": 1})


if __name__ == "__main__":
    unittest.main()
