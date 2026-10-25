#!/usr/bin/env python3
"""Full-runtime difftest of RuntimeD3: the Lean checker `nearspec-v3-check-d3` (checkD3) and, with
--python, the independent Python checker `oracle/tools/spec_check_v3_d2.py` vs nearcore's verdicts in
a D3 corpus (oracle/v3-d3; meta.json `expected_rel` = nearcore, `in_d3`).

  difftest_d3.py CORPUS [--sample N] [--shards K] [--only d3|mutants|ood] [--python] [--no-lean]
                        [--save DIR] [--lean-from FILE] [--python-from FILE]
                        [--report FILE] [--domain baseline|successor] [--widen CODE[,CODE...]]
                        [--timeout SECONDS]

Comparison contract
-------------------
Every input case is classified into exactly one partition bucket (the sum of the buckets is asserted
to equal the input count; a mismatch raises rather than printing a partial report). A case is a
disagreement only when its own bucket says so:

  * `missing_output`            — the checker produced no verdict line. A failure, never an exclusion.
  * `malformed_verdict`         — a verdict outside {accept, reject, out_of_domain}. A failure.
  * `domain_exclusion_asserted` — the checker says out_of_domain and its reason cites a domain code
                                  the oracle independently marks in `d3_violations` for that case.
                                  This is the only form of exclusion that passes.
  * `domain_exclusion_unasserted` — out_of_domain whose reason is absent, unknown, or not licensed by
                                  the oracle's `d3_violations`. A failure (no unconditional pass).
  * `domain_exclusion_where_in_domain` — out_of_domain on a case the relation under test includes.
                                  A failure.
  * `accept_above_g_alpha`      — accept on a case the oracle puts above G_α. A failure.
  * `missing_code_cache_exclusion` — the oracle marks `e.code_cache` and the checker does not report
                                  the compiled-contract-cache exclusion. A failure, unless the run
                                  widens `e.code_cache`: then the verdict is compared with nearcore
                                  and the cache exclusion remains admissible (rolled-back deploys).
  * `verdict_compared_agree`    — accept/reject matches nearcore and the case is in domain. Pass.
  * `verdict_compared_disagree` — accept/reject differs from nearcore. A failure.
  * `verdict_agree_outside_domain` — accept/reject matches nearcore on a case the oracle classifies
                                  outside the domain. The documented acceptance quotient: nearcore
                                  agrees, the oracle's D3α classifier does not. Classified per case and
                                  reported; not a verdict failure (see docs/logs/lean-chunk-L7-2026-10-23.md
                                  §4.4 and §4.4b).

Domain expectations are kept separate. `--domain baseline` (the default, and what `checkD3` is) expects
an exclusion exactly on the oracle's out-of-domain cases. `--domain successor --widen CODE` moves the
cases whose violations are a subset of CODE into the successor's domain and expects a nearcore-matching
accept/reject there. Baseline and successor runs write their domain name into every per-case record, so
the two expectation sets are never conflated.

`--report FILE` writes a machine-readable report: the partition, per-case verdicts/reasons, the
oracle's independently computed classification, and the observable fields actually compared. The
checker currently emits only `verdict` and `reason`; gas, refunds, logs and roots are not emitted and
are listed as unavailable rather than claimed.

Checkers run as K parallel processes with file-based input lists and outputs (no pipes).
--save DIR keeps the per-case JSON lines (lean.jsonl, python.jsonl); --lean-from / --python-from reuse
such a file instead of running that checker."""
import collections
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("D3_CHECK", os.path.join(HERE, "../../wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3"))
PY = os.path.join(HERE, "../../tools/spec_check_v3_d3.py")

VERDICTS = ("accept", "reject", "out_of_domain")

# Codes a checker may cite as its domain-exclusion reason, and the oracle `d3_violations` codes that
# license each one. `w.shape` licensing `e.mldsa_key` is the documented relabel in oracle/v3-d3/src/d3.rs
# (the oracle classifies the ML-DSA key action as `e.mldsa_key`, "the checkers report `w.shape`").
# A code absent from this table cannot license an exclusion; that is a failure, not a pass.
EXCLUSION_LICENSES = {
    "c.not_genesis": frozenset({"c.not_genesis"}),
    "c.segment": frozenset({"c.segment"}),
    "c.no_resharding": frozenset({"c.no_resharding"}),
    "c.single_epoch": frozenset({"c.single_epoch"}),
    "c.no_split_gate": frozenset({"c.no_split_gate"}),
    "w.shape": frozenset({"w.shape", "e.mldsa_key"}),
    "e.secp": frozenset({"e.secp"}),
    "e.wasm-\u03b1": frozenset({"e.ood_host", "e.float", "e.eth_implicit_local", "e.wasm-\u03b1"}),
    "g_alpha": frozenset({"e.g_alpha"}),
    "code_cache": frozenset({"e.code_cache"}),
}

# Observable fields the current checker does not emit. Listed in the report so a consumer cannot
# mistake verdict-level agreement for the full observable contract (workplan W01 criterion 4/5).
OBSERVABLES_UNAVAILABLE = [
    "gas_burnt", "gas_used", "refunds", "logs", "return_data", "emitted_receipts",
    "state_root", "outcome_root", "validator_rewards", "tx_results", "action_results",
]
OBSERVABLES_CHECKED = ["verdict", "domain_exclusion_reason"]


class CheckerTimeout(RuntimeError):
    """A checker shard exceeded the deadline. A timeout is a failure, never an exclusion."""


def parse_results(lines, dirs):
    expected = set(dirs)
    if not expected or len(expected) != len(dirs):
        raise ValueError("empty or duplicate checker inputs")
    got = {}
    for line in lines:
        row = json.loads(line)
        if not isinstance(row, dict) or row.get("case") not in expected:
            raise ValueError("foreign/malformed checker output")
        case = row["case"]
        if case in got:
            raise ValueError(f"duplicate checker output: {case}")
        if row.get("verdict") not in VERDICTS or not isinstance(row.get("reason"), str):
            raise ValueError(f"malformed checker verdict: {case}")
        got[case] = row
    if set(got) != expected:
        raise ValueError(f"missing {len(expected - set(got))} checker results")
    return got


def run_checker(name, dirs, shards, td, timeout=None):
    """Lean takes case dirs as arguments; Python takes --list FILE. Both print one JSON line per case.

    `timeout` (seconds, default D3_TIMEOUT or 0 = no limit) is a per-shard wall clock. A shard that
    exceeds it is killed and the run fails loudly: the workplan treats a timeout as a failure, so it
    must not turn into "fewer cases, still zero disagreements"."""
    timeout = timeout if timeout is not None else float(os.environ.get("D3_TIMEOUT", "0") or 0)
    if shards <= 0 or not dirs or len(set(dirs)) != len(dirs):
        raise ValueError("shards and input population must be nonempty and unique")
    procs = []
    for s in range(shards):
        part = dirs[s::shards]
        if not part:
            continue
        lst = os.path.join(td, f"{name}-in{s}")
        with open(lst, "w") as f:
            f.write("\n".join(part) + "\n")
        out = open(os.path.join(td, f"{name}-out{s}"), "w")
        err = open(os.path.join(td, f"{name}-err{s}"), "w")
        if name == "lean":
            cmd = [LEAN] + part
        else:
            cmd = [sys.executable, PY, "--list", lst]
        procs.append((s, part, subprocess.Popen(cmd, stdout=out, stderr=err,
                                                stdin=subprocess.DEVNULL), out, err))
    timed_out = []
    for s, part, p, out, err in procs:
        try:
            p.wait(timeout=timeout or None)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()
            timed_out.append((s, len(part)))
        out.close()
        err.close()
    if timed_out:
        detail = ", ".join(f"shard {s} ({n} cases)" for s, n in timed_out)
        raise CheckerTimeout(f"{name} checker exceeded {timeout}s on {detail}")
    got = {}
    for s, part, p, _, _ in procs:
        if p.returncode != 0:
            raise subprocess.CalledProcessError(p.returncode, p.args)
        with open(os.path.join(td, f"{name}-out{s}")) as f:
            got.update(parse_results(f, part))
    return got


def boundary(reason):
    r = reason or ""
    if "code_cache" in r or "compiled-contract cache" in r:
        return "code_cache"
    if "g_alpha" in r or "gAlpha" in r or "G_\u03b1" in r or "e_alpha" in r:
        return "g_alpha"
    return None


def reason_codes(reason):
    """Every domain-exclusion code a checker's reason text asserts.

    Two sources: the classifier family (`boundary`, which also recognises the compiled-contract-cache
    wording) and the parenthesised code in `out of domain (CODE): ...`. Returning all of them lets a
    checker whose reason ordering differs from the oracle's violation ordering still be licensed by
    the violation it does cite, without permitting a code the oracle never marks."""
    r = reason or ""
    codes = set()
    b = boundary(r)
    if b is not None:
        codes.add(b)
    prefix = "out of domain ("
    if r.startswith(prefix):
        close = r.find(")", len(prefix))
        if close > len(prefix):
            codes.add(r[len(prefix):close])
    return frozenset(codes)


def exclusion_asserted(reason, violations):
    """True iff the reason cites at least one code the oracle's own classification licenses."""
    codes = reason_codes(reason)
    licensed = set()
    for c in codes:
        licensed |= EXCLUSION_LICENSES.get(c, frozenset())
    return bool(licensed & set(violations)), codes


def compare(label, dirs, metas, got, domain="baseline", widen=()):
    """Classify every input exactly once.

    Returns (stats, bad, partition, records). `stats` keeps the historical per-(family,verdict,nearcore)
    histogram so existing log figures still map; `partition` is the exhaustive, mutually exclusive
    classification whose sum is asserted equal to len(dirs)."""
    stats = collections.Counter()
    partition = collections.Counter()
    bad = []
    records = []
    widen = frozenset(widen)
    for d in dirs:
        m = metas[d]
        fam = os.path.basename(os.path.dirname(d))
        near = bool(m.get("expected_rel"))
        rel_d3 = bool(m.get("expected_rel_d3")) if m.get("expected_rel_d3") is not None else None
        viol = list(m.get("d3_violations") or [])
        ind3 = bool(m.get("in_d3", m.get("expected_rel_d3") is not None and not viol))
        row = {
            "case": d,
            "family": fam,
            "checker": label,
            "expectation_domain": domain,
            "expected_rel": near,
            "expected_rel_d3": rel_d3,
            "in_d3": ind3,
            "d3_violations": viol,
        }
        raw = got.get(d)
        # ---- 1. output presence -------------------------------------------------
        if raw is None or "verdict" not in raw:
            partition["missing_output"] += 1
            bad.append((d, f"{label} produced no verdict line", "", m.get("nearcore")))
            row.update(verdict=None, reason=None, classification="missing_output",
                       verdict_compared=False, verdict_agrees=None, exclusion_asserted=None)
            records.append(row)
            continue
        v = raw["verdict"]
        reason = raw.get("reason", "") or ""
        row.update(verdict=v, reason=reason)
        stats[(fam, v, "nearcore_ok" if near else "nearcore_rej")] += 1
        # ---- 2. verdict domain --------------------------------------------------
        if v not in VERDICTS:
            partition["malformed_verdict"] += 1
            bad.append((d, f"{label} verdict {v!r} is not one of {VERDICTS}", reason, m.get("nearcore")))
            row.update(classification="malformed_verdict", verdict_compared=False, verdict_agrees=None,
                       exclusion_asserted=None)
            records.append(row)
            continue
        # The relation under test: baseline = the oracle's D3α; successor = D3α plus the explicitly
        # widened exclusion families. Baseline and successor rows carry different expectation_domain.
        widened = set(viol) & widen
        remaining = set(viol) - widen
        in_domain = ind3 or (bool(widened) and not remaining)
        row["in_domain_under_test"] = in_domain
        # ---- 3. a checker must never accept a case above G_alpha -----------------
        if v == "accept" and "e.g_alpha" in viol and "e.g_alpha" not in widen:
            partition["accept_above_g_alpha"] += 1
            bad.append((d, f"G_\u03b1: oracle True, {label} accept", reason,
                        m.get("features", {}).get("fc_gas_burnt_for_function_call")))
            row.update(classification="accept_above_g_alpha", verdict_compared=True, verdict_agrees=False,
                       exclusion_asserted=None)
            records.append(row)
            continue
        # ---- 4. a code-cache case needs the cache exclusion ----------------------
        # A successor that widens `e.code_cache` resolves in-chunk deploys through the deploy
        # tracker, so such a case is compared against nearcore; only a rolled-back deploy may still
        # carry the cache exclusion, which then counts as asserted.
        codes = reason_codes(reason)
        if "e.code_cache" in viol and "e.code_cache" in widen and v == "out_of_domain" \
                and "code_cache" in codes and not (set(viol) - widen):
            partition["domain_exclusion_asserted"] += 1
            stats[("domain_exclusion", "asserted", label)] += 1
            row.update(classification="domain_exclusion_asserted", verdict_compared=False,
                       verdict_agrees=None, exclusion_codes=sorted(codes), exclusion_asserted=True)
            records.append(row)
            continue
        if "e.code_cache" in viol and "e.code_cache" not in widen \
                and not (v == "out_of_domain" and "code_cache" in codes):
            partition["missing_code_cache_exclusion"] += 1
            bad.append((d, f"code cache: oracle True, {label} {v}", reason, m.get("nearcore")))
            row.update(classification="missing_code_cache_exclusion", verdict_compared=v != "out_of_domain",
                       verdict_agrees=False, exclusion_codes=sorted(codes))
            records.append(row)
            continue
        # ---- 5. domain exclusions need an asserted, licensed reason ---------------
        if v == "out_of_domain":
            ok, codes = exclusion_asserted(reason, remaining)
            row.update(exclusion_codes=sorted(codes), exclusion_asserted=ok)
            if in_domain:
                partition["domain_exclusion_where_in_domain"] += 1
                row["classification"] = "domain_exclusion_where_in_domain"
                bad.append((d, f"{label} out_of_domain on an in-domain case ({domain})", reason,
                            m.get("nearcore")))
            elif not ok:
                partition["domain_exclusion_unasserted"] += 1
                row["classification"] = "domain_exclusion_unasserted"
                bad.append((d, f"{label} out_of_domain without an oracle-asserted reason: {sorted(codes)}",
                            reason, m.get("nearcore")))
            else:
                partition["domain_exclusion_asserted"] += 1
                row["classification"] = "domain_exclusion_asserted"
                stats[("domain_exclusion", "asserted", label)] += 1
            row.update(verdict_compared=False, verdict_agrees=None)
            records.append(row)
            continue
        # ---- 6. the accept/reject verdict comparison ----------------------------
        expected = "accept" if near else "reject"
        agrees = v == expected
        row.update(verdict_compared=True, verdict_agrees=agrees, exclusion_asserted=None)
        if not agrees:
            partition["verdict_compared_disagree"] += 1
            row["classification"] = "verdict_compared_disagree"
            bad.append((d, f"{label} {v} vs nearcore {near}", reason, m.get("nearcore")))
        elif not in_domain:
            # The documented acceptance quotient: the verdict matches nearcore on a case the oracle's
            # D3a classifier places outside the domain. Explicitly classified, never an unconditional
            # pass; kept as a verdict agreement because nearcore itself agrees.
            partition["verdict_agree_outside_domain"] += 1
            row["classification"] = "verdict_agree_outside_domain"
            stats[(f"ood_decided_by_{label}", v, str(near))] += 1
        else:
            partition["verdict_compared_agree"] += 1
            row["classification"] = "verdict_compared_agree"
        records.append(row)
    # ---- invariant: the partition must cover every input exactly once ----------
    covered = sum(partition.values())
    if covered != len(dirs):
        raise ValueError(
            f"{label}: partition covers {covered} of {len(dirs)} inputs; "
            f"buckets={dict(partition)}")
    return stats, bad, partition, records


def main():
    corpus = sys.argv[1]
    arg = lambda n, d: sys.argv[sys.argv.index(n) + 1] if n in sys.argv else d  # noqa: E731
    sample = int(arg("--sample", "0"))
    shards = int(arg("--shards", "8"))
    only = arg("--only", "")
    save = arg("--save", "")
    report = arg("--report", "")
    domain = arg("--domain", "baseline")
    widen = [w for w in arg("--widen", "").split(",") if w]
    use_py = "--python" in sys.argv
    use_lean = "--no-lean" not in sys.argv
    timeout = float(arg("--timeout", "0") or 0)
    if domain not in ("baseline", "successor"):
        sys.exit(f"--domain must be baseline or successor, not {domain!r}")
    if domain == "baseline" and widen:
        sys.exit("--widen requires --domain successor")
    dirs = []
    for fam in ("d3", "mutants", "ood"):
        if only and fam != only:
            continue
        p = os.path.join(corpus, fam)
        if os.path.isdir(p):
            dirs += [os.path.join(p, d) for d in sorted(os.listdir(p))]
    if sample and sample < len(dirs):
        random.Random(1).shuffle(dirs)
        dirs = sorted(dirs[:sample])
    metas = {d: json.load(open(os.path.join(d, "meta.json"))) for d in dirs}
    if not dirs:
        sys.exit("FAIL: no corpus inputs")
    if not use_lean and not use_py and not arg("--lean-from", "") and not arg("--python-from", ""):
        sys.exit("FAIL: no checker selected")
    results = {}
    def load(fn):
        with open(fn) as f:
            return parse_results(f, dirs)
    lean_from, py_from = arg("--lean-from", ""), arg("--python-from", "")
    timed_out = None
    with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as td:
        try:
            if lean_from:
                results["lean"] = load(lean_from)
            elif use_lean:
                results["lean"] = run_checker("lean", dirs, shards, td, timeout=timeout)
            if py_from:
                results["python"] = load(py_from)
            elif use_py:
                # shuffle so that expensive cases spread over the shards
                pd = list(dirs)
                random.Random(7).shuffle(pd)
                results["python"] = run_checker("python", pd, shards, td, timeout=timeout)
        except CheckerTimeout as e:
            timed_out = str(e)
            print(f"FAIL: {timed_out}", file=sys.stderr)
            if report:
                # A timeout is a failure, not a partial comparison. Record it and stop; never
                # emit a partition for a population the checker did not finish.
                with open(report, "w") as f:
                    json.dump({"schema": "near-d3-difftest-report-v1",
                               "corpus": os.path.abspath(corpus), "domain": domain,
                               "widen": sorted(widen), "inputs": len(dirs),
                               "failure": "timeout", "detail": timed_out,
                               "checkers": {}, "total_disagreements": None,
                               "cases": []}, f, indent=1, sort_keys=True)
                    f.write("\n")
                print(f"wrote failure report {report}")
            sys.exit(1)
    if save:
        os.makedirs(save, exist_ok=True)
        for name, got in results.items():
            with open(os.path.join(save, f"{name}.jsonl"), "w") as f:
                for d in dirs:
                    if d in got:
                        f.write(json.dumps(got[d]) + "\n")
    total_bad = 0
    per_checker = {}
    all_records = []
    for name, got in results.items():
        stats, bad, partition, records = compare(name, dirs, metas, got, domain=domain, widen=widen)
        print(f"==== {name} vs nearcore (domain={domain})")
        for k, c in sorted(stats.items(), key=str):
            print(k, c)
        print(f"{name}: cases={len(dirs)} disagreements_with_nearcore={len(bad)}")
        print(f"{name}: partition " + json.dumps(dict(sorted(partition.items())), sort_keys=True))
        for b in bad[:20]:
            print("DISAGREE", *b, sep="\n  ")
        total_bad += len(bad)
        per_checker[name] = {
            "cases": len(dirs),
            "disagreements": len(bad),
            "partition": dict(sorted(partition.items())),
        }
        all_records.extend(records)
    if "lean" in results and "python" in results:
        L, P = results["lean"], results["python"]
        pairs = collections.Counter()
        diff = []
        for d in dirs:
            lv = L.get(d, {}).get("verdict", "missing")
            pv = P.get(d, {}).get("verdict", "missing")
            pairs[(lv, pv)] += 1
            if lv != pv:
                diff.append((d, lv, pv, L.get(d, {}).get("reason"), P.get(d, {}).get("reason")))
        print("==== lean vs python")
        for k, c in sorted(pairs.items()):
            print(f"lean={k[0]} python={k[1]}: {c}")
        print(f"lean-vs-python: cases={len(dirs)} disagreements={len(diff)}")
        for x in diff[:20]:
            print("LEAN\u2260PY", x[0], f"lean={x[1]} ({x[3]})", f"python={x[2]} ({x[4]})", sep="\n  ")
        total_bad += len(diff)
        per_checker["lean-vs-python"] = {"cases": len(dirs), "disagreements": len(diff)}
    if report:
        doc = {
            "schema": "near-d3-difftest-report-v1",
            "corpus": os.path.abspath(corpus),
            "domain": domain,
            "widen": sorted(widen),
            "inputs": len(dirs),
            "checkers": per_checker,
            "total_disagreements": total_bad,
            "observables": {
                "checked": OBSERVABLES_CHECKED,
                "unavailable": OBSERVABLES_UNAVAILABLE,
                "oracle_meta_fields": ["expected_rel", "expected_rel_d3", "in_d3", "d3_violations",
                                       "features", "action_results", "tx_results", "receipt_classes"],
            },
            "cases": all_records,
        }
        with open(report, "w") as f:
            json.dump(doc, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"wrote report {report} ({len(all_records)} per-case records)")
    sys.exit(1 if total_bad else 0)


if __name__ == "__main__":
    main()
