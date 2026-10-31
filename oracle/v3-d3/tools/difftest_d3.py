#!/usr/bin/env python3
"""Full-runtime difftest of RuntimeD3: the Lean checker `nearspec-v3-check-d3` (checkD3) and, with
--python, the independent Python checker `oracle/tools/spec_check_v3_d2.py` vs nearcore's verdicts in
a D3 corpus (oracle/v3-d3; meta.json `expected_rel` = nearcore, `in_d3`).

  difftest_d3.py CORPUS [--sample N] [--shards K] [--only d3|mutants|ood] [--python] [--no-lean]
                        [--save DIR] [--lean-from FILE] [--python-from FILE]
                        [--report FILE] [--domain baseline|successor] [--widen CODE[,CODE...]]
                        [--timeout SECONDS] [--lean-out] [--d2]

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
  * `domain_exclusion_independently_asserted` — out_of_domain on an out-of-domain case whose reason
                                  the oracle's labels do not license (its classifier predates the
                                  restriction), but whose named predicate an independent Python decode
                                  of claim.bin / witness.bin establishes (`oracle/tools/
                                  independent_domain.py`, passed in as `independent`). Pass.
  * `domain_exclusion_unasserted` — out_of_domain whose reason is absent, unknown, or licensed neither
                                  by the oracle's `d3_violations` nor by the independent decode. A
                                  failure (no unconditional pass).
  * `race_exclusion_conservative` — the preparation-race exclusion on an in-domain
                                  `e.code_deploy_served` case where nearcore's own forced schedules
                                  show the same verdict at different failure points and the decode
                                  finds a deploy-served call: the checker excludes a case nearcore
                                  decides (a completeness gap, W08 §7). Not a verdict failure; always
                                  reported in its own bucket.
  * `accept_above_g_alpha_agree` — with `g_alpha_accepts_compared` (the signed tier, whose hand-over
                                  path has no G_α: `D3.checkD3_cases`), an accept above G_α that
                                  nearcore also accepts. Pass; one that nearcore rejects stays
                                  `accept_above_g_alpha`.
  * `domain_exclusion_where_in_domain` — out_of_domain on a case the relation under test includes.
                                  A failure.
  * `accept_above_g_alpha`      — accept on a case the oracle puts above G_α. A failure.
  * `missing_code_cache_exclusion` — the oracle marks `e.code_cache` and the checker does not report
                                  the compiled-contract-cache exclusion (the `code_cache` wording or,
                                  since W08, `e.code_prep_race`). A failure, unless the run
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
plain checker emits only `verdict` and `reason`, so by default the report declares the consensus
outputs unavailable rather than claiming them.

`--lean-out` runs the observable driver `nearspec-v3-check-d3-out` as the Lean leg. It prints the
same verdict/reason line as the plain checker *plus* the consensus outputs of an accepted case
(`stateRoot`, `outcomeRoot`, `gasBurnt`, `balanceBurnt`, `outgoingReceiptsRoot`, `proposals`,
`txRoot`, `encodedMerkleRoot`, `encodedLength`, `congestion`, `bwRequests`, `logs`, `receiptCount`,
`wasmGas`). For every accepted case this script independently decodes `claim.bin` with
`tools/d3/claim_outputs.py` (the same decoder `tools/d3/check_outputs.py` uses) and compares the
claim-comparable fields field by field. A disagreement — a mismatched field, an accepted case with
null outputs, a non-accepted case that emitted outputs, an undecodable claim — is a hard failure:
it increments `total_disagreements` and the run exits 1. `--d2` selects the D2 pipeline
(`nearspec-v3-check-d3-out --d2`, and the plain leg defaults to `nearspec-v3-check-d2` when
`--lean-out` is absent); it also selects the corpus's D2 metadata for the expected verdict
(`expected_rel_d2`, `in_d2`, `d2_violations`). Without `--lean-out` the run is unchanged: the plain
driver, the same comparison and the same report keys.

Checkers run as K parallel processes with file-based input lists and outputs (no pipes).
--save DIR keeps the per-case JSON lines (lean.jsonl, python.jsonl); --lean-from / --python-from reuse
such a file instead of running that checker."""
import collections
import importlib.util
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("D3_CHECK", os.path.join(HERE, "../../wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3"))
# The observable driver (`--lean-out`): the same checker, printing the consensus outputs on acceptance.
LEAN_OUT = os.environ.get(
    "D3_CHECK_OUT", os.path.join(HERE, "../../wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out"))
# The plain D2 driver, used as the default Lean leg when `--d2` is given without `--lean-out`.
D2_CHECK = os.environ.get("D2_CHECK", os.path.join(HERE, "../../../spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2"))
PY = os.path.join(HERE, "../../tools/spec_check_v3_d3.py")
# The independent claim decoder. Shared with tools/d3/check_outputs.py; the wire format lives in one
# place so this script never re-implements it.
CLAIM_OUTPUTS = os.path.join(HERE, "../../../tools/d3/claim_outputs.py")

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
# D2's classifier names the WASM-action exclusion `e.wasm` (D3 relabels it `e.wasm-α`). Applied only in
# `--d2` mode so the default D3 licensing table is untouched; no D3 corpus case carries `e.wasm` in
# `d3_violations`, but the default path stays literally the same table.
D2_EXCLUSION_LICENSES = dict(EXCLUSION_LICENSES, **{"e.wasm": frozenset({"e.wasm"})})

# Observable fields a checker emits. The default driver (`nearspec-v3-check-d3`) prints only the verdict
# and reason; the observable driver (`nearspec-v3-check-d3-out`, `--lean-out`) additionally prints the
# consensus outputs of an accepted case. A consumer must not mistake verdict-level agreement for the full
# observable contract (workplan W01 criterion 4/5), so the unavailable list stays explicit and the report
# records which driver produced the lines.
OBSERVABLES_UNAVAILABLE = [
    "refunds", "return_data", "validator_rewards", "tx_results", "action_results",
]
# Emitted by `nearspec-v3-check-d3-out` for accepted cases: the endorsed header's consensus fields, which
# the signed checker proved equal to the values it computed (`NearSpecV3.accepted_observable_agrees`).
OBSERVABLES_EMITTED_BY_OUT_DRIVER = [
    "stateRoot", "outcomeRoot", "gasBurnt", "balanceBurnt", "outgoingReceiptsRoot",
    "proposals", "txRoot", "encodedMerkleRoot", "encodedLength", "congestion", "bwRequests",
    "logs", "receiptCount", "wasmGas",
]
# The subset of the out driver's fields that `claim.bin` also records, so an independent Python decode
# can check them. Mirrors `tools/d3/check_outputs.py`'s mapping (SCALAR_FIELDS + proposals); the wire
# format comes from `tools/d3/claim_outputs.py`, not from a second decoder here. The rest of the
# emitted fields (`congestion`, `bwRequests`, `logs`, `receiptCount`, `wasmGas`) are computed values the
# claim does not carry, so they stay explicitly un-compared by this script.
OBSERVABLES_COMPARED_VS_CLAIM = [
    "stateRoot", "outcomeRoot", "gasBurnt", "balanceBurnt", "outgoingReceiptsRoot",
    "proposals", "txRoot", "encodedMerkleRoot", "encodedLength",
]
OBSERVABLES_EMITTED_BUT_NOT_COMPARED = [
    "congestion", "bwRequests", "logs", "receiptCount", "wasmGas",
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


def run_checker(name, dirs, shards, td, timeout=None, exe=None, prefix=()):
    """Lean takes case dirs as arguments; Python takes --list FILE. Both print one JSON line per case.

    `timeout` (seconds, default D3_TIMEOUT or 0 = no limit) is a per-shard wall clock. A shard that
    exceeds it is killed and the run fails loudly: the workplan treats a timeout as a failure, so it
    must not turn into "fewer cases, still zero disagreements". `exe`/`prefix` override the Lean
    driver (the observable driver and its `--d2` mode); both default to the historical plain run."""
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
            cmd = [exe or LEAN] + list(prefix) + part
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


# Reason codes that are the compiled-contract-cache exclusion: the classifier family `code_cache`
# (the pre-W08 wording) and the W08 preparation race.
CODE_CACHE_REASONS = frozenset({"code_cache", "e.code_prep_race"})
# Partition buckets that are not failures. Every other bucket is a disagreement and is in `bad`.
# `race_exclusion_conservative` is a known completeness gap (step 5a), passed only under its
# independent conditions and always reported separately.
PASS_BUCKETS = ("domain_exclusion_asserted", "domain_exclusion_independently_asserted",
                "verdict_compared_agree", "verdict_agree_outside_domain", "accept_above_g_alpha_agree",
                "race_exclusion_conservative")


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


def exclusion_asserted(reason, violations, licenses=None):
    """True iff the reason cites at least one code the oracle's own classification licenses."""
    licenses = licenses or EXCLUSION_LICENSES
    codes = reason_codes(reason)
    licensed = set()
    for c in codes:
        licensed |= licenses.get(c, frozenset())
    return bool(licensed & set(violations)), codes


def schedule_failure_point_races(meta):
    """True iff the oracle's forced preparation schedules (`nearcore_schedule`: `eager`, `lazy`,
    each nearcore's own validator result) give the same verdict but different results, i.e. the
    failure point depends on the schedule while the verdict does not. Missing data is False."""
    s = meta.get("nearcore_schedule")
    if not isinstance(s, dict):
        return False
    eager, lazy = s.get("eager"), s.get("lazy")
    if not isinstance(eager, str) or not isinstance(lazy, str):
        return False
    return (eager == "ok") == (lazy == "ok") and eager != lazy


def compare(label, dirs, metas, got, domain="baseline", widen=(), licenses=None, independent=None,
            g_alpha_accepts_compared=False):
    """Classify every input exactly once.

    Returns (stats, bad, partition, records). `stats` keeps the historical per-(family,verdict,nearcore)
    histogram so existing log figures still map; `partition` is the exhaustive, mutually exclusive
    classification whose sum is asserted equal to len(dirs).

    `independent(case_dir, reason) -> {licensed, predicate, detail}` (oracle/tools/
    independent_domain.py) licenses an exclusion the oracle's labels do not, from a Python decode of
    the case; without it only the oracle's labels license. `g_alpha_accepts_compared` compares an
    accept above G_alpha with nearcore instead of failing it (step 3; the signed tier)."""
    stats = collections.Counter()
    partition = collections.Counter()
    bad = []
    records = []
    widen = frozenset(widen)
    licenses = licenses or EXCLUSION_LICENSES
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
        # Except where the relation under test decides above G_alpha. The signed tier does on its
        # hand-over path: `D3.checkD3_cases` (spec/lean/v3/NearSpecV3/D3/Signed.lean) proves
        # `checkD3` is the legacy core (which keeps G_alpha) unless the core errs and `handover`
        # fires, and then it is `signedRecorderCheck Wasm.pv86 none`, i.e. no gas cap (user decision
        # 2026-10-30). Such an accept is then legitimate iff nearcore accepts too: compared, never
        # passed unconditionally.
        if v == "accept" and "e.g_alpha" in viol and "e.g_alpha" not in widen and g_alpha_accepts_compared:
            agrees = near
            row.update(verdict_compared=True, verdict_agrees=agrees, exclusion_asserted=None,
                       in_domain_under_test=in_domain)
            if agrees:
                partition["accept_above_g_alpha_agree"] += 1
                row["classification"] = "accept_above_g_alpha_agree"
            else:
                partition["accept_above_g_alpha"] += 1
                row["classification"] = "accept_above_g_alpha"
                bad.append((d, f"G_α: {label} accept above G_α, nearcore rejects", reason,
                            m.get("nearcore")))
            records.append(row)
            continue
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
        # The cache exclusion is either the compiled-contract-cache wording (`code_cache`) or, since
        # W08 (docs/evidence/lean-chunk-completion/w08-warm-cache), the preparation race
        # `out of domain (e.code_prep_race)`. On the pre-W08 corpora the oracle's race label is
        # `e.code_cache`; on the successor generator's corpora it is `e.code_prep_race` (step 5,
        # through the licence table). `e.code_deploy_served` never licenses the race (step 5a).
        codes = reason_codes(reason)
        cache_reason = bool(codes & CODE_CACHE_REASONS)
        if "e.code_cache" in viol and "e.code_cache" in widen and v == "out_of_domain" \
                and cache_reason and not (set(viol) - widen):
            partition["domain_exclusion_asserted"] += 1
            stats[("domain_exclusion", "asserted", label)] += 1
            row.update(classification="domain_exclusion_asserted", verdict_compared=False,
                       verdict_agrees=None, exclusion_codes=sorted(codes), exclusion_asserted=True)
            records.append(row)
            continue
        if "e.code_cache" in viol and "e.code_cache" not in widen \
                and not (v == "out_of_domain" and cache_reason):
            partition["missing_code_cache_exclusion"] += 1
            bad.append((d, f"code cache: oracle True, {label} {v}", reason, m.get("nearcore")))
            row.update(classification="missing_code_cache_exclusion", verdict_compared=v != "out_of_domain",
                       verdict_agrees=False, exclusion_codes=sorted(codes))
            records.append(row)
            continue
        # ---- 5. domain exclusions need an asserted, licensed reason ---------------
        if v == "out_of_domain":
            ok, codes = exclusion_asserted(reason, remaining, licenses)
            row.update(exclusion_codes=sorted(codes), exclusion_asserted=ok)
            # ---- 5a. a conservative race exclusion on a deterministic deploy-served case ------
            # `e.code_deploy_served` is in domain (nearcore's verdict is the same under both forced
            # preparation schedules), so the race exclusion there is a checker-vs-oracle domain
            # disagreement: the checker excludes a case nearcore decides. It is not unexplained only
            # when nearcore itself shows the schedule dependence the checker stops at: the oracle's
            # forced eager and lazy runs (`nearcore_schedule`, oracle/v3-successor/src/cachejudge.rs)
            # give the same verdict at different failure points (W08 §4: the `code.none` mutants
            # whose failing call races while the verdict does not), and the independent decode finds
            # a call whose code only an earlier in-chunk deploy serves. Counted in its own bucket and
            # listed as a known completeness gap, never as an agreement.
            if in_domain and "e.code_prep_race" in codes and "e.code_deploy_served" in viol:
                sched = schedule_failure_point_races(m)
                ind = independent(d, reason) if independent is not None else None
                row.update(nearcore_schedule_failure_point_races=sched, independent=ind)
                if sched and ind is not None and ind.get("licensed"):
                    partition["race_exclusion_conservative"] += 1
                    row.update(classification="race_exclusion_conservative", verdict_compared=False,
                               verdict_agrees=None)
                    records.append(row)
                    continue
            if in_domain:
                partition["domain_exclusion_where_in_domain"] += 1
                row["classification"] = "domain_exclusion_where_in_domain"
                bad.append((d, f"{label} out_of_domain on an in-domain case ({domain})", reason,
                            m.get("nearcore")))
            elif not ok and independent is not None and \
                    (ind := independent(d, reason)) is not None and ind.get("licensed"):
                # ---- 5b. licensed by an independent decode of the case (oracle/tools/
                # independent_domain.py): the corpus oracle predates the restriction, so the
                # predicate the reason names is computed from claim.bin / witness.bin in Python.
                partition["domain_exclusion_independently_asserted"] += 1
                row.update(classification="domain_exclusion_independently_asserted", independent=ind)
                stats[("domain_exclusion", "independently_asserted", label)] += 1
            elif not ok:
                if independent is not None:
                    row["independent"] = independent(d, reason)
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


_CLAIM_MOD = None


def claim_module():
    """Load `tools/d3/claim_outputs.py` once. Imported lazily so the default run pays nothing."""
    global _CLAIM_MOD
    if _CLAIM_MOD is None:
        spec = importlib.util.spec_from_file_location("d3_claim_outputs", CLAIM_OUTPUTS)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load claim decoder at {CLAIM_OUTPUTS}")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _CLAIM_MOD = mod
    return _CLAIM_MOD


def independent_outputs(claim_path):
    """Decode `claim.bin` in Python and return the fields the out driver also emits.

    Mirrors `tools/d3/check_outputs.py`'s `independent_outputs` (its `SCALAR_FIELDS` plus
    `proposals`), but decodes with `tools/d3/claim_outputs.py` so this script never re-implements
    the wire format. The returned keys are the driver's keys, so a comparison is mechanical."""
    mod = claim_module()
    with open(claim_path, "rb") as f:
        claim = f.read()
    c = mod.decode_claim(claim)
    ci = mod.decode_chunk_inner(c["chunk_inner"])
    return {
        "stateRoot": ci["prev_state_root"].hex(),
        "outcomeRoot": ci["prev_outcome_root"].hex(),
        "gasBurnt": ci["prev_gas_used"],
        "balanceBurnt": ci["prev_balance_burnt"],
        "outgoingReceiptsRoot": ci["prev_outgoing_receipts_root"].hex(),
        "proposals": [p.hex() for p in ci["proposals"]],
        "txRoot": ci["tx_root"].hex(),
        "encodedMerkleRoot": ci["encoded_merkle_root"].hex(),
        "encodedLength": ci["encoded_length"],
    }


# Buckets that are hard failures. `observable_missing_line` is counted in the partition but not here:
# the verdict comparison already owns a case with no line at all (`missing_output`), and counting it
# twice would double `total_disagreements`.
OBSERVABLE_FAILURE_BUCKETS = (
    "accepted_null_outputs", "accepted_missing_outputs",
    "nonaccepted_with_outputs", "claim_decode_error", "accepted_observables_disagree",
)


def compare_observables(dirs, got):
    """Compare the out driver's emitted observables against an independent decode of `claim.bin`.

    Every accepted case must carry outputs and every field in `OBSERVABLES_COMPARED_VS_CLAIM` must
    equal the claim's value; a non-accepted case must carry `outputs: null`. A mismatch, a null or
    missing output on an accepted case, outputs on a non-accepted case, or an undecodable claim is a
    hard failure — never a note. A case with no line at all is owned by the verdict comparison
    (`missing_output`) and only counted here so the denominator is complete.

    Returns `(summary, bad, per_field, by_case, failures)`."""
    summary = collections.Counter()
    per_field = collections.Counter()
    bad = []
    by_case = {}
    for d in dirs:
        j = got.get(d)
        row = {"observable_compared": False}
        if j is None or "verdict" not in j:
            summary["observable_missing_line"] += 1
            row["observable_classification"] = "observable_missing_line"
            by_case[d] = row
            continue
        v = j.get("verdict")
        if v not in VERDICTS:
            summary["observable_skipped_malformed"] += 1
            row["observable_classification"] = "observable_skipped_malformed"
            by_case[d] = row
            continue
        outs = j.get("outputs")
        if v != "accept":
            if outs is not None:
                summary["nonaccepted_with_outputs"] += 1
                row.update(observable_compared=True, observable_agrees=False,
                           observable_classification="nonaccepted_with_outputs")
                bad.append((d, f"out driver emitted outputs on a {v} case", j.get("reason") or "",
                            [{"field": "<outputs>", "emitted": outs, "claim": None}]))
            else:
                summary["nonaccepted_no_outputs"] += 1
                row["observable_classification"] = "nonaccepted_no_outputs"
            by_case[d] = row
            continue
        if "outputs" not in j:
            summary["accepted_missing_outputs"] += 1
            row.update(observable_compared=True, observable_agrees=False,
                       observable_classification="accepted_missing_outputs")
            bad.append((d, "accepted case has no `outputs` key (plain driver line?)", j.get("reason") or "",
                        [{"field": "<outputs>", "emitted": "missing", "claim": None}]))
            by_case[d] = row
            continue
        if outs is None:
            summary["accepted_null_outputs"] += 1
            row.update(observable_compared=True, observable_agrees=False,
                       observable_classification="accepted_null_outputs")
            bad.append((d, "accepted case has null outputs", j.get("reason") or "",
                        [{"field": "<outputs>", "emitted": None, "claim": None}]))
            by_case[d] = row
            continue
        try:
            ind = independent_outputs(os.path.join(d, "claim.bin"))
        except Exception as e:  # noqa: BLE001 - a decode failure is a failure, with its message
            summary["claim_decode_error"] += 1
            row.update(observable_compared=True, observable_agrees=False,
                       observable_classification="claim_decode_error")
            bad.append((d, f"claim decode failed: {e}", "",
                        [{"field": "<claim>", "emitted": None, "claim": str(e)}]))
            by_case[d] = row
            continue
        mismatches = []
        for f in OBSERVABLES_COMPARED_VS_CLAIM:
            if outs.get(f) != ind.get(f):
                per_field[f] += 1
                mismatches.append({"field": f, "emitted": outs.get(f), "claim": ind.get(f)})
        row.update(observable_compared=True, observable_agrees=not mismatches,
                   observable_fields_compared=len(OBSERVABLES_COMPARED_VS_CLAIM))
        if mismatches:
            summary["accepted_observables_disagree"] += 1
            row["observable_classification"] = "accepted_observables_disagree"
            row["observable_mismatches"] = mismatches[:20]
            fields = sorted({x["field"] for x in mismatches})
            bad.append((d, f"observables disagree on {len(mismatches)} field(s) {fields}",
                        j.get("reason") or "", mismatches[:20]))
        else:
            summary["accepted_observables_agree"] += 1
            row["observable_classification"] = "accepted_observables_agree"
        by_case[d] = row
    failures = sum(summary[k] for k in OBSERVABLE_FAILURE_BUCKETS)
    return summary, bad, per_field, by_case, failures


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
    use_out = "--lean-out" in sys.argv
    d2 = "--d2" in sys.argv
    timeout = float(arg("--timeout", "0") or 0)
    if domain not in ("baseline", "successor"):
        sys.exit(f"--domain must be baseline or successor, not {domain!r}")
    if domain == "baseline" and widen:
        sys.exit("--widen requires --domain successor")
    if d2 and domain == "successor":
        sys.exit("--d2 selects the D2 relation and its metadata; --domain successor is a D3 mode")
    if d2 and not use_lean:
        sys.exit("--d2 needs the Lean leg; drop --no-lean or drop --d2")
    if use_out and not use_lean:
        sys.exit("--lean-out needs the Lean leg; drop --no-lean or drop --lean-out")
    if d2 and use_py:
        # The Python leg this script knows is `spec_check_v3_d3.py`, the D3 checker. Running it over
        # D2 metadata would compare a D3 relation against D2 expectations and report the mismatch as
        # a disagreement. Refuse instead of producing a false number; `oracle/tools/difftest_v3_d2.py`
        # is the D2 Python difftest.
        sys.exit("--d2 cannot be combined with --python here: this script's Python leg is the D3 "
                 "checker (spec_check_v3_d3.py); use oracle/tools/difftest_v3_d2.py for D2")
    families = ("d2", "mutants", "ood") if d2 else ("d3", "mutants", "ood")
    dirs = []
    for fam in families:
        if only and fam != only:
            continue
        p = os.path.join(corpus, fam)
        if os.path.isdir(p):
            dirs += [os.path.join(p, d) for d in sorted(os.listdir(p))]
    if sample and sample < len(dirs):
        random.Random(1).shuffle(dirs)
        dirs = sorted(dirs[:sample])
    metas = {d: json.load(open(os.path.join(d, "meta.json"))) for d in dirs}
    # In --d2 mode the expected verdict and the domain classification come from the D2 oracle's own
    # fields. The D3 fields are absent in a D2 corpus, so `compare()` would classify every honest
    # case as outside the domain; the view below keeps `compare()` unchanged and feeds it D2 metadata.
    if d2:
        metas = {d: {
            "expected_rel": bool(m.get("expected_rel_d2", m.get("expected_rel"))),
            "expected_rel_d3": bool(m.get("expected_rel_d2", m.get("expected_rel"))),
            "in_d3": bool(m.get("in_d2", False)),
            "d3_violations": list(m.get("d2_violations") or []),
            "nearcore": m.get("nearcore"),
            "features": m.get("features") or {},
        } for d, m in metas.items()}
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
                # --lean-out runs the observable driver as the Lean leg: its line is the plain driver's
                # verdict/reason plus the accepted case's outputs. --d2 selects the D2 pipeline for
                # both drivers. With neither flag this is the historical call, byte for byte.
                if use_out:
                    results["lean"] = run_checker("lean", dirs, shards, td, timeout=timeout,
                                                  exe=LEAN_OUT, prefix=("--d2",) if d2 else ())
                elif d2:
                    results["lean"] = run_checker("lean", dirs, shards, td, timeout=timeout, exe=D2_CHECK)
                else:
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
    licenses = D2_EXCLUSION_LICENSES if d2 else EXCLUSION_LICENSES
    total_bad = 0
    per_checker = {}
    all_records = []
    observable_result = None
    # Set once the Lean leg's lines have been shown to carry the out driver's `outputs` key. It is
    # checked again after the loop: a --lean-out run whose report lacks an observable comparison would
    # be a silent downgrade to a verdict-only run, exactly the failure mode this flag exists to remove.
    observable_checked = False
    for name, got in results.items():
        stats, bad, partition, records = compare(name, dirs, metas, got, domain=domain, widen=widen,
                                                 licenses=licenses)
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
        # Only when the lines really carry outputs. The out driver's non-accepted lines carry
        # `outputs: null`, so "any line has the key" detects its output. A --lean-from file saved from
        # the plain driver has no such key: the comparison cannot be made, and silently skipping it
        # would report an observable check that never happened. That is a failure, not a pass.
        has_outputs = any("outputs" in j for j in got.values())
        if name == "lean" and use_out and got and not has_outputs:
            print("FAIL: --lean-out needs lines produced by the output driver; the saved Lean lines "
                  "have no `outputs` key (plain-driver save). Re-run without --lean-from or save the "
                  "lines from a --lean-out run.", file=sys.stderr)
            if report:
                with open(report, "w") as f:
                    json.dump({"schema": "near-d3-difftest-report-v1",
                               "corpus": os.path.abspath(corpus), "domain": domain,
                               "widen": sorted(widen), "inputs": len(dirs),
                               "failure": "missing_observables",
                               "detail": "--lean-from lines carry no outputs key",
                               "checkers": {}, "total_disagreements": None, "cases": []},
                              f, indent=1, sort_keys=True)
                    f.write("\n")
            sys.exit(1)
        if name == "lean" and use_out and got and has_outputs:
            summary, obs_bad, per_field, by_case, obs_failures = compare_observables(dirs, got)
            observable_checked = True
            observable_result = {
                "driver": LEAN_OUT,
                "driver_mode": "d2" if d2 else "d3",
                "compared_vs_claim": list(OBSERVABLES_COMPARED_VS_CLAIM),
                "emitted_but_not_compared": list(OBSERVABLES_EMITTED_BUT_NOT_COMPARED),
                "partition": dict(sorted(summary.items())),
                "field_mismatches": dict(sorted(per_field.items())),
                "total_failures": obs_failures,
                "failures": [
                    {"case": d, "problem": p, "reason": r, "mismatches": mm}
                    for d, p, r, mm in obs_bad[:200]
                ],
            }
            print("==== lean observables vs independent claim decode")
            print("lean-observables: partition "
                  + json.dumps(dict(sorted(summary.items())), sort_keys=True))
            print(f"lean-observables: cases={len(dirs)} field_mismatches={sum(per_field.values())} "
                  f"failures={obs_failures}")
            for b in obs_bad[:20]:
                print("OBSERVABLES DISAGREE", b[0], b[1], sep="\n  ")
                for mm in (b[3] or [])[:3]:
                    print(f"  field={mm['field']} emitted={mm['emitted']!r} claim={mm['claim']!r}")
            total_bad += obs_failures
            per_checker["lean"]["observables"] = {
                "driver": LEAN_OUT,
                "driver_mode": "d2" if d2 else "d3",
                "cases": len(dirs),
                "failures": obs_failures,
                "partition": dict(sorted(summary.items())),
                "field_mismatches": dict(sorted(per_field.items())),
            }
            # Attach the per-case observable verdict to the Lean row so a consumer can see both.
            for row in records:
                row.update(by_case.get(row["case"], {}))
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
    # Invariant: --lean-out either produced an observable comparison or the run failed above. A report
    # that claims the flag was used while carrying no comparison would be a silent downgrade.
    if use_out and use_lean and not observable_checked and "lean" in results:
        print("FAIL: --lean-out was requested but no observable comparison ran; the Lean lines carry "
              "no `outputs` key. Refusing to write a verdict-only report.", file=sys.stderr)
        sys.exit(1)
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
                "emitted_by_out_driver": OBSERVABLES_EMITTED_BY_OUT_DRIVER,
                "note": "the out driver's outputs are the endorsed header's fields; the signed checker "
                        "proved they equal the computed transition values on acceptance. Per-field "
                        "agreement against an independent claim decode is measured by "
                        "tools/d3/check_outputs.py, not by this verdict-level script.",
                "oracle_meta_fields": ["expected_rel", "expected_rel_d3", "in_d3", "d3_violations",
                                       "features", "action_results", "tx_results", "receipt_classes"],
            },
            "cases": all_records,
        }
        if observable_result is not None:
            # Additive only: the key appears when --lean-out produced the Lean lines. The "observables"
            # block's pre-existing keys keep their meaning; "checked" gains the compared field names and
            # "note" changes because the claim comparison now happens in this script.
            doc["observables"]["checked"] = OBSERVABLES_CHECKED + list(OBSERVABLES_COMPARED_VS_CLAIM)
            doc["observables"]["compared_vs_claim"] = list(OBSERVABLES_COMPARED_VS_CLAIM)
            doc["observables"]["emitted_but_not_compared"] = list(OBSERVABLES_EMITTED_BUT_NOT_COMPARED)
            doc["observables"]["note"] = (
                "the out driver's outputs are the computed transition values on acceptance; the "
                "signed checker proved they equal the endorsed header's fields "
                "(NearSpecV3.accepted_observable_agrees). This run compared them field by field "
                "against an independent decode of claim.bin (tools/d3/claim_outputs.py); a "
                "disagreement is a hard failure counted in total_disagreements. The remaining "
                "emitted fields carry computed values the claim does not record and are listed as "
                "emitted_but_not_compared; the unavailable fields are not emitted at all.")
            doc["observable_comparison"] = observable_result
        with open(report, "w") as f:
            json.dump(doc, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"wrote report {report} ({len(all_records)} per-case records)")
    sys.exit(1 if total_bad else 0)


if __name__ == "__main__":
    main()
