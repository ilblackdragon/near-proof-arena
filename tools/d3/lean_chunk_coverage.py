#!/usr/bin/env python3
"""Build the Lean chunk-transition coverage inventory (plan §4 L0).

This is research/accounting tooling. It reconciles the *pinned* nearcore surface
(action tags and host imports read from git objects, never a dirty checkout)
against the Lean specification's actual dispatch tables, and emits one row per
boundary item with the fields the plan requires:

    id, family, nearcore_commit, nearcore_path_symbol, lean_path_symbol, status,
    domain_guard, evidence, owner, dependencies, acceptance_tests, remaining_work

Statuses are limited to the plan's vocabulary: implemented, partial, missing,
impossible-at-boundary, validated. They describe the **canonical Gate-B relation**, the
successor tier `allFeatures` (`Successor/Config.lean` `Tier.cfg .allFeatures`, checker
`nearspec-v3-check-successor --tier allFeatures`). What the signed statement of record
(`D3.checkD3`/`RelD3`, `--tier signed`) or its legacy core (`D3.checkD3Core`) still excludes
is recorded in `domain_guard`/`remaining_work`, always naming the tier, and is a stated
signed-tier restriction rather than a Gate-B gap.

Promotion rules (plan §4 L0; workplan "Rules for remaining work"):

* `implemented`: Lean has a dispatch arm / decided path for the item on `allFeatures`.
  Nothing more is claimed: not "this behaviour was tested against nearcore".
* `validated`: implemented, plus whole-chunk fixtures judged by pinned nearcore run cold,
  plus a deliberate-breakage control showing those fixtures detect a bug in that semantics.
  The evidence is a `VALIDATION` entry below; every path it names must exist (the tool
  fails otherwise), so a promotion cannot outlive its evidence.
* Promotions are *derived*: the tool first checks the Lean surface (a successor decoder arm,
  an `allFeatures` flag, a named exclusion string, ...) and only then applies the evidence
  entry. If the surface disappears, the row falls back to `partial`/`missing`.
* `impossible-at-boundary`: a pinned-source reason why no relation can decide the input
  (nearcore nondeterminism, a transport limit, a trusted claim fact, a test-only feature),
  with the checked predicate or theorem where one exists.

Nothing here is a proof or a conformance test; the evidence fields cite where those are.

Exit status is 1 when the emitted inventory differs from the file given to
--check. Regenerate with --output after an intentional review.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

sys_path = Path(__file__).resolve().parent
import sys
if str(sys_path) not in sys.path:
    sys.path.insert(0, str(sys_path))

PIN = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
PV = 86
ACTION_MOD = "core/primitives/src/action/mod.rs"
VM = "runtime/near-vm-runner/src/"
LEAN_ROOT = "spec/lean/v3/NearSpecV3"

# Lean files whose dispatch tables define the "implemented" side.
LEAN_FILES = [
    "Wasm/Host.lean",
    "Wasm/Exec.lean",
    "Wasm/CryptoHost.lean",
    "Wasm/Decode.lean",
    "Wasm/Syntax.lean",
    # `noResharding` lives here since the parallel domain module was retired (UQ-010, 2026-10-29).
    "ReshardingD3.lean",
    "Wasm/Prepare.lean",
    "Wasm/InstanceLayout.lean",
    "D2/Types.lean",
    "D2/Actions.lean",
    # L2 (float domain): the kernel, its opcode dispatch, its guard switch and its successor
    # relation. Adding these makes the drift gate fail if the float surface moves without the
    # inventory being regenerated.
    "Wasm/Float.lean",
    "Wasm/FloatTests.lean",
    "ChallengeChunkV3Float.lean",
    # The canonical Gate-B relation: the `allFeatures` configuration, the successor action
    # decoder, the signed hand-over and the genesis-aware successor core. Their facts drive the
    # promotions below (`successor_facts`).
    "Successor/Config.lean",
    "Successor/GlobalCodecs.lean",
    "D3/Signed.lean",
    "GenesisD3.lean",
]

# Host families whose absence is a real semantic gap rather than a boundary exclusion.
CURVE_PREFIXES = ("alt_bn128_", "bls12381_", "ecrecover", "p256_verify")
TEST_FEATURES = ("sandbox_debug_log", "sleep_nanos", "burn_gas")

EV = "docs/evidence/lean-chunk-completion/"
W12 = EV + "tier-refinement-w12/README.md"

# --- Validation evidence registry ----------------------------------------------------------
# One entry per promoted family: `paths` must all exist (checked), `fixtures` are the
# whole-chunk nearcore-judged populations, `control` the deliberate-breakage control(s),
# `lean` the proofs/tests that back the Lean side. A row is `validated` only through an entry
# whose `fixtures` and `control` are both non-empty (`_validated`).
VALIDATION = {
    "curve-hosts": dict(
        paths=[EV + "curve-host-fixtures/README.md", EV + "cross-family-fixtures/README.md",
               EV + "remaining-shapes/README.md", EV + "open-uqs/README.md", W12],
        fixtures=("curve-host-fixtures: 149 steps calling all 14 hosts (pos/neg/edge inputs, "
                  "memory/register/out-of-bounds sources), seeds 4242 and 31337: 111/111 and 118/118 "
                  "verdicts agree with cold nearcore, blind 87/87 and 94/94; cross-family "
                  "curve-callbacks, 8 seeds (201-204, 211-214), 9,643 rows, 0 disagreements; "
                  "remaining-shapes curve-yield-timeout, 4 seeds (601-604), 1,500 rows, 0 disagreements"),
        control=("family-level: the pre-fix BLS Miller-loop checker rejects 2 honest chunks per run "
                 "(curve-host-fixtures replay/control-prefix-*); C2 BLS-writer element charge "
                 "(45/45 honest chunks flip); C-Y timed-out-yield callback result"),
        lean=("O2 proved: Lift.curveHosts, relSuccessor_storageResolution_curveHosts "
              "(Successor/TierO2.lean); UQ-004: 32/32 PV86 crypto costs and flags pinned"),
    ),
    "global-actions": dict(
        paths=[EV + "global-cache-fixtures/README.md", EV + "global-promise-fixtures/README.md",
               EV + "cross-family-fixtures/README.md", EV + "remaining-shapes/README.md",
               EV + "resharding-fixtures-2/README.md", W12],
        fixtures=("global-cache-fixtures, seeds 2718 and 31415: 978 honest chunks, 265 selected "
                  "cases agree on globalActions and completeCodeGlobal (deployments incl. "
                  "redeployment nonce, hash/account use+call, use+call rollback, state inits, "
                  "12 incoming distribution receipts per window); global-promise-fixtures "
                  "166/166; cross-family rollback-refund, 4 seeds (401-404); remaining-shapes "
                  "state-init-emit (4 seeds, 1,595 rows) and dist-identity (8 seeds, 1,027 rows); "
                  "resharding-fixtures-2 g61/g67 (deployments across a split)"),
        control=("C5 (a failed action keeps its emitted receipts: 4-7 honest composition chunks per "
                 "run flip), C-S (state init credits one extra yocto: 4 chunks flip), C-D1/C-D2 "
                 "(distribution proofs unchecked: 110 rejection reasons move, 35 rows stop rejecting)"),
        lean=("O3 proved under LayoutsWF (an admission fact, A1): Lift.globalActions_wf, "
              "relSuccessor_globalActions_allFeatures (Successor/TierO3*.lean); 12 pinned borsh "
              "codec probes (global-cache-fixtures/codec-vectors.json)"),
    ),
    "global-receivers": dict(
        paths=[EV + "global-cache-fixtures/README.md", EV + "cross-family-fixtures/README.md",
               EV + "w08-warm-cache/README.md"],
        fixtures=("global-cache-fixtures (seeds 2718, 31415): calls on hash- and account-identified "
                  "global contracts, success and rollback, both tiers; cross-family rollback-refund "
                  "(CreateAccount + UseGlobalContract by account or by hash, panicking init), 4 seeds"),
        control=("C5 (rollback-refund, 4 seeds); w08 code-cache family: the pre-change "
                 "completeCodeGlobal binary rejects 720 nearcore-accepted chunks"),
        lean="Successor/StorageExecution.lean resolveCode (D3.L4.Rci.resolve, kGlobalContractCode)",
    ),
    "code-cache": dict(
        paths=[EV + "w08-warm-cache/README.md", EV + "open-uqs/README.md",
               EV + "pipeline-race-fixtures/README.md"],
        fixtures=("UQ-002: 279/279 corpus `e.code_cache` cases decided or race-excluded, 0 "
                  "disagreements (169 accept/accept, 15 reject/reject, 95 race exclusions all "
                  "nearcore-rejected cold); w08 code-cache family, 5 seeds (800-804); "
                  "pipeline-race-fixtures, 4 seeds, 3,853 cases"),
        control=("the pre-change completeCodeGlobal binary rejects 720 nearcore-accepted "
                 "deploy-served chunks; without the pipeline rule 89 nearcore-rejected chunks "
                 "are accepted (carried over in open-uqs)"),
        lean=("Successor/CodeResolution.lean (cold policy; complete_eq_cold, "
              "complete_untimely_ood, raceExclusion_isExclusion)"),
    ),
    "resharding": dict(
        paths=[EV + "resharding-fixtures/README.md", EV + "resharding-fixtures-2/README.md",
               EV + "signed-completeness/README.md", EV + "proof-debt/README.md", W12],
        fixtures=("resharding-fixtures (seeds 11, 23; 6 chains): 1,087 honest PV86 witnesses all "
                  "accepted, 86/86 mutants rejected, blind 1,084/1,087 (3 harness blind errors); "
                  "resharding-fixtures-2 (seeds 31, 37, 41, 51, 61, 67; consecutive splits, "
                  "threshold gates, two layout changes in one walk): 1,833/1,833 honest accepted, "
                  "182/182 mutants rejected, 0 disagreements, blind 1,832/1,833"),
        control=("the pre-W11 checker rejects 5 valid post-split chunks (3 implicit-transition "
                 "post roots, 2 InvalidBandwidthRequests); `--ablate-reshard-handover` restores "
                 "the signed-tier exclusion on every hand-over case (asserted by make d3-smoke)"),
        lean=("O6 proved at verdict level (Successor/TierO6.lean "
              "checkSuccessor_resharding_vmono); W11 split correctness (ReshardingProofs.lean "
              "retainSplit_get, splitKey_partition, splitRootE_refinedBy); kernel non-vacuity "
              "relAllFeatures_seed37_00_h10085_s7 (Examples/RealCaseD3Split*); "
              "Successor/LayoutReach.lean (a PV86 layout change is a V3 split)"),
    ),
    "genesis": dict(
        paths=[EV + "open-uqs/README.md", EV + "cross-family-fixtures/README.md"],
        fixtures=("UQ-017: 266/266 genesis-main corpus chunks accept/accept on allFeatures; "
                  "cross-family genesis-tx, 4 seeds (501-504, 3 chains each): 60 genesis-B2 chunks "
                  "with full mutant sets, 8,149 rows, 0 disagreements"),
        control=("C3 (genesis-B2 last-chunk transaction root unchecked: 15 `g.tx_in_genesis_chunk` "
                 "mutants per run accepted against nearcore's reject)"),
        lean=("Successor/RuntimeCore.lean checkD2CoreGWith (genesis branch: the non-genesis "
              "comparison set against the stored genesis chunk extra, tx_valid all-1); "
              "GenesisD3.checkD3G; tier-lift/genesis-overlap theorems"),
    ),
    "segment": dict(
        paths=[EV + "gate-b-caps/README.md"],
        fixtures=("gate-b-caps: the 7 nearcore-valid corpus claims with > 32 blocks accept; "
                  "seg29/seg30/seg31/seg32/seg70 chains (n_blocks 31-71, 1,144 honest chunks) all "
                  "accept, blind match"),
        control="the same tree without the lift (checker e3c9ff28) excludes exactly those 7 claims",
        lean="ProtocolCfg.segmentUnbounded on Tier.cfg .allFeatures",
    ),
    "witness-size": dict(
        paths=[EV + "gate-b-caps/README.md"],
        fixtures=("gate-b-caps: wsize.near-above and wsize.above (witnesses of 8,434,574 and 9,464,574 B, "
                  "above the former 8 MiB bound) are accepted by cold nearcore and by allFeatures, blind "
                  "match; wsize.below / near-below accept on both checkers; the 64 MiB decode bound and the "
                  "w.compressed_size band are tested with constructed witnesses at 8,388,608 / 50,000,000 / "
                  "67,108,864 B and one byte above each"),
        control="the checker without the lift reports `out of domain (w.size)` on exactly wsize.near-above and wsize.above",
        lean="ProtocolCfg.witnessUnbounded on Tier.cfg .allFeatures; compressedSafeWitnessBytes_ok",
    ),
    "gas-cap": dict(
        paths=[EV + "gate-b-caps/README.md", EV + "signed-completeness/README.md"],
        fixtures=("gate-b-caps fixture gas.above (1.8 Pgas of function-call gas in one chunk, "
                  "nearcore ok) accepts, blind match; the 1,010 corpus `e.g_alpha` chunks are "
                  "decided on allFeatures (pre-freeze replay: no e.g_alpha exclusion)"),
        control="the checker with gasCap = some maxGasBurnt excludes gas.above (e.g_alpha)",
        lean="gasCap := none on Tier.cfg .allFeatures (nearcore's max_gas_burnt is per call)",
    ),
    "storage-proof": dict(
        paths=[EV + "storage-limit-fixtures/README.md", EV + "open-uqs/README.md", W12],
        fixtures=("storage-limit-fixtures, seeds 99/101: one-byte flips of the per-receipt and "
                  "chunk soft limits, 3,098 cases per tier agree, blind 2,691/2,691 gradable; "
                  "removal-soft (W12 §16.1), 4 seeds, 7,296 cases: the recorder engine "
                  "(storageResolution, used by allFeatures) has 0 disagreements"),
        control=("the legacy-engine tiers (runtimeLimits and the pre-move-(f) signed tier) "
                 "disagree with nearcore on 624 of the 7,296 removal-soft cases"),
        lean=("recorder drivers set sizeOk := true and model RecordedStorageCounter and "
              "main_storage_proof_size_soft_limit exactly; UQ-015 answered (bound sound)"),
    ),
    "eth-wallet": dict(
        paths=[EV + "eth-wallet-fixtures/README.md", EV + "open-uqs/README.md"],
        fixtures=("eth-wallet-fixtures: genesis ETH-implicit accounts holding each of the four legacy "
                  "wallet magic hashes (as pre-PV83 accounts do), called through the chain's global "
                  "wallet (rlp_execute transfers and function calls through the wallet, failing "
                  "calls) and, in a second scenario, before the global wallet exists; 8 seeds "
                  "(701-704, 791-794), 931 honest chunks + 9,719 mutants = 10,650 cases, "
                  "allFeatures 0 accept/reject disagreements with cold nearcore (7 named "
                  "e.code_prep_race exclusions of baseline code mutants), blind 908/908 gradable "
                  "honest chunks match; signed tier 0 disagreements (every wallet chunk excluded as "
                  "e.eth_implicit_local)"),
        control=("a checker built with the redirect ablated (control/ablate-eth-redirect.patch: a "
                 "magic-hash ETH-implicit account treated as having no contract) changes 609 rows, all wallet cases: 587 "
                 "nearcore-valid chunks rejected (post state root) and 22 nearcore-rejected "
                 "pre-deployment chunks accepted"),
        lean=("Successor/StorageExecution.lean resolveCode via D3.L4.Rci.resolve; UQ-007: "
              "legacyWallet_unreachable_pv86, ethWallet_kind_unreachable, 7/7 wallet hashes recomputed "
              "from nearcore's embedded wasm equal Lean's (one-byte control fails); the corpus "
              "e.eth_implicit_local claims (ordinary local contracts) agree with cold nearcore"),
    ),
}


def _validated(repo, key):
    """The evidence string of a registry entry, after checking every path exists."""
    e = VALIDATION[key]
    missing = [p for p in e["paths"] if not (Path(repo) / p).exists()]
    if missing:
        raise ValueError(f"validation evidence for {key} is missing: {missing}")
    if not e["fixtures"] or not e["control"]:
        raise ValueError(f"validation entry {key} lacks fixtures or a breakage control")
    return (f"whole-chunk fixtures: {e['fixtures']}. Breakage control: {e['control']}. "
            f"Lean: {e['lean']}. Evidence: {', '.join(e['paths'])}")


# --- Per-row evidence (L0 row validation, 2026-10-31) --------------------------------------
# `l0-row-validation/rows.json` is written by `tools/d3/l0_exercise.py evidence`. For one row it
# records the exercising whole-chunk cases (from the observation trace of the control build, each
# judged by cold pinned nearcore or, for claim mutants, by the claim-v3 discipline) and a per-row
# breakage control (`NEARSPEC_ABLATE=<target>` in the control build, replayed through the
# repository's comparator). A row is promoted only when (i) the derived surface already made it
# `implemented`, (ii) the entry has at least ROW_MIN_ACCEPT nearcore-accepted and ROW_MIN_REJECT
# nearcore-rejected exercising cases (guards: deciding rejects only), (iii) the unablated replay of
# the control cases passes and (iv) the ablated replay has at least one disagreement.
ROW_EVIDENCE_DIR = EV + "l0-row-validation/"
ROW_EVIDENCE = ROW_EVIDENCE_DIR + "rows.json"
ROW_MIN_ACCEPT = {"host": 1, "action": 1, "d2-core": 0, "instruction": 1, "wasm-exec": 1,
                  "wasm-prepare": 1, "successor-guard": 1}
ROW_MIN_REJECT = {"host": 1, "action": 1, "d2-core": 1, "instruction": 1, "wasm-exec": 1,
                  "wasm-prepare": 1, "successor-guard": 1}
# Second pass (2026-10-30): two further statuses an entry may request (`"status"` in rows.json).
# * `validated-by-subsumption`: a guard that can be the first failure, but whose removal never
#   changes a verdict, because a later guard rejects every input it rejects. The entry names the
#   subsuming rows (each must itself be `validated` in this inventory), the deciding fixtures (≥ 1
#   case rejected first by this guard, with an unablated pass) and the ablated replay (every case
#   still rejected), plus the proof (Lean lemmas in L0_LEMMAS, each must be declared there) or the
#   source argument. Emitted as `validated` with a subsumption evidence entry.
# * `impossible-at-boundary`: a guard that can never be the first failure on `allFeatures` (never
#   evaluated there, proved never to fail, or reachable only on inputs no nearcore chain produces).
#   The entry gives the reason; named Lean lemmas must be declared in L0_LEMMAS.
# An entry may also set `lean_path_symbol` (the `allFeatures` site of a row first written against
# the signed tier); it is applied whatever the row's status.
L0_LEMMAS = "spec/lean/v3/NearSpecV3/L0GuardSubsumption.lean"
_ROW_CACHE = {}


def _row_evidence(repo):
    key = str(repo)
    if key not in _ROW_CACHE:
        p = Path(repo) / ROW_EVIDENCE
        _ROW_CACHE[key] = json.loads(p.read_text())["rows"] if p.exists() else {}
    return _ROW_CACHE[key]


def _check_surface(repo, rid, items):
    """Each `{"file", "text"}` must occur in the named Lean file (drift guard for a reason that
    rests on the current `allFeatures` configuration or code shape)."""
    for it in items:
        src = (Path(repo) / LEAN_ROOT / it["file"]).read_text()
        if it["text"] not in src:
            raise ValueError(f"row {rid}: surface text {it['text']!r} no longer in {it['file']}")


def _check_lemmas(repo, rid, names):
    src = (Path(repo) / L0_LEMMAS).read_text()
    for n in names:
        short = n.rsplit(".", 1)[-1]
        if f"theorem {short} " not in src:
            raise ValueError(f"row {rid}: lemma {n} is not declared in {L0_LEMMAS}")


def _status_entry(repo, r, e):
    """`impossible-at-boundary` entries (subsumption entries are applied by promote_subsumed)."""
    paths = [ROW_EVIDENCE_DIR + "README.md", ROW_EVIDENCE] + e.get("paths", [])
    missing = [p for p in paths if not (Path(repo) / p).exists()]
    if missing:
        raise ValueError(f"row evidence for {r['id']} is missing: {missing}")
    _check_lemmas(repo, r["id"], e.get("lean", []))
    _check_surface(repo, r["id"], e.get("surface", []))
    out = dict(r)
    out["status"] = "impossible-at-boundary"
    lean = f" Lean: {', '.join(e['lean'])} ({L0_LEMMAS})." if e.get("lean") else ""
    ex = e.get("exercising")
    fx = (f" Fixtures: {ex['nearcore_reject']} {ex['source']} (e.g. {', '.join(ex['examples'][:2])})."
          if ex else "")
    reason = e["reason"] if e["reason"].endswith(".") else e["reason"] + "."
    out["evidence"] = (f"L0 row validation, second pass (2026-10-30): {reason}{lean}{fx} "
                       f"Evidence: {', '.join(paths[:2])} | earlier record: {r['evidence']}")
    out["remaining_work"] = e.get("remaining", "none on allFeatures")
    return out


def promote_row(repo, r):
    """Apply a per-row evidence entry to an `implemented` row (see the rules above)."""
    e = _row_evidence(repo).get(r["id"])
    if e is not None and e.get("lean_path_symbol"):
        r = dict(r, lean_path_symbol=e["lean_path_symbol"])
    if r["status"] != "implemented":
        return r
    if e is not None and e.get("status") == "impossible-at-boundary":
        return _status_entry(repo, r, e)
    if e is not None and e.get("status") == "validated-by-subsumption":
        return r  # promote_subsumed, once every row's own status is known
    if e is not None and e.get("status") == "implemented":
        return dict(r, remaining_work=e["remaining"])
    if r["family"] not in ROW_MIN_REJECT:
        return r
    if e is None:
        if r["family"] != "host" or not _row_evidence(repo):
            return r
        return dict(r, remaining_work=r["remaining_work"] + "; L0 row validation (2026-10-31): no case "
                    "of its populations calls this host, so a cold-judged scenario contract is needed "
                    f"({ROW_EVIDENCE_DIR}README.md)")
    paths = [ROW_EVIDENCE_DIR + "README.md", ROW_EVIDENCE, "tools/d3/l0_ctl_patch.py",
             "tools/d3/l0_exercise.py"] + e.get("paths", [])
    missing = [p for p in paths if not (Path(repo) / p).exists()]
    if missing:
        raise ValueError(f"row evidence for {r['id']} is missing: {missing}")
    ex, ctl = e["exercising"], e["control"]
    fam = r["family"]
    if ex.get("disagreements_caused", 0):
        return dict(r, remaining_work=r["remaining_work"] + "; L0 row validation (2026-10-31): Lean "
                    f"disagrees with nearcore on {ex['disagreements_caused']} exercising cases "
                    f"(completeness bug: {e.get('disagreement_reason', 'see the evidence README')}) "
                    f"({ROW_EVIDENCE_DIR}README.md)")
    if not (ex["nearcore_accept"] >= ROW_MIN_ACCEPT[fam] and ex["nearcore_reject"] >= ROW_MIN_REJECT[fam]
            and ctl["baseline"] == "pass" and ctl["ablated_disagreements"] >= 1):
        why = ("removing the guard leaves every deciding mutant rejected by a later guard "
               "(verdict-redundant), so no verdict-level breakage control detects it"
               if ctl["ablated_disagreements"] == 0 else
               "positive chunks and a detecting control, but no nearcore-rejected exercising chunk")
        return dict(r, remaining_work=r["remaining_work"] + f"; L0 row validation (2026-10-31): {why} "
                    f"({ROW_EVIDENCE_DIR}README.md)")
    out = dict(r)
    out["status"] = "validated"
    out["evidence"] = (
        (f"whole-chunk fixtures: {ex['nearcore_reject']} witness+claim mutants rejected first by this guard "
         f"(judged by cold nearcore) " if fam == "d2-core" and "nearcore (cold)" in ex["source"] else
         f"whole-chunk fixtures: {ex['nearcore_reject']} claim mutants rejected first by this guard "
         f"(claim-v3 discipline) " if fam == "d2-core" else
         f"whole-chunk fixtures: {ex['nearcore_accept']} nearcore-accepted and {ex['nearcore_reject']} "
         f"nearcore-rejected cases exercise it ") +
        f"({ex['source']}; e.g. {', '.join(ex['examples'][:3])}), " +
        (f"0 verdict disagreements caused by this row ({ex['disagreements']} disagreeing cases also "
         f"run {', '.join(ex['disagreement_cause'])}, which causes them; they are not counted). "
         if ex.get("disagreements") else "0 verdict disagreements. ") +
        f"Breakage control: `NEARSPEC_ABLATE={ctl['target']}` "
        f"({ctl['what']}) in the control build: {ctl['ablated_disagreements']} of {ctl['cases']} "
        f"replayed exercising cases disagree with the expected verdict (unablated: "
        f"{ctl['cases']}/{ctl['cases']} agree). Evidence: {', '.join(paths[:2])} | earlier record: {r['evidence']}")
    out["remaining_work"] = e.get("remaining", "none on allFeatures")
    return out


def promote_subsumed(repo, r, status):
    """Apply a `validated-by-subsumption` entry (see ROW_MIN_* comment)."""
    e = _row_evidence(repo).get(r["id"])
    if r["status"] != "implemented" or e is None or e.get("status") != "validated-by-subsumption":
        return r
    paths = [ROW_EVIDENCE_DIR + "README.md", ROW_EVIDENCE] + e.get("paths", [])
    missing = [p for p in paths if not (Path(repo) / p).exists()]
    if missing:
        raise ValueError(f"row evidence for {r['id']} is missing: {missing}")
    _check_lemmas(repo, r["id"], e.get("lean", []))
    _check_surface(repo, r["id"], e.get("surface", []))
    by = e["subsumed_by"]
    ex, ctl = e["exercising"], e["control"]
    ok = (all(status.get(b) == "validated" for b in by) and ex["nearcore_reject"] >= 1
          and ctl["baseline"] == "pass" and ctl["ablated_disagreements"] == 0
          and (e.get("lean") or e.get("argument")))
    if not ok:
        return dict(r, remaining_work=r["remaining_work"] + "; L0 row validation (2026-10-30): "
                    "subsumption entry incomplete (a subsuming row is not validated, or no deciding "
                    f"fixture) ({ROW_EVIDENCE_DIR}README.md)")
    out = dict(r)
    out["status"] = "validated"
    proof = (f"Lean: {', '.join(e['lean'])} ({L0_LEMMAS})" if e.get("lean") else
             f"source argument: {e['argument']}")
    out["evidence"] = (
        f"validated by subsumption (L0 row validation, 2026-10-30): {ex['nearcore_reject']} claim "
        f"mutants are rejected first by this guard (claim-v3 discipline; {ex['source']}; e.g. "
        f"{', '.join(ex['examples'][:2])}). Removing it (`NEARSPEC_ABLATE={ctl['target']}`) leaves all "
        f"{ctl['cases']} rejected ({ctl['ablated_reasons']}), so no verdict-level control can detect "
        f"it; it is subsumed by {', '.join(by)} (validated): {e['why']}. {proof}. Evidence: "
        f"{', '.join(paths[:2])} | earlier record: {r['evidence']}")
    out["remaining_work"] = e.get("remaining", "none on allFeatures")
    return out


# --- L4: the three global-contract actions (tags 9/10/11) ---------------------------------
# The signed tier's decoder (`D2.pBase`) still rejects them; the successor decoder
# (`Successor/GlobalCodecs.lean` `pBaseGlobal`) decodes them and `allFeatures` executes them
# (`globalActions := true`). Per-tag fixture/control pointers, on top of `VALIDATION["global-actions"]`.
GLOBAL_ACTION_TAGS = {
    9: "DeployGlobalContract: global-cache deployments (incl. redeployment nonce) and their "
       "distribution receipts; dist-identity mutants; split crossings (resharding-fixtures-2 g61/g67). "
       "Control: C-D1/C-D2",
    10: "UseGlobalContract: global-cache hash/account use+call, missing-use failure, use+call "
        "rollback; rollback-refund CreateAccount + UseGlobalContract. Control: C5",
    11: "DeterministicStateInit: global-cache third-party/repeated inits, missing-code and "
        "insufficient-deposit failures; state-init-emit compositions; global-promise state-init "
        "hosts. Control: C-S",
}


def _l0_supplement():
    """Execution/boundary rows and the oracle/exclusion/UQ sections (research analysis)."""
    import lean_chunk_coverage_l0 as l0

    return {"rows": l0.extra_rows(), "sections": l0.sections(), "lean_files": l0.lean_files()}


def git_show(repo, path):
    return subprocess.check_output(
        ["git", "-C", str(repo), "show", f"{PIN}:{path}"], text=True
    )


def action_tags(repo):
    src = git_show(repo, ACTION_MOD)
    block = src.split("pub enum Action {", 1)[1].split("\n}", 1)[0]
    block = re.sub(r"///[^\n]*", "", block)
    block = re.sub(r"//[^\n]*", "", block)
    tags = []
    for m in re.finditer(r"(\w+)\s*\([^)]*\)\s*=\s*(\d+)\s*,", block):
        tags.append((m.group(1), int(m.group(2))))
    if not tags:
        raise ValueError("unparsed action enum")
    numbers = [t for _, t in tags]
    if numbers != sorted(set(numbers)):
        raise ValueError("action tags not strictly increasing")
    return tags


def env_imports(repo):
    """Host import names from imports.rs, reusing the established extractor."""
    src = git_show(repo, VM + "imports.rs")
    body = src.split("\nimports! {\n", 1)[1].split("\n}", 1)[0]
    body = re.sub(r"//[^\n]*", "", body)
    # Entries may span lines (name, then `<[`, args, `] -> [...]>,`), so split on the
    # terminating `>,` rather than on newlines.
    result = []
    chunks = re.split(r">\s*,", body)
    for chunk in chunks:
        chunk = " ".join(chunk.split())
        if "<[" not in chunk:
            continue
        d = {"gate": None, "feature": None, "module": "env", "alias": None}
        gate = re.search(r"#\[(\w+)\]", chunk)
        if gate:
            d["gate"] = gate.group(1)
        feature = re.search(r'#\[\["(\w+)"\]\]', chunk)
        if feature:
            d["feature"] = feature.group(1)
        module = re.search(r"@in\s+(\w+)\s*:", chunk)
        if module:
            d["module"] = module.group(1)
        alias = re.search(r"@as\s+(\w+)\s*:", chunk)
        if alias:
            d["alias"] = alias.group(1)
        # The import name is the leading identifier; `@as` supplies the Wasm-visible name.
        fn = re.search(r"(?<![\w@])([a-z][a-z0-9_]*)\s*<\[", chunk)
        if not fn:
            continue
        d["function"] = fn.group(1)
        d["name"] = d["alias"] or d["function"]
        result.append(d)
    if not result:
        raise ValueError("unparsed imports block")
    return result


def lean_host_arms(repo):
    src = (repo / LEAN_ROOT / "Wasm/Host.lean").read_text()
    return sorted(set(re.findall(r'^\s*\| "([a-z0-9_]+)"', src, re.MULTILINE)))


def lean_crypto_host_arms(repo):
    """Curve hosts with a transcribed host semantics in the successor table (`Wasm/CryptoHost.lean`).

    The signed tier (`checkD3`) still reports a *call* of one out of domain (`Host.hostCall` has
    no arm for them; `D3/CryptoDomain.hostCall_no_arm` checks that). The successor dispatches
    them through this table when `St.curveHosts` is set, which `allFeatures` does.

    `alt_bn128_*` is included: its arithmetic/codec lives in `NearSpecV3/AltBn128.lean` and its
    three arms are in the same `cryptoHostCall` table. Only the *payload* file differs; the arm's
    presence in the table is what this function reports.
    """
    src = (repo / LEAN_ROOT / "Wasm/CryptoHost.lean").read_text()
    block = src.split("def cryptoHostCall", 1)[1]
    return sorted(set(re.findall(r'^\s*\| "([a-z0-9_]+)" => some', block, re.MULTILINE)))


def curve_fixture_steps(repo):
    """Per-host whole-chunk step counts from the curve-host fixture README's coverage table:
    name -> (steps, pos, neg, edge, chunks). Read, not asserted: a host is validated only if the
    table shows at least one positive and one negative step for it."""
    src = (Path(repo) / EV / "curve-host-fixtures/README.md").read_text()
    out = {}
    for m in re.finditer(r"^\| `([a-z0-9_]+)` \| (\d+) \((\d+)/(\d+)/(\d+)\) \| (\d+) \|", src, re.MULTILINE):
        out[m.group(1)] = tuple(int(m.group(i)) for i in range(2, 7))
    return out


def allfeatures_cfg(repo):
    """The flags `Tier.cfg .allFeatures` sets (`Successor/Config.lean`), as source text values."""
    src = (repo / LEAN_ROOT / "Successor/Config.lean").read_text()
    block = src.split("| .allFeatures =>", 1)[1].split("}", 1)[0]
    flags = dict(re.findall(r"(\w+)\s*:=\s*([^,]+?)\s*(?:,|$)", block, re.MULTILINE))
    if "globalActions" not in flags:
        raise ValueError("unparsed Tier.cfg .allFeatures")
    return {k: v.strip() for k, v in flags.items()}


def successor_global_tags(repo):
    """Action tags the successor decoder `pBaseGlobal` decodes itself (not via `pBase`)."""
    src = (repo / LEAN_ROOT / "Successor/GlobalCodecs.lean").read_text()
    block = src.split("def pBaseGlobal (tag : Nat)", 1)[1].split("\ndef ", 1)[0]
    return sorted({int(m.group(1)) for m in re.finditer(r"^\s*\|\s*(\d+)\s*=>\s*let", block, re.MULTILINE)})


def successor_facts(repo):
    """Facts about the canonical relation the derived promotions read. Each is a presence test
    on the current tree; none names a retired module."""
    root = repo / LEAN_ROOT
    rd = lambda p: (root / p).read_text() if (root / p).exists() else ""
    flags = allfeatures_cfg(repo)
    on = lambda k: flags.get(k) == "true"
    rc, ce, se = rd("Successor/RuntimeCore.lean"), rd("Successor/CodeResolution.lean"), rd("Successor/StorageExecution.lean")
    any_contract_in_d3a = any("def contractInD3α" in p.read_text() for p in root.rglob("*.lean"))
    return {
        "flags": flags,
        "globalActions": on("globalActions"),
        "curveHosts": on("curveHosts"),
        "resharding": on("resharding") and "def checkReshardCoreObs" in rd("Successor/ReshardCore.lean"),
        "genesis": on("genesisMainTransition")
                   and "tx_valid not all 1 for a genesis main block" in rc,
        "segmentUnbounded": on("segmentUnbounded"),
        "witnessUnbounded": on("witnessUnbounded"),
        "gasCapNone": flags.get("gasCap") == "none",
        "storageResolution": on("storageResolution"),
        "globalTags": successor_global_tags(repo),
        "signedHandover": "def withReshardHandover" in rd("D3/Signed.lean"),
        "noReshardingInReshardingD3": "def noResharding" in rd("ReshardingD3.lean"),
        "contractInD3aGone": not any_contract_in_d3a,
        "ethResolve": "def resolveCode" in se and "Rci.resolve" in se,
        "prepRace": "out of domain (e.code_prep_race)" in ce,
        "codeResponse": "out of domain (w.code_response_size)" in rc,
        "fuelCert": "w.fuel_certificate" in se,
        "globalIdentity": "global_code_identity" in rd("Successor/GlobalExecution.lean"),
    }


def lean_base_tags(repo):
    """Action tags the Lean D2 decoder accepts, and those it rejects as out of domain."""
    src = (repo / LEAN_ROOT / "D2/Types.lean").read_text()
    block = src.split("def pBase (tag : Nat) : P Base := fun bs =>", 1)[1]
    block = block.split("/--", 1)[0]
    ood = []
    for m in re.finditer(r"^\s*\|\s*(\d+)\s*=>\s*throw\s+(ood\w+)", block, re.MULTILINE):
        ood.append((int(m.group(1)), m.group(2)))
    excluded = {t for t, _ in ood}
    ok = []
    for m in re.finditer(r"^\s*\|\s*(\d+)\s*=>", block, re.MULTILINE):
        tag = int(m.group(1))
        if tag not in excluded:  # a tag that throws is not a decoded tag
            ok.append(tag)
    return sorted(ok), sorted(ood)


def _pAct(repo):
    src = (repo / LEAN_ROOT / "D2/Types.lean").read_text()
    return src.split("def pAct : P Act", 1)[1].split("/--", 1)[0]


def lean_instr_ops(repo):
    """Numeric opcode bytes accepted by the Lean decoder."""
    src = (repo / LEAN_ROOT / "Wasm/Decode.lean").read_text()
    ops = set()

    def add_range(a, b):
        for x in range(a, b + 1):
            ops.add(x)

    for m in re.finditer(r"\(0x([0-9A-Fa-f]{2}) ≤ op && op ≤ 0x([0-9A-Fa-f]{2})\)", src):
        add_range(int(m.group(1), 16), int(m.group(2), 16))
    for m in re.finditer(r"op = 0x([0-9A-Fa-f]{2})", src):
        ops.add(int(m.group(1), 16))
    return sorted(ops)


def float_coverage(repo):
    """L2's surface, read from the Lean source (not asserted): which float opcodes the kernel
    decides, whether the preparation switch and the successor relation exist, and how many decided
    directed cases the build checks.

    The *status* is derived, not stored by hand: a float row is `implemented` only when the kernel
    decides all 70 opcodes the decoder admits, the four guard sites are switchable, and the
    successor relation exists. Anything less is `partial` with the missing count recorded."""
    root = repo / LEAN_ROOT
    fl = (root / "Wasm/Float.lean").read_text()
    prep = (root / "Wasm/Prepare.lean").read_text()
    tests = (root / "Wasm/FloatTests.lean").read_text()
    osucc = (root / "ChallengeChunkV3Float.lean").read_text()
    # the opcode arms of `evalFloatOp`
    ev = fl.split("def evalFloatOp", 1)[1].split("/--", 1)[0] if "def evalFloatOp" in fl else ""
    arms = set(int(m.group(1), 16) for m in re.finditer(r"\|\s*0x([0-9A-Fa-f]{2,4})\s*=>", ev))
    # the opcodes the kernel classifies as decided (no immediates)
    imm = fl.split("def isFloatOpNoImm", 1)[1].split("\n/--", 1)[0] if "def isFloatOpNoImm" in fl else ""
    decided = 0
    for m in re.finditer(r"\(0x([0-9A-Fa-f]{2,4}) ≤ op && op ≤ 0x([0-9A-Fa-f]{2,4})\)", imm):
        lo, hi = int(m.group(1), 16), int(m.group(2), 16)
        decided += hi - lo + 1
    guard_sites = sum(prep.count(f'"{msg}"') for msg in
                      ("float in an imported function type", "float global",
                       "float type or operator in a function body"))
    switchable = ("floats : Bool := false" in prep and
                  "def floatPv86 : NearCfg := { pv86 with floats := true }" in prep)
    directed = len(re.findall(r"^theorem ", tests, re.MULTILINE))
    successor = "def checkD3F " in osucc and "theorem checkD3F_characterization" in osucc
    return {
        "eval_arms": len(arms),
        "decided_opcodes": decided,
        "guard_sites": guard_sites,
        "switchable": switchable,
        "directed_tests": directed,
        "successor_relation": successor,
        "complete": len(arms) >= 70 and decided == 70 and switchable and guard_sites == 3
                    and successor,
    }


def domain_guards(repo):
    """Named domain guards the plan asks L0 to enumerate."""
    # The parallel domain module was retired 2026-10-29 (UQ-010): `noResharding` moved to ReshardingD3.lean
    # (it describes the legacy core's guards, not the statement of record), `contractInD3α` was
    # dropped (it described no checker). See docs/research/lean-chunk-w00-owner-map.md §3.4.
    dom = (repo / LEAN_ROOT / "ReshardingD3.lean").read_text()
    syn = (repo / LEAN_ROOT / "Wasm/Syntax.lean").read_text()
    prep = (repo / LEAN_ROOT / "Wasm/Prepare.lean").read_text()
    return {
        "noResharding": "def noResharding" in dom,
        "curveHosts": "def curveHosts" in (repo / LEAN_ROOT / "Wasm/Exec.lean").read_text(),
        # L2 keeps the guard *and* adds a switch that turns it off, so the presence test is that
        # the three preparation messages, the switch and its default all exist. (The execution-side
        # sentinel was `float (out of domain)` before L2; it is now a decided operator, so the
        # preparation guards are what the row means.)
        # `>= 1`, not `== 1`: L2 names each guard as a predicate (`floatGuardImport` etc.) whose
        # doc comment repeats the message the `throw` site uses, so the literal appears twice. The
        # row is about the guard existing and being switchable, not about how often the message is
        # mentioned in a comment.
        "floatOutOfDomain": (
            "float in an imported function type" in prep
            and "float global" in prep
            and "float type or operator in a function body" in prep
            and "floats : Bool := false" in prep),
    }


def row(i, family, symbol, lean, status, guard, evidence, owner, deps, tests, remaining):
    return {
        "id": i,
        "family": family,
        "nearcore_commit": PIN,
        "nearcore_path_symbol": symbol,
        "lean_path_symbol": lean,
        "status": status,
        "domain_guard": guard,
        "evidence": evidence,
        "owner": owner,
        "dependencies": deps,
        "acceptance_tests": tests,
        "remaining_work": remaining,
    }


# --- Reconciliation of the hand-written L0 rows against the canonical relation -------------
# `lean_chunk_coverage_l0.py` describes each guard as the signed core (`checkD2Core`/
# `checkD3Core`) has it. For the rows below the canonical relation (`allFeatures`) has since
# lifted or decided the guard. Each entry is (Lean-surface condition on `successor_facts`,
# fields applied when it holds, VALIDATION key or None). When the condition fails the l0 row is
# emitted unchanged, so a regression in the Lean surface shows up as a status change in --check.
L0_RECONCILE = {
    "L0-D2-015": (lambda f: f["segmentUnbounded"], dict(
        status="validated",
        lean_path_symbol="ProtocolCfg.segmentUnbounded (Tier.cfg .allFeatures); signed: ChunkValidationD2.lean:144",
        domain_guard="allFeatures: lifted (no segment bound, as in nearcore); signed tier (checkD3Core): c.segment (n_blocks ≤ 32)",
        remaining_work="none on allFeatures. The signed tier keeps c.segment as a stated prover-capacity "
                       "restriction (3 census claims with 41/41/43 blocks)",
    ), "segment"),
    "L0-D2-002": (lambda f: f["witnessUnbounded"], dict(
        status="validated",
        lean_path_symbol="ProtocolCfg.witnessUnbounded (Tier.cfg .allFeatures; guard sites ReshardCore.lean:229-230, "
                         "RuntimeCore.lean:416-417 not evaluated); signed: ChunkValidationD2.lean:120",
        domain_guard="allFeatures: lifted (nearcore's 64 MiB decode limit stays in the decoder; the "
                     "w.compressed_size exclusion covers (50,000,000 B, 64 MiB]); signed tier (checkD3Core): "
                     "w.size (8 MiB)",
        remaining_work="none on allFeatures. The signed tier keeps the 8 MiB bound as a stated "
                       "prover-capacity restriction",
    ), "witness-size"),
    "L0-D2-040": (lambda f: f["storageResolution"], dict(
        status="validated",
        lean_path_symbol="Successor/StorageExecution (recorder driver, sizeOk := true; per-receipt and soft limits "
                         "modelled); signed: ChunkValidationD2.lean:235-237 + D3.withReshardHandover precondition 2",
        domain_guard="allFeatures: no storage-proof bound; nearcore's per-receipt limit and chunk soft limit are "
                     "executed exactly. Signed tier (checkD3): the core's bound, handed to the recorder when "
                     "values + code + 2000·R exceed 4,000,000 (owner map §3.4 move (f))",
        remaining_work="none on allFeatures. UQ-015 answered (the signed bound is sound). The narrower legacy "
                       "tier runtimeLimits reports w.size on 1,580 removal-soft cases (exclusion, never an accept)",
    ), "storage-proof"),
    "L0-D2-041": (lambda f: f["gasCapNone"], dict(
        status="validated",
        lean_path_symbol="ProtocolCfg.gasCap = none (Tier.cfg .allFeatures); signed: ChunkValidationD2.lean:240",
        domain_guard="allFeatures: lifted (nearcore has no per-chunk function-call gas limit); signed tier "
                     "(checkD3Core): e.g_alpha, lifted on the hand-over path",
        remaining_work="none on allFeatures. The signed tier keeps G_α on the core path as a stated "
                       "prover-capacity restriction (847 census claims)",
    ), "gas-cap"),
    "L0-D3-006": (lambda f: f["ethResolve"], dict(
        status="validated",
        lean_path_symbol="NearSpecV3.Successor.StorageExecution.resolveCode (D3.L4.Rci.resolve) on allFeatures; "
                         "signed: D3/FunctionCall.lean:236-240",
        domain_guard="allFeatures: decided (a magic hash redirects to the chain's global wallet; any other local "
                     "contract stays local; .legacyEthWallet unreachable at PV86); signed tier (checkD3Core): "
                     "e.eth_implicit_local",
        acceptance_tests="a PV86 chain whose genesis holds ETH-implicit accounts with legacy magic-hash "
                         "contracts, called in whole chunks (eth-wallet-fixtures); breakage control: "
                         "resolveCode without the wallet redirect",
        remaining_work="none on allFeatures. The signed tier keeps e.eth_implicit_local (210 census claims; "
                       "every wallet chunk of the family is excluded there, never decided wrongly)",
    ), "eth-wallet"),
    "L0-D3-008": (lambda f: f["ethResolve"] and f["globalActions"], dict(
        status="validated",
        lean_path_symbol="NearSpecV3.Successor.StorageExecution.resolveCode (.global codeHash/accountId, "
                         "kGlobalContractCode) on allFeatures; signed: D3/FunctionCall.lean:248",
        domain_guard="allFeatures: decided; signed tier (checkD3Core): w.shape global contract identifier "
                     "(reached only after the action decoder, which rejects tags 9-11 first)",
        remaining_work="none on allFeatures; the signed tier keeps the w.shape exclusion",
    ), "global-receivers"),
    "L0-D3-009": (lambda f: f["prepRace"], dict(
        status="validated",
        lean_path_symbol="NearSpecV3.Successor.CodeResolution (cold policy) on allFeatures; signed: "
                         "D3/FunctionCall.lean:252-275",
        domain_guard="allFeatures: committed and rolled-back same-code deploys decided; only the "
                     "preparation-pipeline race is excluded (e.code_prep_race, row L0-AF-prep-race). "
                     "Signed tier (checkD3Core): e.code_cache",
        remaining_work="none on allFeatures beyond row L0-AF-prep-race. The signed tier keeps e.code_cache "
                       "(169 census claims)",
    ), "code-cache"),
    "L0-D3-011": (lambda f: f["prepRace"], dict(
        status="validated",
        lean_path_symbol="NearSpecV3.Successor.CodeResolution.resolveCodeBytes (in-chunk deploys: the deploy "
                         "tracker `current`, committed and attempted deploys, the compiled cache) via "
                         "StorageExecution.functionCallRecordedF on allFeatures; signed: D3/FunctionCall.lean:268-275",
        domain_guard="allFeatures: decided (an in-chunk deploy serves a later call of the same code, committed "
                     "or rolled back); only the preparation-pipeline race is excluded (row L0-AF-prep-race). "
                     "Signed tier (checkD3Core): codeAvailable / e.code_cache",
        remaining_work="none on allFeatures beyond row L0-AF-prep-race (the same evidence as row L0-D3-009)",
    ), "code-cache"),
    "L0-W-015": (lambda f: f["curveHosts"], dict(
        status="validated",
        lean_path_symbol="NearSpecV3.Wasm.CryptoHost.cryptoHostCall (allFeatures, St.curveHosts); signed: "
                         "Wasm/Exec.lean curveHosts (no Host.hostCall arm)",
        domain_guard="allFeatures: dispatched; signed tier (checkD3): a call is out of domain (e.wasm-α)",
        remaining_work="none on allFeatures (per-host rows L0-host-*); breakage controls are family-level. "
                       "The signed tier keeps the call exclusion (245 census claims)",
    ), "curve-hosts"),
    "L0-W-016": (lambda f: f["noReshardingInReshardingD3"] and f["signedHandover"], dict(
        status="implemented",
        lean_path_symbol="spec/lean/v3/NearSpecV3/ReshardingD3.lean:80 `noResharding`, `noResharding_spec`",
        domain_guard="none: a description of the legacy core's guards, not a domain condition",
        evidence="UQ-010 closed 2026-10-29 (owner map §3.4 (d)): the parallel predicate module was retired; "
                 "`noResharding` moved to ReshardingD3.lean as the description of D3.checkD3Core's "
                 "c.same_layout/c.no_split_gate guards. The statement of record (D3.checkD3) decides "
                 "claims that fail it (D3.withReshardHandover; checkD3_cases) and allFeatures decides them "
                 "(row L0-resharding)",
        acceptance_tests="prove `checkD3 => noResharding` or delete the duplicate (done: retired)",
        remaining_work="none (retired as a domain predicate)",
    ), None),
    "L0-W-017": (lambda f: f["contractInD3aGone"], dict(
        status="implemented",
        lean_path_symbol="none (contractInD3α dropped); the call-vs-import gate is Wasm/Exec.lean runCall "
                         "and D3/FunctionCall.lean contractOOD (row L0-W-010)",
        domain_guard="none",
        evidence="UQ-010 closed 2026-10-29 (owner map §3.4 (d)): contractInD3α excluded a contract that merely "
                 "imports a curve host, while every checker excludes only a call, so it described no checker "
                 "and was dropped. The import/call behaviour is row L0-W-010 (192 import-only cases)",
        acceptance_tests="import-only curve case accepted (L0-W-010)",
        remaining_work="none (retired)",
    ), None),
}


def reconcile_l0(repo, sf, r):
    entry = L0_RECONCILE.get(r["id"])
    if entry is None:
        return r
    cond, fields, key = entry
    if not cond(sf):
        return r
    out = dict(r)
    out.update(fields)
    if key is not None:
        out["evidence"] = _validated(repo, key) + " | earlier signed-tier record: " + r["evidence"]
    elif "evidence" not in fields:
        out["evidence"] = r["evidence"]
    return out


def inventory(repo, nearcore):
    """`repo` is the nearproof checkout (Lean side); `nearcore` the pinned source."""
    repo = Path(repo)
    nearcore = Path(nearcore)
    tags = action_tags(nearcore)
    imports = env_imports(nearcore)
    arms = set(lean_host_arms(repo))
    crypto_arms = set(lean_crypto_host_arms(repo))
    ok_tags, ood_tags = lean_base_tags(repo)
    ops = lean_instr_ops(repo)
    guards = domain_guards(repo)
    env = [i for i in imports if i["module"] == "env"]
    env_names = sorted({i["name"] for i in env})
    ood_map = dict(ood_tags)
    tag_name = {t: n for n, t in tags}
    sf = successor_facts(repo)
    curve_steps = curve_fixture_steps(repo)

    rows = []

    # --- Actions -----------------------------------------------------------
    for name, t in tags:
        # Tags 8 and 14 are delegate actions: pAct decodes them through a separate
        # branch, not pBase.  Check that branch rather than assuming pBase covers all.
        delegate = name in ("Delegate", "DelegateV2") or t in (8, 14)
        if t in ok_tags:
            status = "implemented"
            remaining = "differential test through a whole chunk; no dedicated regression yet"
            guard = "none"
        elif delegate and "if t == 8 || t == 14 then" in _pAct(repo):
            status = "implemented"
            remaining = "delegate body decodes via pAct; no whole-chunk differential case recorded"
            guard = "none"
        elif t in ood_map and t in sf["globalTags"] and sf["globalActions"] and t in GLOBAL_ACTION_TAGS:
            # Signed decoder rejects the tag; the successor decoder decodes it and allFeatures
            # executes it (globalActions). Validated through the registry entry.
            status = "validated"
            remaining = (
                "none on allFeatures. The signed tier (checkD3, D2.pBase) still excludes the tag "
                f"(`{ood_map[t]}`), a stated signed-tier restriction; O3's unconditional Lift needs "
                "LayoutsWF, which admission contract A1 supplies"
            )
            guard = (f"signed tier (checkD3): out-of-domain ({ood_map[t]}) at D2.pBase; "
                     "allFeatures: decoded by Successor.pBaseGlobal and executed")
        elif t in ood_map:
            status = "partial" if t in sf["globalTags"] else "missing"
            remaining = (
                "decoder rejects this tag as out of domain; implement codec plus "
                "execution, then remove the exclusion"
                if status == "missing" else
                "successor decoder arm exists but allFeatures does not execute it or no validation "
                "entry covers it"
            )
            guard = f"out-of-domain ({ood_map[t]})"
        else:
            status = "missing"
            remaining = "no Lean decode arm"
            guard = "undecoded"
        is_global = t in GLOBAL_ACTION_TAGS and t in sf["globalTags"]
        rows.append(row(
            f"L0-action-{t:02d}", "action", f"{ACTION_MOD}:{name} = {t}",
            "NearSpecV3.Successor.pBaseGlobal (allFeatures); signed tier: none (D2.pBase rejects)"
            if is_global
            else ("NearSpecV3.D2.Types.pBase" if t in ok_tags else "none"),
            status, guard,
            (f"{GLOBAL_ACTION_TAGS[t]}. " + _validated(repo, "global-actions"))
            if status == "validated" else
            "tools/d3/lean_chunk_coverage.py action_tags vs D2/Types.lean pBase",
            "L4", "L0", "1 valid + 1 invalid whole-chunk case per tag",
            remaining,
        ))

    # --- Host functions ----------------------------------------------------
    for name in env_names:
        if name in arms:
            status = "implemented"
            remaining = "host gas/return behaviour not differentially tested in this lane"
            guard = "none"
        elif name in crypto_arms:
            st = curve_steps.get(name)
            if sf["curveHosts"] and st and st[1] > 0 and st[2] > 0:
                status = "validated"
                remaining = (
                    f"none on allFeatures ({st[0]} fixture steps: {st[1]} pos / {st[2]} neg / "
                    f"{st[3]} edge, over {st[4]} honest chunks of seed 4242). The breakage controls "
                    "are family-level, not per host. The signed tier (checkD3) still excludes a "
                    "call (`e.wasm-α`, Host.hostCall has no arm), a stated signed-tier restriction"
                )
            else:
                status = "partial"
                remaining = (
                    "successor host semantics exists (Wasm/CryptoHost.lean) but allFeatures does "
                    "not dispatch it, or the curve-host fixtures lack a positive and a negative step"
                )
            guard = ("signed tier (checkD3): out-of-domain on a call (e.wasm-α; import allowed); "
                     "allFeatures: dispatched through cryptoHostCall (St.curveHosts)")
        elif name.startswith(CURVE_PREFIXES):
            status = "missing"
            remaining = (
                "curve host: production-enabled at PV86 and reachable; the Lean spec "
                "reports out-of-domain and no arithmetic implementation exists"
            )
            guard = "out-of-domain (curveHosts)"
        elif name in TEST_FEATURES:
            status = "impossible-at-boundary"
            remaining = "test/sandbox feature; not importable in production features"
            guard = "not-enabled-in-production"
        else:
            status = "missing"
            remaining = "no Lean dispatch arm"
            guard = "none"
        if name in crypto_arms:
            lean_sym = f"NearSpecV3.Wasm.CryptoHost.cryptoHostCall \"{name}\" (allFeatures); signed tier: none"
        elif name in arms:
            lean_sym = "NearSpecV3.Wasm.Host.dispatch"
        else:
            lean_sym = "none"
        rows.append(row(
            f"L0-host-{name}", "host", f"{VM}imports.rs:env::{name}",
            lean_sym,
            status, guard,
            _validated(repo, "curve-hosts") if status == "validated" else
            "tools/d3/lean_chunk_coverage.py env_imports vs Wasm/Host.lean and "
            "Wasm/CryptoHost.lean arms",
            "L3" if name.startswith(CURVE_PREFIXES) else "L4", "L0",
            "positive/negative host vector plus exact gas through a real chunk",
            remaining,
        ))

    # --- Instructions ------------------------------------------------------
    rows.append(row(
        "L0-instr-integer", "instruction", "wasmparser integer opcode set",
        "NearSpecV3.Wasm.Decode.isIntNumOp", "implemented", "none",
        f"Decode.lean accepts {len(ops)} numeric opcode bytes",
        "L2", "L0", "generated comparisons per opcode family",
        "coverage count is syntactic; execution agreement is tested, not proved",
    ))
    rows.append(row(
        "L0-instr-float", "instruction", "wasmparser float opcode set",
        "NearSpecV3.Wasm.evalFloatOp", "implemented", "none under NearCfg.floats (default false)",
        "Wasm/Float.lean decides all 70 float opcodes with no immediates (comparisons, abs/neg/"
        "ceil/floor/trunc/nearest/sqrt, add/sub/mul/div/min/max/copysign, the 8 trapping and 8 "
        "saturating truncations, 10 converts, demote/promote, 4 reinterprets) plus loads/stores/"
        "consts in Exec.lean; the signed tier keeps them out of domain via NearCfg.floats = false",
        "L2", "L0",
        "signed zero, subnormal, infinity, NaN payload and rounding-tie cases per opcode",
        "operator semantics anchored to pinned nearcore: 1,260 directed triples through its own "
        "engine plus 210 gas modules (oracle/wasm-d3/tests/float_nearcore.py), and 79,742 "
        "directed cases/seed + 1,120 generated cases total over 4 seeds against the Python IEEE reference; NOT proved "
        "equivalent, and whole-chunk coverage is 26 recorded float chunks",
    ))

    # --- L2 float preparation and execution rows (plan §4 L2) --------------
    fc = float_coverage(repo)
    rows.append(row(
        "L0-W-001", "wasm-prepare", "prepare_v3.rs:303-333 (transform_import_section)",
        "NearSpecV3.Wasm.Prepare (NearCfg.floats)", "implemented",
        "switchable: floatPv86 lifts it",
        "the import-type guard is gated on `!cfg.floats`; floatPv86 lifts it, and the signature "
        "is then checked by Validate.lean's float operand/result types",
        "L2", "L0", "contract importing a float-signature function, never calling it",
        "implemented and directed-tested (oracle/wasm-d3/tests/float_prepare.py: an import-only "
        "f32 and f64 signature, exact gas against nearcore); the signed tier is unchanged because "
        "NearCfg.floats defaults to false",
    ))
    rows.append(row(
        "L0-W-002", "wasm-prepare", "prepare_v3.rs (global section)",
        "NearSpecV3.Wasm.Prepare (NearCfg.floats)", "implemented",
        "switchable: floatPv86 lifts it",
        "the global-section guard is gated on `!cfg.floats`; a float global's initialiser is its "
        "bit pattern (Syntax.ConstE.f32/f64, Exec.evalConst), so the value is byte-exact",
        "L2", "L0", "contract with an f64 global",
        "implemented and directed-tested (float_prepare.py: immutable, mutable and read-then-"
        "dropped f64 globals, exact gas against nearcore); the initialiser is a bit pattern",
    ))
    rows.append(row(
        "L0-W-003", "wasm-prepare", "prepare_v3.rs:397-470 (validate_contract); finite-wasm",
        "NearSpecV3.Wasm.Prepare (NearCfg.floats)", "implemented",
        "switchable: floatPv86 lifts it",
        "the body guard is gated on `!cfg.floats`; the finite-wasm max-stack and gas analyses "
        "handle float operators (FiniteWasm.lean; floatPartial is cvtop_partial)",
        "L2", "L0", "d3float run/cb",
        "implemented for the whole operator set; 20 float-blocked chunks lifted in the d3c9 "
        "whole-chunk test (oracle/wasm-d3/tests/chunk_float.py); 125 float domain moves in the full replay",
    ))
    rows.append(row(
        "L0-W-012", "wasm-exec", "Exec.lean; Validate.lean; FiniteWasm.lean",
        "NearSpecV3.Wasm.execFloat", "implemented", "decided under NearCfg.floats",
        "Exec.lean's `.float` arm calls evalFloatOp, the only float entry point; Validate.lean "
        "gives the signatures; FiniteWasm.lean the stack and gas classification",
        "L2", "L0", "after L2 lifts prepare, exercise each site",
        "all four sites implemented; whole-chunk coverage still uses one float contract; the signed relation is "
        "unchanged (checkD3F is a separate entry point)",
    ))

    # --- Domain guards -----------------------------------------------------
    # These rows record that a *signed-tier* guard exists ("this guard is the exclusion"); they
    # say nothing about allFeatures, which decides what they exclude (rows below).
    guard_notes = {
        "noResharding": ("describes the legacy core's (D3.checkD3Core) two resharding guards; it is "
                         "not a domain condition of RelD3 (the signed hand-over decides such claims) "
                         "nor of allFeatures (ReshardCore decides them). Lives in ReshardingD3.lean"),
        "curveHosts": ("signed-tier list of the 14 curve hosts a call of which is out of domain; "
                       "allFeatures dispatches them (rows L0-host-*)"),
        "floatOutOfDomain": ("signed-tier preparation guard, switchable by NearCfg.floats; "
                             "allFeatures sets floats (rows L0-W-001..003)"),
    }
    for name, present in sorted(guards.items()):
        rows.append(row(
            f"L0-guard-{name}", "domain_guard", f"chunk_validation: {name}",
            f"NearSpecV3.Wasm.{name}" if present else "none",
            "implemented" if present else "missing",
            "this guard *is* the exclusion (signed tier)" if present else "none",
            "tools/d3/lean_chunk_coverage.py domain_guards", "L0", "L0",
            "witness that the guard rejects exactly the excluded set and nothing else",
            "guard presence only; rejection completeness not re-derived here. " + guard_notes.get(name, ""),
        ))

    # --- Resharding / storage boundaries -----------------------------------
    # Three separate axes, because they are separate conditions in the validator and separate
    # rows in the plan: (a) genesis as the main transition, (b) same-layout, (c) split gate.
    # `L0-resharding` is the umbrella row for actual shard-layout *transitions*.
    genesis_mod = repo / LEAN_ROOT / "GenesisD3.lean"
    genesis_src = genesis_mod.read_text() if genesis_mod.exists() else ""
    genesis_done = "def checkD3G" in genesis_src and "MainTransition::Genesis" in genesis_src
    reshard_mod = repo / LEAN_ROOT / "ReshardingD3.lean"
    reshard_src = reshard_mod.read_text() if reshard_mod.exists() else ""
    same_layout_done = "theorem sameLayout_forbids_resharding" in reshard_src
    split_gate_done = "theorem splitGate_excludes_nonempty" in reshard_src

    genesis_valid = genesis_done and sf["genesis"]
    rows.append(row(
        "L0-genesis-main-transition", "boundary",
        "chunk_validation.rs:403-413 MainTransition::Genesis",
        "NearSpecV3.Successor.checkD2CoreGWith (allFeatures, genesisMainTransition); NearSpecV3.checkD3G"
        if genesis_valid else ("NearSpecV3.checkD3G" if genesis_done else "none"),
        "validated" if genesis_valid else ("partial" if genesis_done else "missing"),
        "allFeatures: decided (genesisMainTransition); signed tier (checkD3): out of domain (c.not_genesis)"
        if genesis_valid else "domain extended: genesis B2 is decided, not refused",
        _validated(repo, "genesis") if genesis_valid else
        "GenesisD3.lean models the genesis main transition; 137/137 recorded genesis-B2 cases "
        "accept, matching meta.json expected_rel; 16 directed negatives fire their intended checks",
        "L6", "L0", "genesis B2 with a nonempty witness plus a genesis header negative",
        "none on allFeatures. Genesis-main outputs are the stored genesis chunk extra, a trusted "
        "claim fact (L0-CLAIM-008, bound by admission contract A1), so these chunks are not "
        "blind-gradable. The signed tier keeps c.not_genesis (137 census cases)"
        if genesis_valid else
        "non-genesis delegation is argued by construction and measured over 115284 cases but not "
        "proved as a rewrite theorem; txValid.all is untested (no genesis case has transactions)",
    ))
    decided_by = ("the signed tier hands such claims to the recorder engine "
                  "(D3.withReshardHandover, precondition 1) and allFeatures decides them "
                  "(Successor.checkReshardCoreObs, TrieSplit)"
                  if sf["signedHandover"] and sf["resharding"] else
                  "no checker decides such claims")
    rows.append(row(
        "L0-same-layout", "domain_guard",
        "chunk_validation: c.same_layout (ChunkValidationD2.lean:140)",
        "NearSpecV3.sameLayout" if same_layout_done else "none",
        "implemented" if same_layout_done else "missing",
        "this guard *is* the exclusion (legacy core checkD3Core only)",
        "ReshardingD3.sameLayout_forbids_resharding: guard true => consecutive-epoch layouts equal "
        "=> get_resharding_transition's layout-difference conjunct false",
        "L6", "L0", "a claim whose epochs differ in layout (var/l6/mut/same_layout_broken)",
        f"legacy-core guard only: {decided_by} (row L0-resharding)",
    ))
    rows.append(row(
        "L0-split-gate", "domain_guard",
        "chunk_validation: c.no_split_gate (ChunkValidationD2.lean:156)",
        "NearSpecV3.noSplitGate" if split_gate_done else "none",
        "implemented" if split_gate_done else "missing",
        "this guard *is* the exclusion (legacy core checkD3Core only)",
        "ReshardingD3.noSplitGate_iff + splitGate_excludes_nonempty; splitGate_reachable_at_pv86 "
        "records that mainnet PV85 has dynamic_resharding_config, so the gate is reachable at PV86",
        "L6", "L0", "a claim carrying a mainnet-PV85-shaped split gate (var/l6/mut/split_gate_present)",
        f"legacy-core guard only: {decided_by}; the split gate is recomputed by "
        "Successor/TrieSplit (check_dynamic_resharding, find_trie_split) and checked on "
        "resharding-fixtures-2 threshold gates (row L0-resharding)",
    ))
    reshard_valid = sf["resharding"] and sf["signedHandover"]
    rows.append(row(
        "L0-resharding", "boundary", "validate_chunk_state_witness: layout transitions "
        "(get_resharding_transition, ImplicitTransitionParams::Resharding, chunk_validation.rs:258-308, 702-733)",
        "NearSpecV3.Successor.checkReshardCoreObs (allFeatures); signed tier: NearSpecV3.D3.withReshardHandover"
        if reshard_valid else "NearSpecV3.Wasm.noResharding (ReshardingD3.lean)",
        "validated" if reshard_valid else "missing",
        "allFeatures: decided (resharding); signed tier (checkD3): decided through the hand-over; "
        "legacy core (checkD3Core): out of domain (c.same_layout / c.no_split_gate)"
        if reshard_valid else "out-of-domain (noResharding)",
        _validated(repo, "resharding") if reshard_valid else
        "D2 excludes every layout change and split gate; L6 owns removal",
        "L6", "L0", "validator fixture crossing a real layout boundary",
        "none on allFeatures. Residuals: the signed hand-over's buffer-to-split-parent form has no "
        "fixture (covered by the rule and checkD3_cases; on allFeatures V3 buffer forwarding is "
        "exercised by 3 cross-layout chunks); the raw split runs of resharding-fixtures-2 are no "
        "longer on disk (committed cases remain)"
        if reshard_valid else
        "an actual shard-layout *transition* is unimplemented; only the exclusion arguments for "
        "same-layout and split-gate are in place",
    ))

    # --- allFeatures' remaining named exclusions ---------------------------
    # Gate B asks the inventory to account for every inherited domain guard. On the canonical
    # relation these four are the named out-of-domain reasons that can still fire; each row says
    # why it is not a Gate-B gap (or that it is).
    if sf["prepRace"]:
        rows.append(row(
            "L0-AF-prep-race", "successor-guard",
            "runtime/runtime/src/pipelining.rs:141-315 (preparation pipeline, scheduled from lib.rs:3256-3325); "
            "wasmtime_runner/mod.rs:705-723 (compiled cache first)",
            "NearSpecV3.Successor.CodeResolution (out of domain (e.code_prep_race))",
            "impossible-at-boundary",
            "allFeatures: out of domain (e.code_prep_race)",
            "nearcore's verdict depends on a thread race between the call's pipelined preparation "
            "and the in-chunk deploy that serves its code: no cache-independent relation can decide "
            "it (UQ-001/UQ-002). The generator labels the race by nearcore's own behaviour under two "
            "forced schedules; Lean excludes exactly the 88 races of the code-cache family and the 95 "
            "corpus races (all nearcore-rejected cold). Checked: raceExclusion_isExclusion, "
            "complete_untimely_ood. " + _validated(repo, "code-cache"),
            "L1 + L7", "L0", "w08 code-cache family; corpus e.code_cache cases",
            "not a Gate-B gap (nearcore nondeterminism is a named exclusion, never an accept). "
            "Residual: 27 conservative exclusions on `code.none` mutants whose nearcore verdict is "
            "reject under both schedules (only the failure point races): a decidable reject reported "
            "as excluded (w08-warm-cache §4; workplan item 7 residual)",
        ))
    if sf["codeResponse"]:
        rows.append(row(
            "L0-AF-code-response", "successor-guard",
            "chain/client/src/stateless_validation/contract_distribution.rs:372-373 "
            "(MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE = 64 MiB); partial_witness_tracker.rs:45-48",
            "NearSpecV3.Successor.RuntimeCore / ReshardCore (out of domain (w.code_response_size))",
            "impossible-at-boundary",
            "allFeatures: out of domain (w.code_response_size)",
            "above 64 MiB of cold-fetched code nearcore drops the ContractCodeResponse and its "
            "verdict depends on the validator's compiled cache (cold: MissingTrieValue, warm: ok). "
            "size-limit-fixtures (seed 2029): at64 accept/accept, over64 out of domain, under64 "
            f"accept/accept. Evidence: {EV}size-limit-fixtures/README.md",
            "L5", "L0", "at/over/under 64 MiB code-response chunks",
            "not a Gate-B gap (cache-dependent nearcore verdict). Residual: one seed, no mutants of "
            "the 64 MiB chunks (workplan item 4 residual)",
        ))
    if sf["fuelCert"]:
        rows.append(row(
            "L0-AF-fuel-certificate", "successor-guard",
            "near-vm-runner gas accounting (every prepared function is gas-metered; finite-wasm)",
            "NearSpecV3.Successor.StorageExecution.vmCall (out of domain (e.wasm-α): w.fuel_certificate)",
            "implemented",
            "allFeatures: out of domain (w.fuel_certificate) when a prepared function fails the certificate",
            "kept out-of-domain reason by decision (workplan, decisions in force): it makes "
            "functionCall_fuel_sufficient's CodeCertified hypothesis a checked condition; it fires on "
            f"no corpus module. Evidence: {EV}fuel-sufficiency/README.md",
            "L1", "L0", "a module that fails the certificate (none known)",
            "not blocking by the 2026-10-31 decision; a general proof of CodeCertified would make the "
            "guard provably dead (workplan item 3 residual)",
        ))
    if sf["globalIdentity"]:
        rows.append(row(
            "L0-AF-global-code-identity", "successor-guard",
            "runtime/runtime/src/global_contracts.rs:162-195,317-353 (distribution receipts built from "
            "the deployed code; forward copies id/code/nonce)",
            "NearSpecV3.Successor.GlobalExecution (out of domain (w.shape): global_code_identity)",
            "impossible-at-boundary",
            "allFeatures: out of domain (w.shape: global_code_identity)",
            "source-backed unreachability: every distribution receipt's CodeHash id is sha256 of its "
            "code by construction, and incoming/delayed/buffered receipts are bound by receipt proofs "
            "and the applied-receipts hash. dist-identity mutants (8 seeds, 1,027 rows, 0 "
            "disagreements); C-D2 shows the guard is reached only when both bindings are skipped. "
            f"Evidence: {EV}remaining-shapes/README.md",
            "L4", "L0", "dist-identity mutants",
            "not a Gate-B gap (no valid chunk reaches it)",
        ))

    # L0 execution/boundary analysis (lifted into tools/d3/lean_chunk_coverage_l0.py so this
    # drift gate covers it too), then reconciled against the canonical relation.
    extra = _l0_supplement()
    existing_ids = {r["id"] for r in rows}
    rows.extend(reconcile_l0(repo, sf, r) for r in extra["rows"] if r["id"] not in existing_ids)
    rows = [promote_row(repo, r) for r in rows]
    status = {r["id"]: r["status"] for r in rows}
    rows = [promote_subsumed(repo, r, status) for r in rows]
    ids = [r["id"] for r in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate coverage row id")

    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    families = {}
    for r in rows:
        families[r["family"]] = families.get(r["family"], 0) + 1

    out = {
        "schema": "near-lean-chunk-coverage-v2",
        "nearcore_commit": PIN,
        "protocol_version": PV,
        "evidence": (
            "static reconciliation of pinned nearcore git objects against Lean dispatch "
            "tables; no execution, differential testing or proof"
        ),
        "counts": dict(sorted(counts.items())),
        "totals": {
            "rows": len(rows),
            "nearcore_env_imports": len(env_names),
            "lean_host_arms": len(arms),
            "lean_crypto_host_arms": len(crypto_arms),
            "nearcore_action_tags": len(tags),
            "lean_decoded_action_tags": len(ok_tags),
            "lean_numeric_opcodes": len(ops),
        },
        "source_sha256": {
            p: hashlib.sha256((Path(repo) / LEAN_ROOT / p).read_bytes()).hexdigest()
            for p in LEAN_FILES + extra["lean_files"]
        },
        "row_families": dict(sorted(families.items())),
        "rows": rows,
    }
    out.update(extra["sections"])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path, help="nearproof checkout")
    ap.add_argument("--nearcore", required=True, type=Path, help="pinned nearcore checkout")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--check", type=Path)
    args = ap.parse_args()
    expected = json.dumps(inventory(args.repo, args.nearcore), sort_keys=True, indent=2) + "\n"
    if args.check:
        if args.check.read_text() != expected:
            ap.exit(1, "Lean chunk coverage differs from source; regenerate and review\n")
        print("Lean chunk coverage matches pinned sources (research evidence only)")
    else:
        args.output.write_text(expected)
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
