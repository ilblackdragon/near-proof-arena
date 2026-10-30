#!/usr/bin/env python3
"""Build the Lean chunk-transition coverage inventory (plan §4 L0).

This is research/accounting tooling. It reconciles the *pinned* nearcore surface
(action tags and host imports read from git objects, never a dirty checkout)
against the Lean specification's actual dispatch tables, and emits one row per
boundary item with the fields the plan requires:

    id, family, nearcore_commit, nearcore_path_symbol, lean_path_symbol, status,
    domain_guard, evidence, owner, dependencies, acceptance_tests, remaining_work

Statuses are limited to the plan's vocabulary: implemented, partial, missing,
impossible-at-boundary, validated. Nothing here is a proof or a conformance test;
a row marked `implemented` means "Lean has a dispatch arm for this name", not "this
behaviour was tested against nearcore".

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
    # `Wasm/DomainD3.lean` was retired 2026-10-29 (UQ-010); `noResharding` now lives in ReshardingD3.lean.
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
]

# Host families whose absence is a real semantic gap rather than a boundary exclusion.
CURVE_PREFIXES = ("alt_bn128_", "bls12381_", "ecrecover", "p256_verify")
TEST_FEATURES = ("sandbox_debug_log", "sleep_nanos", "burn_gas")


# --- L4: additive bodies for the three global-contract actions -----------------
# Each of these tags has a pinned codec, storage charge and action body in
# D3/GlobalContract.lean / D3/GlobalContractExec.lean with directed #guard tests in
# D3/GlobalContractTests.lean. None can be carried by a whole chunk yet: `D2.Base`
# is closed, so `pBase` (D2/Types.lean:299-302) rejects them before any action runs,
# and widening it changes the signed near-chunk-v3 format. Status is therefore
# `partial`, not `implemented`, and the whole-chunk acceptance test is unmet.
L4_ACTION_ROWS = {
    9: (
        "implemented additively (codec pDeployGlobal, storage charge "
        "`0.0001 N/byte * code.len()` = global_contract_storage_per_byte, fee, "
        "LackBalanceForState on insufficient balance, distribution receipt); "
        "whole-chunk acceptance blocked: pBase:299 rejects the tag and D2.Base is closed"
    ),
    10: (
        "implemented additively (codec pUseGlobal, Gci.len 32/account-id length, "
        "global-contract key read, local-code removal, storage refund); "
        "whole-chunk acceptance blocked: pBase:300 rejects the tag and D2.Base is closed"
    ),
    11: (
        "implemented additively (codec pDsi, deterministic account id "
        "`sha256`-based derivation, 0-balance/100-usage account, storage charge); "
        "whole-chunk acceptance blocked: pBase:302 rejects the tag and D2.Base is closed"
    ),
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

    These are still out of domain in D3α (`Host.hostCall` has no arm for them, and
    `D3/CryptoDomain.hostCall_no_arm` checks that), so having an arm here is `partial`: the host
    semantics exists, but the whole-chunk path is unchanged and no whole-chunk case exercises it.

    `alt_bn128_*` is included: its arithmetic/codec lives in `NearSpecV3/AltBn128.lean` and its
    three arms are in the same `cryptoHostCall` table, so the same reading applies. Only the
    *payload* file differs; the arm's presence in the table is what this function reports.
    """
    src = (repo / LEAN_ROOT / "Wasm/CryptoHost.lean").read_text()
    block = src.split("def cryptoHostCall", 1)[1]
    return sorted(set(re.findall(r'^\s*\| "([a-z0-9_]+)" => some', block, re.MULTILINE)))


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
    # `Wasm/DomainD3.lean` was retired 2026-10-29 (UQ-010): `noResharding` moved to ReshardingD3.lean
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
        elif t in ood_map:
            status = "missing"
            remaining = (
                "decoder rejects this tag as out of domain; implement codec plus "
                "execution, then remove the exclusion"
            )
            guard = f"out-of-domain ({ood_map[t]})"
            # L4: tags 9/10/11 have an additive implementation (codec, fee, storage
            # charge and action body in D3/GlobalContract{,Exec}.lean) but the D2
            # `Base` type is closed, so `pBase`/`pRcpt`/`pTxD2` still reject them and
            # no whole chunk can carry one. Honest status: partial, not implemented.
            if t in L4_ACTION_ROWS:
                status = "partial"
                remaining = L4_ACTION_ROWS[t]
                guard = f"out-of-domain ({ood_map[t]}) in checkD3/checkD2; accepted only in a widened-Base successor"
        else:
            status = "missing"
            remaining = "no Lean decode arm"
            guard = "undecoded"
        rows.append(row(
            f"L0-action-{t:02d}", "action", f"{ACTION_MOD}:{name} = {t}",
            "NearSpecV3.D3.GlobalContractExec.BaseL4" if t in L4_ACTION_ROWS
            else ("NearSpecV3.D2.Types.pBase" if t in ok_tags else "none"),
            status, guard,
            "tools/d3/lean_chunk_coverage.py action_tags vs D2/Types.lean pBase; "
            "L4 additive bodies in D3/GlobalContractExec.lean"
            if t in L4_ACTION_ROWS else
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
            status = "partial"
            remaining = (
                "successor-domain host semantics exists (Wasm/CryptoHost.lean); D3α still "
                "reports it out of domain (Host.hostCall has no arm), and no whole-chunk case "
                "runs it — see docs/research/lean-chunk-crypto-L3.md"
            )
            guard = "out-of-domain (curveHosts) in D3α; modelled in the D3γ table"
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
            lean_sym = f"NearSpecV3.Wasm.CryptoHost.{name} (successor table); D3α: none"
        elif name in arms:
            lean_sym = "NearSpecV3.Wasm.Host.dispatch"
        else:
            lean_sym = "none"
        rows.append(row(
            f"L0-host-{name}", "host", f"{VM}imports.rs:env::{name}",
            lean_sym,
            status, guard,
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
        "consts in Exec.lean; D3α keeps them out of domain via NearCfg.floats = false",
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
        "f32 and f64 signature, exact gas against nearcore); D3alpha is unchanged because "
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
        "all four sites implemented; whole-chunk coverage still uses one float contract; the D3alpha relation is "
        "unchanged (checkD3F is a separate entry point)",
    ))

    # --- Domain guards -----------------------------------------------------
    for name, present in sorted(guards.items()):
        rows.append(row(
            f"L0-guard-{name}", "domain_guard", f"chunk_validation: {name}",
            f"NearSpecV3.Wasm.{name}" if present else "none",
            "implemented" if present else "missing",
            "this guard *is* the exclusion" if present else "none",
            "tools/d3/lean_chunk_coverage.py domain_guards", "L0", "L0",
            "witness that the guard rejects exactly the excluded set and nothing else",
            "guard presence only; rejection completeness not re-derived here",
        ))

    # --- Resharding / storage boundaries -----------------------------------
    # Three separate axes, because they are separate conditions in the validator and separate
    # rows in the plan: (a) genesis as the main transition, (b) same-layout, (c) split gate.
    # `L0-resharding` stays as the umbrella row for actual shard-layout *transitions*.
    genesis_mod = repo / LEAN_ROOT / "GenesisD3.lean"
    genesis_src = genesis_mod.read_text() if genesis_mod.exists() else ""
    genesis_done = "def checkD3G" in genesis_src and "MainTransition::Genesis" in genesis_src
    reshard_mod = repo / LEAN_ROOT / "ReshardingD3.lean"
    reshard_src = reshard_mod.read_text() if reshard_mod.exists() else ""
    same_layout_done = "theorem sameLayout_forbids_resharding" in reshard_src
    split_gate_done = "theorem splitGate_excludes_nonempty" in reshard_src

    rows.append(row(
        "L0-genesis-main-transition", "boundary",
        "chunk_validation.rs:403-413 MainTransition::Genesis",
        "NearSpecV3.checkD3G" if genesis_done else "none",
        "partial" if genesis_done else "missing",
        "domain extended: genesis B2 is decided, not refused",
        "GenesisD3.lean models the genesis main transition; 137/137 recorded genesis-B2 cases "
        "accept, matching meta.json expected_rel; 16 directed negatives fire their intended checks",
        "L6", "L0", "genesis B2 with a nonempty witness plus a genesis header negative",
        "non-genesis delegation is argued by construction and measured over 115284 cases but not "
        "proved as a rewrite theorem; txValid.all is untested (no genesis case has transactions)",
    ))
    rows.append(row(
        "L0-same-layout", "domain_guard",
        "chunk_validation: c.same_layout (ChunkValidationD2.lean:140)",
        "NearSpecV3.sameLayout" if same_layout_done else "none",
        "implemented" if same_layout_done else "missing",
        "this guard *is* the exclusion",
        "ReshardingD3.sameLayout_forbids_resharding: guard true => consecutive-epoch layouts equal "
        "=> get_resharding_transition's layout-difference conjunct false",
        "L6", "L0", "a claim whose epochs differ in layout (var/l6/mut/same_layout_broken)",
        "an argument, not an implementation: the epoch table is taken as the layout source of truth "
        "(spec/claim-v3.md T6); no whole-witness positive crossing a real boundary exists",
    ))
    rows.append(row(
        "L0-split-gate", "domain_guard",
        "chunk_validation: c.no_split_gate (ChunkValidationD2.lean:156)",
        "NearSpecV3.noSplitGate" if split_gate_done else "none",
        "implemented" if split_gate_done else "missing",
        "this guard *is* the exclusion",
        "ReshardingD3.noSplitGate_iff + splitGate_excludes_nonempty; splitGate_reachable_at_pv86 "
        "records that mainnet PV85 has dynamic_resharding_config (0 corpus claims carry a gate)",
        "L6", "L0", "a claim carrying a mainnet-PV85-shaped split gate (var/l6/mut/split_gate_present)",
        "exclusion only: the gate IS reachable at PV86 on mainnet (version.rs:564 enables "
        "DynamicResharding at PV85, mainnet/85.json sets dynamic_resharding_config), so this is "
        "not a proven impossibility and D3 declines to decide such claims",
    ))
    rows.append(row(
        "L0-resharding", "boundary", "validate_chunk_state_witness: layout transitions",
        "NearSpecV3.Wasm.DomainD3.noResharding", "missing", "out-of-domain (noResharding)",
        "D2 excludes every layout change and split gate; L6 owns removal",
        "L6", "L0", "validator fixture crossing a real layout boundary",
        "an actual shard-layout *transition* (split shard retained left/right, ImplicitTransitionParams::"
        "Resharding at chunk_validation.rs:702-733) is still unimplemented; only the exclusion "
        "arguments for same-layout and split-gate are in place",
    ))

    # L0 execution/boundary analysis (docs/research/lean-chunk-coverage-gen.py logic,
    # lifted into tools/d3/lean_chunk_coverage_l0.py so this drift gate covers it too).
    extra = _l0_supplement()
    existing_ids = {r["id"] for r in rows}
    rows.extend(r for r in extra["rows"] if r["id"] not in existing_ids)
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
