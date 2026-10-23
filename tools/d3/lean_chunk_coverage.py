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
from pathlib import Path

PIN = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
PV = 86
ACTION_MOD = "core/primitives/src/action/mod.rs"
VM = "runtime/near-vm-runner/src/"
LEAN_ROOT = "spec/lean/v3/NearSpecV3"

# Lean files whose dispatch tables define the "implemented" side.
LEAN_FILES = [
    "Wasm/Host.lean",
    "Wasm/Exec.lean",
    "Wasm/Decode.lean",
    "Wasm/Syntax.lean",
    "Wasm/DomainD3.lean",
    "Wasm/Prepare.lean",
    "D2/Types.lean",
    "D2/Actions.lean",
]

# Host families whose absence is a real semantic gap rather than a boundary exclusion.
CURVE_PREFIXES = ("alt_bn128_", "bls12381_", "ecrecover", "p256_verify")
TEST_FEATURES = ("sandbox_debug_log", "sleep_nanos", "burn_gas")


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


def domain_guards(repo):
    """Named domain guards the plan asks L0 to enumerate."""
    dom = (repo / LEAN_ROOT / "Wasm/DomainD3.lean").read_text()
    syn = (repo / LEAN_ROOT / "Wasm/Syntax.lean").read_text()
    return {
        "noResharding": "def noResharding" in dom,
        "contractInD3alpha": "contractInD3" in dom,
        "curveHosts": "def curveHosts" in (repo / LEAN_ROOT / "Wasm/Exec.lean").read_text(),
        "floatOutOfDomain": "float (out of domain)" in syn or "float (out of domain)" in dom,
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
        else:
            status = "missing"
            remaining = "no Lean decode arm"
            guard = "undecoded"
        rows.append(row(
            f"L0-action-{t:02d}", "action", f"{ACTION_MOD}:{name} = {t}",
            "NearSpecV3.D2.Types.pBase" if t in ok_tags else "none",
            status, guard,
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
        rows.append(row(
            f"L0-host-{name}", "host", f"{VM}imports.rs:env::{name}",
            "NearSpecV3.Wasm.Host.dispatch" if name in arms else "none",
            status, guard,
            "tools/d3/lean_chunk_coverage.py env_imports vs Wasm/Host.lean arms",
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
        "NearSpecV3.Wasm.Instr.float", "missing", "out-of-domain (float)",
        "Decode.lean parses float opcodes only to reject them; Exec.lean returns "
        "unmodeled 'float (out of domain)'",
        "L2", "L0", "every f32/f64 opcode with signed zero, subnormal, NaN payload cases",
        "no float semantics exist; this is L2's whole deliverable",
    ))

    # --- Domain guards -----------------------------------------------------
    for name, present in sorted(guards.items()):
        rows.append(row(
            f"L0-guard-{name}", "domain_guard", f"chunk_validation: {name}",
            f"NearSpecV3.Wasm.DomainD3.{name}" if present else "none",
            "implemented" if present else "missing",
            "this guard *is* the exclusion" if present else "none",
            "tools/d3/lean_chunk_coverage.py domain_guards", "L0", "L0",
            "witness that the guard rejects exactly the excluded set and nothing else",
            "guard presence only; rejection completeness not re-derived here",
        ))

    # --- Resharding / storage boundaries -----------------------------------
    rows.append(row(
        "L0-resharding", "boundary", "validate_chunk_state_witness: layout transitions",
        "NearSpecV3.Wasm.DomainD3.noResharding", "missing", "out-of-domain (noResharding)",
        "D2 excludes every layout change and split gate; L6 owns removal",
        "L6", "L0", "validator fixture crossing a real layout boundary",
        "shard-layout transitions, split gates and resharding witness processing unimplemented",
    ))

    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1

    return {
        "schema": "near-lean-chunk-coverage-v1",
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
            "nearcore_action_tags": len(tags),
            "lean_decoded_action_tags": len(ok_tags),
            "lean_numeric_opcodes": len(ops),
        },
        "source_sha256": {
            p: hashlib.sha256((Path(repo) / LEAN_ROOT / p).read_bytes()).hexdigest()
            for p in LEAN_FILES
        },
        "rows": rows,
    }


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
