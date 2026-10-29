#!/usr/bin/env python3
"""UQ-004: are the curve (and other crypto) host-function gas schedules fully pinned at PV86?

nearcore has no `86.yaml`. This script establishes, from the pinned source alone, which parameter
values the PV86 validator uses and checks that every Lean crypto-host cost constant equals them:

1. `RuntimeConfigStore::get_config(pv)` returns the entry with the largest key `<= pv`
   (`core/parameters/src/config_store.rs:240-248`). The keys are 0 and the versions listed in
   `CONFIG_DIFFS` (`config_store.rs:26-66`); the script parses that list and checks that the largest
   key `<= 86` is 85, i.e. PV86 uses the table "base + every diff up to 85".
2. It rebuilds that table independently from `parameters.yaml` and the diff files (the same
   `old`/`new` application as `ParameterTable::apply_diff`) and checks it against
   `parameters.snap`, which nearcore's own `test_json_unchanged` regenerates from
   `CONFIG_DIFFS` filtered to `<= PROTOCOL_VERSION` (= 86, `config_store.rs:402-418`).
3. It checks every Lean constant in `TABLE` (gas and compute) against that table, plus the
   feature flags the crypto hosts depend on.

`--break NAME` perturbs one Lean value in memory: the check must then fail (deliberate-breakage
control). Exit 0 only when every comparison holds.
"""
import argparse
import re
import sys
from pathlib import Path

import yaml

REPO = Path(__file__).resolve().parents[2]
NEARCORE = Path("/data/illia/nearproof-deps/nearcore")
PIN = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
CFG = "core/parameters/res/runtime_configs"
LEAN = REPO / "spec/lean/v3/NearSpecV3/Wasm"

# Lean constant -> (file, nearcore parameter). Each Lean constant is `⟨gas, compute, key⟩`.
TABLE = {
    "ecrecoverBase": ("CryptoHost.lean", "wasm_ecrecover_base"),
    "p256VerifyBase": ("CryptoHost.lean", "wasm_p256_verify_base"),
    "p256VerifyByte": ("CryptoHost.lean", "wasm_p256_verify_byte"),
    "ed25519VerifyBase": ("Machine.lean", "wasm_ed25519_verify_base"),
    "ed25519VerifyByte": ("Machine.lean", "wasm_ed25519_verify_byte"),
    "p1SumBase": ("CryptoHost.lean", "wasm_bls12381_p1_sum_base"),
    "p1SumElement": ("CryptoHost.lean", "wasm_bls12381_p1_sum_element"),
    "p2SumBase": ("CryptoHost.lean", "wasm_bls12381_p2_sum_base"),
    "p2SumElement": ("CryptoHost.lean", "wasm_bls12381_p2_sum_element"),
    "g1MultiexpBase": ("CryptoHost.lean", "wasm_bls12381_g1_multiexp_base"),
    "g1MultiexpElement": ("CryptoHost.lean", "wasm_bls12381_g1_multiexp_element"),
    "g2MultiexpBase": ("CryptoHost.lean", "wasm_bls12381_g2_multiexp_base"),
    "g2MultiexpElement": ("CryptoHost.lean", "wasm_bls12381_g2_multiexp_element"),
    "mapFpToG1Base": ("CryptoHost.lean", "wasm_bls12381_map_fp_to_g1_base"),
    "mapFpToG1Element": ("CryptoHost.lean", "wasm_bls12381_map_fp_to_g1_element"),
    "mapFp2ToG2Base": ("CryptoHost.lean", "wasm_bls12381_map_fp2_to_g2_base"),
    "mapFp2ToG2Element": ("CryptoHost.lean", "wasm_bls12381_map_fp2_to_g2_element"),
    "pairingBase": ("CryptoHost.lean", "wasm_bls12381_pairing_base"),
    "pairingElement": ("CryptoHost.lean", "wasm_bls12381_pairing_element"),
    "p1DecompressBase": ("CryptoHost.lean", "wasm_bls12381_p1_decompress_base"),
    "p1DecompressElement": ("CryptoHost.lean", "wasm_bls12381_p1_decompress_element"),
    "p2DecompressBase": ("CryptoHost.lean", "wasm_bls12381_p2_decompress_base"),
    "p2DecompressElement": ("CryptoHost.lean", "wasm_bls12381_p2_decompress_element"),
    "altBn128G1MultiexpBase": ("CryptoHost.lean", "wasm_alt_bn128_g1_multiexp_base"),
    "altBn128G1MultiexpElement": ("CryptoHost.lean", "wasm_alt_bn128_g1_multiexp_element"),
    "altBn128G1SumBase": ("CryptoHost.lean", "wasm_alt_bn128_g1_sum_base"),
    "altBn128G1SumElement": ("CryptoHost.lean", "wasm_alt_bn128_g1_sum_element"),
    "altBn128PairingBase": ("CryptoHost.lean", "wasm_alt_bn128_pairing_check_base"),
    "altBn128PairingElement": ("CryptoHost.lean", "wasm_alt_bn128_pairing_check_element"),
}
def lean_flags():
    """Feature flags the crypto/wallet hosts depend on, as the Lean model fixes them (read from the
    Lean sources, not restated here)."""
    host = (LEAN / "HostSigs.lean").read_text()
    crypto = (LEAN / "CryptoHost.lean").read_text()
    gc = (REPO / "spec/lean/v3/NearSpecV3/D3/GlobalContract.lean").read_text()
    ver = re.search(r"^def bls12381Version : Nat := (\d+)", crypto, re.M)
    eth = re.search(r"^def ethImplicitGlobalContractPv86 : Bool := (true|false)", gc, re.M)
    assert ver and eth, "Lean flag definitions not found"
    return {
        # `p256_verify` is in the PV86 production import table iff the host fn is enabled.
        "p256_verify_host_fn": '("p256_verify",' in host,
        # `bls12381Version = 0` is the pre-NEP-488 behaviour (fix off), `logic/bls12381.rs:17-28`.
        "bls12381_not_in_group_fix": int(ver.group(1)) != 0,
        "eth_implicit_global_contract": eth.group(1) == "true",
    }


def diff_versions(src):
    return [int(v) for v in re.findall(r"\((\d+), include_config!\(\"\d+\.yaml\"\)\)", src)]


def gas_compute(v):
    if isinstance(v, dict) and "gas" in v:
        return int(v["gas"]), int(v.get("compute", v["gas"]))
    if isinstance(v, (bool, dict)):
        return v
    return (int(v), int(v)) if isinstance(v, int) else v


def build_table(root, upto):
    params = yaml.safe_load((root / "parameters.yaml").read_text())
    for ver in upto:
        diff = yaml.safe_load((root / f"{ver}.yaml").read_text()) or {}
        for k, ch in diff.items():
            if gas_compute(params.get(k)) != gas_compute(ch.get("old")):
                raise SystemExit(f"{ver}.yaml: {k} old={ch['old']!r} != current {params[k]!r}")
            params[k] = ch["new"]
    return params


def parse_snap(text):
    out = {}
    for ln in text.splitlines():
        m = re.match(r"^([a-z0-9_]+)\s+(.+?)\s*$", ln)
        if m:
            out[m.group(1)] = m.group(2)
    return out


def snap_value(s):
    s = s.strip()
    if s in ("true", "false"):
        return s == "true"
    m = re.match(r"^([\d_]+)(?:,\s*compute:\s*([\d_]+))?$", s)
    if m:
        g = int(m.group(1).replace("_", ""))
        return (g, int(m.group(2).replace("_", "")) if m.group(2) else g)
    return s


def lean_costs():
    vals = {}
    for name, (fname, _) in TABLE.items():
        src = (LEAN / fname).read_text()
        m = re.search(rf"^def {name} : Cost := ⟨(\d+), (\d+), (none|some \d+)⟩", src, re.M)
        if not m:
            raise SystemExit(f"Lean constant {name} not found in {fname}")
        vals[name] = (int(m.group(1)), int(m.group(2)))
    return vals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nearcore", default=str(NEARCORE))
    ap.add_argument("--break", dest="brk", help="perturb this Lean constant (control)")
    a = ap.parse_args()
    nc = Path(a.nearcore)
    head = (nc / ".git").exists() and __import__("subprocess").run(
        ["git", "-C", str(nc), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head != PIN:
        raise SystemExit(f"nearcore at {head!r}, expected {PIN}")
    versions = diff_versions((nc / "core/parameters/src/config_store.rs").read_text())
    upto = [v for v in versions if v <= 86]
    assert versions == sorted(versions) and len(versions) > 20, versions
    assert max(upto) == 85 and 86 not in versions, ("PV86 config key", max(upto))
    later = [v for v in versions if v > 86]
    table = build_table(nc / CFG, upto)
    snap = parse_snap((nc / CFG / "parameters.snap").read_text())
    lean = lean_costs()
    if a.brk:
        g, c = lean[a.brk]
        lean[a.brk] = (g + 1, c)
    failures = []
    rows = []
    for name, (_, key) in TABLE.items():
        built, snapv = gas_compute(table[key]), snap_value(snap[key])
        ok = built == snapv == lean[name]
        rows.append((key, built, snapv, lean[name], ok))
        if not ok:
            failures.append((name, key, built, snapv, lean[name]))
    for key, want in lean_flags().items():
        built, snapv = table[key], snap_value(snap[key])
        ok = built == snapv == want
        rows.append((key, built, snapv, want, ok))
        if not ok:
            failures.append((key, key, built, snapv, want))
    print(f"CONFIG_DIFFS keys <= 86: max {max(upto)}; keys > 86 (not applied): {later}")
    for key, built, snapv, lv, ok in rows:
        print(f"{'ok ' if ok else 'BAD'} {key:42s} built={built} snap={snapv} lean={lv}")
    print(f"{len(rows) - len(failures)}/{len(rows)} pinned values agree")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
