#!/usr/bin/env python3
"""Write `params.bin` (`near-arena-params-v3`, spec/claim-v3.md §4) for a domain.

  params_bin_v3.py OUT [DOMAIN]        (DOMAIN default D0)

params.bin = bytes "near-arena-params-v3" ‖ bytes "near/pv86/chunk-validation/v0" ‖ u32 86
           ‖ bytes domain_id ‖ hash runtime_config_digest_v3
runtime_config_digest_v3 = sha256(JCS(runtime-config description)), the challenge's
`runtime_config_digest` (spec/tools/build_challenge_draft_v3*.py compute it the same way). The
description is per domain (CONFIGS): D0 `runtime-config-pv86-v3.json`; D1 `-v3-d1.json` (+ the
transaction fees D1 reads); D2, D3 and D3a (`near-chunk-v3`) `-v3-d2.json` (+ every fee, limit and parameter the D2
relation reads, and `runtime_config_view_sha256` = sha256 of nearcore's whole `RuntimeConfigView`
at PV 86, which covers the WASM config D3 reads; `near-arena-oracle-v3-d1 params --d1 --d2`).
"""
import hashlib, json, os, struct, subprocess, sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True, cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()

def jcs(v): return json.dumps(v, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
def b(s): s = s.encode(); return struct.pack("<I", len(s)) + s

CONFIGS = {"D0": "spec/challenge-inputs/runtime-config-pv86-v3.json",
           "D1": "spec/challenge-inputs/runtime-config-pv86-v3-d1.json",
           "D2": "spec/challenge-inputs/runtime-config-pv86-v3-d2.json",
           "D3": "spec/challenge-inputs/runtime-config-pv86-v3-d2.json",
           "D3a": "spec/challenge-inputs/runtime-config-pv86-v3-d2.json"}

def params_bin(domain="D0"):
    rc = json.load(open(os.path.join(ROOT, CONFIGS[domain])))
    digest = hashlib.sha256(jcs(rc).encode()).digest()
    return (b("near-arena-params-v3") + b("near/pv86/chunk-validation/v0") + struct.pack("<I", 86)
            + b(domain) + digest)

if __name__ == "__main__":
    out = sys.argv[1]
    domain = sys.argv[2] if len(sys.argv) > 2 else "D0"
    data = params_bin(domain)
    open(out, "wb").write(data)
    print(out, len(data), "bytes, runtime_config_digest sha256:" + data[-32:].hex())
