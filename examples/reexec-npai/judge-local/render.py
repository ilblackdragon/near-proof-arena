#!/usr/bin/env python3
"""LOCAL EMULATION of the judge's Expected-module generation for the npai-v1
(approved interpreter) route (runners/formal-checker `TemplateExpected` with
spec/lean/judge/Expected.lean.template).

Writes judge-local/out/ArenaExpected.lean with the digests of the given
public.bin and verifier.npai. Used only for local `lake build` of the
certificate; the real judge renders its own file.

usage: render.py PUBLIC_BIN VERIFIER_NPAI
"""
import hashlib, os, sys

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.abspath(os.path.join(here, "..", "..", ".."))
pub = open(sys.argv[1], "rb").read()
img = open(sys.argv[2], "rb").read()

def lst(b):
    return "[" + ", ".join("0x%02x" % x for x in b) + "]"

tmpl = open(os.path.join(repo, "spec/lean/judge/Expected.lean.template")).read()
data = {
    "profile_id": '"validity-classical-128"',
    "profile_model": '"random_oracle"',
    "target_bits": "(128 : Nat)",
    "assumption_0": '"sha256-collision-resistance"',
    "assumption_1": '"random-oracle-fiat-shamir-sha256"',
    "max_prover_queries_log2": "(40 : Nat)",
    "max_hash_queries_log2": "(64 : Nat)",
    "verify_fuel": "(1073741824 : Nat)",
    "max_proof_bytes": "(8388608 : Nat)",
    "max_reduction_fuel": "(1073741824 : Nat)",
    "public_digest": lst(hashlib.sha256(pub).digest()),
    "verifier_digest": lst(hashlib.sha256(img).digest()),
}
for k, v in data.items():
    tmpl = tmpl.replace("{{%s}}" % k, v)
assert "{{" not in tmpl, tmpl
out = os.path.join(here, "out")
os.makedirs(out, exist_ok=True)
open(os.path.join(out, "ArenaExpected.lean"), "w").write(tmpl)
print("rendered", out)
