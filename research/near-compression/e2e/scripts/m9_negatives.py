#!/usr/bin/env python3
"""E2E-D M9: fresh-process cross-setup negatives (a real-leaf tree vs. the M8 stub tree).

    m9_negatives.py PROVER M9_TREE_DIR OUT_DIR [M8_TREE_DIR]

Both packets are for T1 (same S, same ctx). The M8 packet's tree has stub INIT / FINAL (and no rt
leaves); the M9 setup's template set lists only real leaves. Each case runs `m8-verify` in a new
process and must exit non-zero with HTREE_VERIFY_REJECT:
  * the M8 stub-leaf packet against the M9 setup (pinned);
  * the M9 packet against the M8 setup (pinned);
  * the M9 packet with its S replaced by the M8 bundle's S (byte-identical: control that S is the same)
    must be ACCEPTED (so the two rejections above are about the tree, not the statement).
The constraint-level swap (a stub exposing a real leaf's exact statement, refused by P_2 under the
run's template set) is `run_m9.sh swap` (M9_SWAP_STUB).
"""
import os, subprocess, sys
from pathlib import Path

P, T, O = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
M8 = Path(sys.argv[4]) if len(sys.argv) > 4 else Path(__file__).resolve().parent.parent / "results/zk/m8/t1real/tree"
O.mkdir(parents=True, exist_ok=True)

def verify(setup, pin, bundle):
    r = subprocess.run([P, "m8-verify", str(setup), pin, str(bundle)], capture_output=True, text=True, env=dict(os.environ, RAYON_NUM_THREADS="1"))
    out = (r.stdout + r.stderr).strip()
    return r.returncode, out, out.splitlines()[-1] if out else ""

pin9 = (T / "SETUP.sha256").read_text().strip()
pin8 = (M8 / "SETUP.sha256").read_text().strip()
b9, b8 = (T / "WRAP.bundle").read_bytes(), (M8 / "WRAP.bundle").read_bytes()
n9, n8 = int.from_bytes(b9[8:12], "little"), int.from_bytes(b8[8:12], "little")
assert b9[:12 + n9] == b8[:12 + n8], "the M8 and M9 packets carry different statements S"
rc, out, last = verify(T / "SETUP.json", pin9, T / "WRAP.bundle")
assert rc == 0 and "INDEPENDENT_HTREE_VERIFY_OK" in out, "the honest M9 packet is rejected"
print("ACCEPTED M9 packet under the M9 setup (control; S identical to the M8 packet's)")
cases = [("M8 stub-leaf packet vs M9 setup", T / "SETUP.json", pin9, M8 / "WRAP.bundle"),
         ("M9 packet vs M8 (stub) setup", M8 / "SETUP.json", pin8, T / "WRAP.bundle")]
ok = 0
for name, s, p, b in cases:
    rc, out, last = verify(s, p, b)
    r = rc != 0 and "HTREE_VERIFY_REJECT" in out and "panicked" not in out
    ok += r
    print(f"{'REJECTED' if r else 'NOT_REJECTED'} {name}: rc={rc} {last}")
print(f"M9_NEGATIVES {ok}/{len(cases)} rejected")
if ok == len(cases):
    print(f"M9_NEGATIVES_ALL_REJECTED {ok}/{len(cases)}")
else:
    sys.exit(1)
