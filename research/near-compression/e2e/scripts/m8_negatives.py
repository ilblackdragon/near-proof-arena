#!/usr/bin/env python3
"""E2E-D M8: fresh-process negatives of `m8-verify` on a heterogeneous-tree packet.

    m8_negatives.py PROVER TREE_DIR OUT_DIR

Each case writes a tampered bundle / setup and runs `m8-verify` in a new process; every case must
exit non-zero with HTREE_VERIFY_REJECT (no panic message, no acceptance). Prints
M8_NEGATIVES_ALL_REJECTED n/n on success.
"""
import hashlib, json, os, subprocess, sys
from pathlib import Path

P, T, O = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
O.mkdir(parents=True, exist_ok=True)
setup = (T / "SETUP.json").read_bytes()
pin = (T / "SETUP.sha256").read_text().strip()
bundle = (T / "WRAP.bundle").read_bytes()
n = int.from_bytes(bundle[8:12], "little")
body = 12 + n

def run(name, setup_b, pin_s, bundle_b):
    sp, bp = O / f"{name}.setup.json", O / f"{name}.bundle"
    sp.write_bytes(setup_b)
    bp.write_bytes(bundle_b)
    r = subprocess.run([P, "m8-verify", str(sp), pin_s, str(bp)], capture_output=True, text=True,
                       env=dict(os.environ, RAYON_NUM_THREADS="1"))
    out = r.stdout + r.stderr
    ok = r.returncode != 0 and "HTREE_VERIFY_REJECT" in out and "panicked" not in out
    print(f"{'REJECTED' if ok else 'NOT_REJECTED'} {name}: rc={r.returncode} {out.strip().splitlines()[-1] if out.strip() else ''}")
    sp.unlink(); bp.unlink()
    return ok

def setup_with(f):
    s = json.loads(setup)
    f(s)
    b = json.dumps(s, separators=(",", ":")).encode()
    return b, hashlib.sha256(b).hexdigest()

def flip(b, i):
    b = bytearray(b)
    b[i] ^= 1
    return bytes(b)

cases = []
# the honest packet must pass (control)
r = subprocess.run([P, "m8-verify", str(T / "SETUP.json"), pin, str(T / "WRAP.bundle")], capture_output=True, text=True)
assert r.returncode == 0 and "INDEPENDENT_HTREE_VERIFY_OK" in r.stdout, "the honest packet is rejected"
print("ACCEPTED honest packet (control)")
cases.append(("S byte 0 changed", setup, pin, flip(bundle, 12)))
cases.append(("S byte in chunk_inner changed", setup, pin, flip(bundle, 12 + 200)))
cases.append(("S last byte changed", setup, pin, flip(bundle, 12 + n - 1)))
cases.append(("S with a non-empty section B count", setup, pin, flip(bundle, 12 + 416)))
cases.append(("S length +1", setup, pin, bundle[:8] + (n + 1).to_bytes(4, "little") + bundle[12:]))
cases.append(("S length -1", setup, pin, bundle[:8] + (n - 1).to_bytes(4, "little") + bundle[12:]))
cases.append(("proof byte flipped (start)", setup, pin, flip(bundle, body + 40)))
cases.append(("proof byte flipped (middle)", setup, pin, flip(bundle, body + (len(bundle) - body) // 2)))
cases.append(("proof byte flipped (end)", setup, pin, flip(bundle, len(bundle) - 3)))
cases.append(("truncated proof", setup, pin, bundle[:-100]))
cases.append(("trailing bytes", setup, pin, bundle + b"\0"))
cases.append(("bad magic", setup, pin, b"NPQTW02\0" + bundle[8:]))
cases.append(("wrong pin", setup, hashlib.sha256(b"x").hexdigest(), bundle))
b, p = setup_with(lambda s: s["program"][100].__setitem__(0, s["program"][100][0] ^ 1))
cases.append(("setup program changed (re-pinned)", b, p, bundle))
b, p = setup_with(lambda s: s.__setitem__("level", s["level"] + 1))
cases.append(("setup level changed (re-pinned)", b, p, bundle))
def th(s):
    h = s["final_heights"][0]
    h[1] = h[1] + 4 if h[1] is not None else 4
b, p = setup_with(th)
cases.append(("setup wrap heights changed (re-pinned)", b, p, bundle))
ok = sum(run(*c) for c in cases)
print(f"M8_NEGATIVES {ok}/{len(cases)} rejected")
if ok == len(cases):
    print(f"M8_NEGATIVES_ALL_REJECTED {ok}/{len(cases)}")
else:
    sys.exit(1)
