#!/usr/bin/env python3
"""Differential test: NPAI bytecode (judge's npai-verify) vs the Lean reference
model ReexecNpai.check on honest and mutated (claim, proof) pairs.

usage: difftest.py IMAGE CASES_DIR [N_MUTATIONS_PER_CASE] [MAX_PROOF_BYTES]
Any disagreement is printed and makes the exit code 1."""
import os, random, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
pkg = os.path.dirname(here)
root = os.path.dirname(os.path.dirname(pkg))
img, cases = sys.argv[1], sys.argv[2]
nmut = int(sys.argv[3]) if len(sys.argv) > 3 else 200
maxp = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
fuel = "1073741824"
pv = os.path.join(root, "target/release/npai-verify")
prove = os.path.join(pkg, "source/target/release/prove")
prep = os.path.join(pkg, "source/target/release/prepare")
rnd = random.Random(1234)
tmp = tempfile.mkdtemp()
subprocess.run([prep, "--params", os.path.join(root, "oracle/fixtures/public/params.bin"), "--out",
                os.path.join(tmp, "pub")], check=True)
pairs = []
for name in sorted(os.listdir(cases)):
    c = os.path.join(cases, name)
    cl, pf = os.path.join(tmp, name + ".claim"), os.path.join(tmp, name + ".proof")
    r = subprocess.run([prove, "--public", os.path.join(tmp, "pub"), "--request", os.path.join(c, "request.bin"),
                        "--witness", os.path.join(c, "witness.bin"), "--claim-out", cl, "--proof-out", pf],
                       capture_output=True)
    if r.returncode != 0:
        continue
    claim, proof = open(cl, "rb").read(), open(pf, "rb").read()
    if len(proof) > maxp:
        continue
    pairs.append((name, "honest", claim, proof))
    for k in range(nmut):
        kind = rnd.randrange(6)
        p, q = bytearray(proof), bytearray(claim)
        if kind == 0:
            i = rnd.randrange(len(p)); p[i] ^= 1 << rnd.randrange(8); tag = f"proof bit {i}"
        elif kind == 1:
            i = rnd.randrange(len(p)); p[i] = rnd.randrange(256); tag = f"proof byte {i}"
        elif kind == 2:
            i = rnd.randrange(len(q)); q[i] ^= 1 << rnd.randrange(8); tag = f"claim bit {i}"
        elif kind == 3:
            i = rnd.randrange(len(p)); p = p[:i]; tag = f"proof trunc {i}"
        elif kind == 4:
            p += bytes([rnd.randrange(256)]); tag = "proof extend"
        else:
            i = rnd.randrange(len(p) - 4)
            p[i:i + 4] = rnd.randrange(1 << 32).to_bytes(4, "little"); tag = f"proof word {i}"
        pairs.append((name, tag, bytes(q), bytes(p)))
lines = []
for j, (name, tag, c, p) in enumerate(pairs):
    cp, pp = os.path.join(tmp, f"m{j}.claim"), os.path.join(tmp, f"m{j}.proof")
    open(cp, "wb").write(c); open(pp, "wb").write(p)
    lines.append(f"{cp} {pp}\n")
ref = subprocess.run(["lake", "env", "lean", "--run", os.path.join(here, "CheckRef.lean")],
                     input="".join(lines), capture_output=True, text=True, cwd=os.path.join(pkg, "dev"))
refs = ref.stdout.split()
assert len(refs) == len(pairs), (ref.stderr[-2000:], len(refs), len(pairs))
bad = 0; acc = 0
for j, (name, tag, c, p) in enumerate(pairs):
    r = subprocess.run([pv, "--image", img, "--public", os.path.join(tmp, "pub"),
                        "--claim", os.path.join(tmp, f"m{j}.claim"), "--proof", os.path.join(tmp, f"m{j}.proof"),
                        "--fuel", fuel], capture_output=True, text=True)
    got = "1" if r.returncode == 0 else "0"
    acc += got == "1"
    if got != refs[j]:
        bad += 1
        print(f"DISAGREE {name} {tag}: npai={got} lean={refs[j]} {r.stdout.strip()}")
print(f"{len(pairs)} cases, {acc} accepted, {bad} disagreements")
sys.exit(1 if bad else 0)
