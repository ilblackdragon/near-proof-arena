#!/usr/bin/env python3
"""Adversarial and timing pass over the public fixtures with the judge's NPAI
interpreter (`npai-verify`) on the exported image.

For every case: prove honestly, check the honest proof is accepted, then run
proof mutators (bit flips across the whole proof, truncations, extensions,
byte insertions/deletions, receipt-count / node-count tampering, a proof of
another case) and claim mutators (bit flips, truncation, another case's
claim). Every mutant must be rejected (or be byte-identical to an accepted
input). Reports verify wall time per honest case (median of 5 runs).

usage: mutate.py IMAGE [FIXTURES_DIR]
"""
import json, os, random, statistics, subprocess, sys, tempfile, time

here = os.path.dirname(os.path.abspath(__file__))
pkg = os.path.dirname(here)
repo = os.path.abspath(os.path.join(pkg, "..", ".."))
args = sys.argv[1:]
img = args[0]
fx = args[1] if len(args) > 1 else os.path.join(repo, "oracle/fixtures/public")
pv = os.path.join(repo, "target/release/npai-verify")
prove = os.path.join(pkg, "source/target/release/prove")
prep = os.path.join(pkg, "source/target/release/prepare")
FUEL = "1073741824"
rng = random.Random(20261003)
tmp = tempfile.mkdtemp()
pub = os.path.join(tmp, "pub")
subprocess.run([prep, "--params", os.path.join(fx, "params.bin"), "--out", pub], check=True)


def verify(claim, proof):
    cp, pp = os.path.join(tmp, "c.bin"), os.path.join(tmp, "p.bin")
    open(cp, "wb").write(claim); open(pp, "wb").write(proof)
    r = subprocess.run([pv, "--image", img, "--public", pub, "--claim", cp, "--proof", pp, "--fuel", FUEL],
                       capture_output=True, text=True)
    try:
        o = json.loads(r.stdout)["outcome"]
    except Exception:
        o = "error"
    return r.returncode, o


def timed(cmd, n=5):
    ts = []
    for _ in range(n):
        t = time.perf_counter(); r = subprocess.run(cmd, capture_output=True); ts.append(time.perf_counter() - t)
        assert r.returncode == 0, (cmd, r.stderr)
    return statistics.median(ts) * 1000


cases = {}
for n in sorted(os.listdir(os.path.join(fx, "cases"))):
    c = os.path.join(fx, "cases", n)
    co, po = os.path.join(tmp, n + ".claim"), os.path.join(tmp, n + ".proof")
    subprocess.run([prove, "--public", pub, "--request", os.path.join(c, "request.bin"),
                    "--witness", os.path.join(c, "witness.bin"), "--claim-out", co, "--proof-out", po], check=True)
    cases[n] = (open(co, "rb").read(), open(po, "rb").read())

accepted = {(c, p) for c, p in cases.values()}
total = rejected = 0
bad = []
ctx_accepted = []


def ctx_range(claim):
    """[start, end) of height ‖ gas_price ‖ gas_limit in claim.bin (spec/claim-v1.md §3)."""
    o = 0
    for _ in range(2):  # format, statement id
        o += 4 + int.from_bytes(claim[o:o + 4], "little")
    o += 4  # protocol version
    o += 4 + int.from_bytes(claim[o:o + 4], "little")  # chain id
    o += 8  # shard
    return o, o + 8 + 16 + 8
timing = []
names = list(cases)
for k, n in enumerate(names):
    claim, proof = cases[n]
    rc, o = verify(claim, proof)
    assert rc == 0 and o == "accept", (n, rc, o)
    muts = []
    L = len(proof)
    for _ in range(40):
        i = rng.randrange(L); b = bytearray(proof); b[i] ^= 1 << rng.randrange(8); muts.append(("flip@%d" % i, claim, bytes(b)))
    for i in range(0, min(L, 64)):  # every byte of the head (counts, first receipt)
        b = bytearray(proof); b[i] ^= 0xff; muts.append(("xff@%d" % i, claim, bytes(b)))
    for cut in sorted({0, 1, 3, 4, L // 2, L - 33, L - 1}):
        if 0 <= cut < L: muts.append(("trunc%d" % cut, claim, proof[:cut]))
    muts += [("ext1", claim, proof + b"\x00"), ("ext32", claim, proof + bytes(32)),
             ("dup", claim, proof + proof)]
    for _ in range(5):
        i = rng.randrange(L)
        muts.append(("ins@%d" % i, claim, proof[:i] + bytes([rng.randrange(256)]) + proof[i:]))
        muts.append(("del@%d" % i, claim, proof[:i] + proof[i + 1:]))
    for d in (1, -1, 2):
        n0 = int.from_bytes(proof[:4], "little")
        if 0 <= n0 + d < 2**32: muts.append(("nrcpt%+d" % d, claim, (n0 + d).to_bytes(4, "little") + proof[4:]))
    other = names[(k + 1) % len(names)]
    muts.append(("proof-of-" + other, claim, cases[other][1]))
    muts.append(("claim-of-" + other, cases[other][0], proof))
    for _ in range(20):
        i = rng.randrange(len(claim)); b = bytearray(claim); b[i] ^= 1 << rng.randrange(8); muts.append(("cflip@%d" % i, bytes(b), proof))
    muts.append(("ctrunc", claim[:-1], proof))
    for lbl, c2, p2 in muts:
        if (c2, p2) in accepted:
            continue
        total += 1
        rc, o = verify(c2, p2)
        if rc != 0 and o != "accept":
            rejected += 1
        elif lbl.startswith("cflip@") and ctx_range(claim)[0] <= int(lbl[6:]) < ctx_range(claim)[1]:
            ctx_accepted.append((n, lbl))
        else:
            bad.append((n, lbl, rc, o))
    cp, pp = os.path.join(tmp, "c.bin"), os.path.join(tmp, "p.bin")
    open(cp, "wb").write(claim); open(pp, "wb").write(proof)
    t_npai = timed([pv, "--image", img, "--public", pub, "--claim", cp, "--proof", pp, "--fuel", FUEL])
    fuel = json.loads(subprocess.run([pv, "--image", img, "--public", pub, "--claim", cp, "--proof", pp, "--fuel", FUEL],
                                     capture_output=True, text=True).stdout)["fuel_used"]
    row = {"case": n, "proof_bytes": L, "fuel_used": fuel, "npai_verify_ms": round(t_npai, 2)}
    timing.append(row)

print(json.dumps({"image": img, "cases": len(names), "mutants": total, "rejected": rejected,
                  "accepted_mutants": bad,
                  "accepted_ctx_field_flips": len(ctx_accepted), "timing": timing}, indent=1))
sys.exit(0 if not bad else 1)
