#!/usr/bin/env python3
"""Local adversarial check of out/verify (NOT the judge's ADVERSARIAL_PROOFS gate).

adversarial.py <verify-bin> <public-dir> <claimA> <proofA> <claimB> <proofB> [--random N]

Asserts: honest (A,A),(B,B) accept twice (determinism); every mutation is
rejected with exit code 1 (never 0): proof byte flips (random + structured
offsets), truncations, extensions, empty/garbage proofs, claim byte flips,
claim/proof swaps across cases, tampered public.bin (must not accept).
"""
import os, random, shutil, subprocess, sys, tempfile

def run(vbin, pub, claim, proof):
    return subprocess.run([vbin, "--public", pub, "--claim", claim, "--proof", proof],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=120).returncode

def main():
    a = sys.argv[1:]
    vbin, pub, cA, pA, cB, pB = a[:6]
    n_rand = int(a[a.index("--random") + 1]) if "--random" in a else 200
    rng = random.Random(1234)
    tmp = tempfile.mkdtemp()
    stats = {"accept_honest": 0, "rejected": 0, "error_nonaccept": 0, "ACCEPTED_HOSTILE": 0}
    def put(name, data):
        p = os.path.join(tmp, name); open(p, "wb").write(data); return p
    def hostile(label, claim, proof, pubdir=pub):
        rc = run(vbin, pubdir, claim, proof)
        if rc == 0:
            stats["ACCEPTED_HOSTILE"] += 1; print("HOSTILE ACCEPTED:", label)
        elif rc == 1: stats["rejected"] += 1
        else: stats["error_nonaccept"] += 1; print(f"non-1 exit {rc}: {label}")
    for c, p in ((cA, pA), (cB, pB)):
        for _ in range(2):
            assert run(vbin, pub, c, p) == 0, "honest proof rejected"
            stats["accept_honest"] += 1
    proof = open(pA, "rb").read(); claim = open(cA, "rb").read()
    # proof byte flips: header, structured offsets, random
    offs = list(range(0, 64)) + [len(proof) - 1 - i for i in range(64)]
    offs += [len(proof) * k // 64 for k in range(64)]
    offs += [rng.randrange(len(proof)) for _ in range(n_rand)]
    for o in offs:
        b = bytearray(proof); b[o] ^= 1 << rng.randrange(8)
        hostile(f"proof flip @{o}", cA, put("p", bytes(b)))
    for cut in (0, 1, 31, 32, len(proof) // 2, len(proof) - 1):
        hostile(f"proof truncated to {cut}", cA, put("p", proof[:cut]))
    hostile("proof + trailing byte", cA, put("p", proof + b"\0"))
    hostile("proof garbage", cA, put("p", os.urandom(len(proof))))
    # claim mutations with the honest proof
    for o in range(len(claim)):
        b = bytearray(claim); b[o] ^= 1
        hostile(f"claim flip @{o}", put("c", bytes(b)), pA)
    hostile("claim truncated", put("c", claim[:-1]), pA)
    hostile("claim extended", put("c", claim + b"\0"), pA)
    hostile("empty claim", put("c", b""), pA)
    # cross-case swaps
    hostile("claimB with proofA", cB, pA)
    hostile("claimA with proofB", cA, pB)
    # tampered public.bin (vk word flipped): must not accept the honest proof
    pub2 = os.path.join(tmp, "pub2"); shutil.copytree(pub, pub2)
    pb = bytearray(open(os.path.join(pub, "public.bin"), "rb").read())
    for o in (len(pb) - 30, 70, 110):
        q = bytearray(pb); q[o] ^= 1; open(os.path.join(pub2, "public.bin"), "wb").write(q)
        hostile(f"public.bin flip @{o}", cA, pA, pub2)
    print(stats)
    sys.exit(1 if stats["ACCEPTED_HOSTILE"] else 0)

if __name__ == "__main__":
    main()
