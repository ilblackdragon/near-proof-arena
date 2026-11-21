"""Generate ML-DSA-65 signatures whose ||z||_inf sits at the FIPS 204 norm bound γ1−β = 524092.

Signer = FIPS 204 Algorithm 7 (ML-DSA.Sign_internal), pure ML-DSA, empty context
(M' = 0x00||0x00||msg), with the single change that the `||z||_inf >= γ1−β` rejection is replaced
by "keep only attempts with max|z| in {B−1, B, B+1}"; the r0, ct0 and hint-weight checks, c̃, the
hint and the encoding are the standard ones. Keys: KeyGen_internal(ξ) with ξ = the nearcore
`SecretKey::from_seed(KeyType::MLDSA65, seed)` bytes (seed string space-padded to 32 bytes).
Deterministic: rnd_i = SHA-256("zbound-rnd" || seed || i), κ = 0, 5, 10, ... ; for each category
the hit with the smallest (i, κ) is taken.

usage: gen_zbound.py OUT.json [NKEYS] [NRND] [NITER]
"""
import hashlib
import json
import sys
from concurrent.futures import ProcessPoolExecutor

import mldsa65 as M

B = M.ZB
CATS = ["zmax-bound-minus-1", "zmax-bound-pos", "zmax-bound-neg", "zmax-bound-plus-1"]


def seed(k):
    return f"zbound-mldsa-{k}"


def msg(k):
    return hashlib.sha256(f"zbound-msg-{k}".encode()).digest()


def category(sig):
    zs = [M.centered(M.G1 - x) for r in range(M.L)
          for x in M.bitunpack(sig[48 + 640 * r: 48 + 640 * (r + 1)], 20)]
    mz = max(abs(x) for x in zs)
    if mz == B - 1:
        return CATS[0]
    if mz == B + 1:
        return CATS[3]
    return CATS[1] if B in zs else CATS[2]


_SK = {}


def work(job):
    k, i, niter = job
    if k not in _SK:
        _SK[k] = M.keygen(M.nearcore_xi(seed(k)))
    _, sk = _SK[k]
    rnd = hashlib.sha256(b"zbound-rnd" + seed(k).encode() + i.to_bytes(4, "little")).digest()
    return [(k, i, kappa, category(sig), mz, sig.hex(), rnd.hex())
            for kappa, sig, mz in M.sign_attempts(sk, msg(k), rnd, niter, lambda m: B - 1 <= m <= B + 1)]


def main():
    outp = sys.argv[1]
    nkeys = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    nrnd = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    niter = int(sys.argv[4]) if len(sys.argv) > 4 else 256
    jobs = [(k, i, niter) for k in range(nkeys) for i in range(nrnd)]
    with ProcessPoolExecutor(32) as ex:
        hits = [h for r in ex.map(work, jobs) for h in r]
    pks = [M.keygen(M.nearcore_xi(seed(k)))[0] for k in range(nkeys)]
    best = {}
    for h in sorted(hits, key=lambda h: (h[0], h[1], h[2])):
        best.setdefault((h[0], h[3]), h)
    sigs, cases = [], []
    for k in range(nkeys):
        for c in CATS:
            if (k, c) not in best:
                continue
            _, i, kappa, _, mz, sh, rnd = best[(k, c)]
            sig = bytes.fromhex(sh)
            assert M.maxabs_z(sig) == mz
            mine = M.verify(pks[k], msg(k), sig)
            assert mine == (mz < B)
            cases.append({"name": f"k{k}-{c}", "key": k, "msg": msg(k).hex(), "sig": len(sigs),
                          "patch": [], "expect": mine, "maxz": mz, "rnd_index": i, "kappa": kappa,
                          "rnd": rnd})
            sigs.append(sh)
    d = {"crate": "expect = FIPS 204 verdict (mldsa65.py); pinned-crate verdict added as crate_verdict",
         "generator": "gen_zbound.py: FIPS 204 Sign_internal without the ||z|| rejection",
         "attempts": nkeys * nrnd * niter, "hits": len(hits),
         "seeds": [seed(k) for k in range(nkeys)],
         "keys": [p.hex() for p in pks], "sigs": sigs, "cases": cases}
    with open(outp, "w") as f:
        json.dump(d, f, indent=1)
    print(len(hits), "hits in", nkeys * nrnd * niter, "attempts;", len(cases), "cases")
    for c in cases:
        print(c["name"], c["maxz"], c["expect"], c["rnd_index"], c["kappa"])


if __name__ == "__main__":
    main()
