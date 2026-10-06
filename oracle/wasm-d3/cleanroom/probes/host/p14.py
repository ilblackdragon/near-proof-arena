"""All ed25519 fixture vectors (oracle/fixtures/v3/ed25519) through ed25519_verify."""
from hp import *
import glob
C = []
for f in sorted(glob.glob(os.path.join(HERE, "../../../../fixtures/v3/ed25519/*.jsonl"))):
    for line in open(f):
        v = json.loads(line)
        if "sig" in v and "pk" in v and "msg" in v and len(v["msg"]) < 4000:
            sig, pk, msg = (bytes.fromhex(v[k]) for k in ("sig", "pk", "msg"))
            C.append((v.get("id", "?"), P(sig + pk + msg).call("ed25519_verify", len(sig), 0, len(msg), len(sig) + len(pk), len(pk), len(sig)).done()))
a = near([c for _, c in C]); b = mine([c for _, c in C])
print("cases", len(C), "diffs", sum(x != y for x, y in zip(a, b)), "verified", sum(x.split()[3].startswith("01") for x in a if x.startswith("ok")))
