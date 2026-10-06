"""Systematic order probe: for each host function, perturb one argument at a time to a failing value
(out-of-bounds pointer, register path to a missing register, huge length, invalid index)."""
from hp import *
import itertools
PK = b"\x00" + bytes(range(32))
H32 = bytes(range(32))
blob = {}
mem = bytearray()
def put(k, b):
    blob[k] = (len(mem), len(b)); mem.extend(b)
put("acct", b"bob.near"); put("pk", PK); put("u128", (5).to_bytes(16, "little")); put("names", b"m1,m2")
put("h32", H32); put("bytes", b"payload"); put("method", b"meth"); put("idx", (0).to_bytes(8, "little"))
put("abort", (8).to_bytes(4, "little") + "boom".encode("utf-16-le"))
put("big", (10**30).to_bytes(16, "little"))
OOB = 2**40
def good_args(name):
    ps = [a.split(":")[0].strip() for i in INV["imports"] if i["name"] == name and i["module"] == "env" for a in i["args"].split(",") if a.strip()]
    vals = {}
    for p in ps:
        if p.endswith("_len") and p[:-4] + "_ptr" in ps:
            base = p[:-4]
            k = ("acct" if "account" in base or "receiver" in base or "beneficiary" in base else
                 "pk" if "public_key" in base else "names" if "method_names" in base else
                 "method" if "method_name" in base else "h32" if ("hash" in base or "yield_id" in base or "data_id" in base or (base == "code" and "state_init" in name)) else "bytes")
            vals[p], vals[base + "_ptr"] = blob[k][1], blob[k][0]
    for p in ps:
        if p in vals: continue
        if p in ("amount_ptr", "allowance_ptr"): vals[p] = blob["u128"][0]
        elif p in ("promise_index", "promise_idx"): vals[p] = 0
        elif p == "gas": vals[p] = 10**12
        elif p == "promise_idx_ptr": vals[p] = blob["idx"][0]
        elif p == "promise_idx_count": vals[p] = 1
        elif p in ("register_id",): vals[p] = 0
        elif p in ("balance_ptr", "stake_ptr"): vals[p] = 4000
        elif p == "action_index": vals[p] = 1
        else: vals[p] = 0
    return ps, vals
def perturbations(ps, vals):
    out = [("good", dict(vals))]
    for p in ps:
        for tag, v in [("oob", OOB), ("reg", U64MAX), ("bad", 5)]:
            if tag == "reg" and not p.endswith("_len"): continue
            if tag == "bad" and p not in ("promise_index", "promise_idx", "action_index"):
                if not p.endswith("_len"): continue
                v = vals[p] - 1 if vals[p] else 1
            if tag == "oob" and p in ("promise_index", "promise_idx", "action_index", "gas", "nonce", "num_nonces", "gas_weight", "register_id", "promise_idx_count"):
                continue
            d = dict(vals); d[p] = v
            if tag == "reg":
                d[p[:-4] + "_ptr"] = 7
            out.append((f"{p}={tag}", d))
    # pairs: invalid promise index combined with each other failure
    pi = [p for p in ps if p in ("promise_index", "promise_idx")]
    if pi:
        for l, d in list(out[1:]):
            if l.startswith(pi[0]): continue
            d2 = dict(d); d2[pi[0]] = 5
            out.append((l + "+badidx", d2))
    return out
NAMES = sys.argv[1:] or [i["name"] for i in INV["imports"] if i["module"] == "env" and i["enabled_in_production"]
         and not i["name"].startswith(("bls", "alt_bn", "ecrecover", "p256"))]
C = []
for name in NAMES:
    ps, vals = good_args(name)
    if not ps: continue
    for l, d in perturbations(ps, vals):
        p = P(bytes(mem), opts="results=S0102,F,N")
        p.call("promise_batch_create", 8, blob["acct"][0])
        if "data_entry" in name:
            p.call("promise_batch_action_state_init", 0, 32, blob["h32"][0], blob["u128"][0])
        if "yield_resume" in name:
            p.call("promise_yield_create_with_id", 4, blob["method"][0], 0, 0, blob["u128"][0], 10**12, 0, 32, blob["h32"][0])
        p.call(name, *[d[x] for x in ps])
        C.append((f"{name[:40]} {l}", p.done(False)))
a = near([c for _, c in C]); b = mine([c for _, c in C])
nd = 0
for (l, _), x, y in zip(C, a, b):
    if x != y:
        nd += 1
        print(f"DIFF {l}\n  near: {x[:260]}\n  mine: {y[:260]}")
print("cases", len(C), "diffs", nd)
