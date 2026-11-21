#!/usr/bin/env python3
"""E2E M5-T1: the runtime trace of a chunk's incoming FunctionCall receipts.

  tracegen.py LEAN_RUN_JSON AIR_DIR OUT_DIR [--mutant NAME]

LEAN_RUN_JSON is `m5t1-tool dump` (the Lean checker's own INTAKE and engine steps, every incoming
receipt run through the oracle form of the receipt step).  AIR_DIR holds `m5t1-tool air`'s
`names.json` / `schema.json`.  Every value of the trace is taken from, or recomputed and asserted
equal to, the Lean run: the receipt bytes, the account before / after, the VM query and answer,
the outcome (`partialEncode`, `leaf`), the refund receipt (`encode`), the receipt state's totals.

Writes OUT_DIR/{RNG,SCHT,MSG,DG,RX}.bin (u32 log2 height, u32 width, u32 cells row-major),
sha_msgs.json (the SHA-256 table's messages), tape.json (the statement: receipt-list digest,
outcome leaves, outgoing receipt hashes), xtape.json (T1 stand-ins: lane B's account read / write,
lane A's Wasm call), pubs.bin, and expected.json (the outputs, for the comparison).

Mutants (`--mutant`): a prover that deviates from the spec in one value, with every *other* cell
recomputed consistently where it can be (exit 3 = not applicable).
"""
import hashlib
import json
import struct
import sys
from collections import Counter, defaultdict

P = 0x78000001

# ---------------------------------------------------------------------------------------------
# ids (M5T1/Ids.lean)
MT = dict(RL=0, KEYR=1, APRE=2, KEYW=3, APOST=4, AH=5, SEED=6, RID=7, RREF=8, LOG0=9, PART=13,
          LEAF0=14, PAD=31)
F = dict(COUNT=0, PRED=2, RECV=4, RID=5, SIGNER=8, PK=10, GPRICE=11, METHOD=17, ARGS=19, GAS=20,
         DEPOSIT=21, AMT=30, LOCKED=31, CODEH=32, USAGE=33, AMT2=40, REFUND=42, GB=43, TB=44,
         LEAFN=45, HEIGHT=50, RANDV=52, TSTAMP=53, EPOCHH=54, LOG0=56, RET=61, VBURNT=70,
         VUSED=71, VCOMP=72, VBAL=73, VUSAGE=74, VSUB=75)
NAR_EXEC = 108059500000
FC_BASE_EXEC = 780000000000
FC_BYTE_EXEC = 2235934
CREATE_ACCOUNT_EXEC = 7200000000000
STORAGE_PER_BYTE = 10 ** 19
ZERO_BALANCE_LIMIT = 770
PTR_KEY, PTR_VAL = 0, 128
SYSTEM = b"system"


def dig(mt):
    return 96 + mt


def msg_id(mf, mt):
    return 128 * mf + 96 + mt


def sidof(qf, fid):
    return 128 * qf + fid


def le(v, n):
    assert 0 <= v < 256 ** n, (v, n)
    return list(v.to_bytes(n, "little"))


def val(bs):
    return int.from_bytes(bytes(bs), "little")


def inv(x):
    x %= P
    assert x != 0
    return pow(x, P - 2, P)


def u32(v):
    return list(struct.pack("<I", v))


# ---------------------------------------------------------------------------------------------
class Trace:
    """A table: named columns (names.json), rows as dicts name -> value."""

    def __init__(self, names):
        self.names = names
        self.idx = {n: i for i, n in enumerate(names)}
        self.rows = []

    def row(self):
        r = [0] * len(self.names)
        self.rows.append(r)
        return r

    def set(self, r, name, v, j=None):
        key = name if j is None else f"{name}.{j}"
        if key not in self.idx:  # single column groups have no `.0`
            assert j == 0 and name in self.idx, key
            key = name
        r[self.idx[key]] = v % P

    def get(self, r, name, j=None):
        key = name if j is None else f"{name}.{j}"
        if key not in self.idx:
            key = name
        return r[self.idx[key]]

    def setv(self, r, name, bs):
        for j, b in enumerate(bs):
            self.set(r, name, b, j)

    def write(self, path, min_log=2):
        h = max(len(self.rows), 1 << min_log)
        log = (h - 1).bit_length()
        h = 1 << log
        w = len(self.names)
        with open(path, "wb") as f:
            f.write(struct.pack("<II", log, w))
            buf = bytearray()
            for i in range(h):
                r = self.rows[i] if i < len(self.rows) else [0] * w
                buf += struct.pack(f"<{w}I", *r)
            f.write(buf)
        return log


# ---------------------------------------------------------------------------------------------
class Fields:
    """The `FB`/`FLEN` buses: providers and consumer counts."""

    def __init__(self):
        self.fb = {}  # (sid, k) -> byte
        self.flen = {}  # sid -> len
        self.fb_use = Counter()
        self.flen_use = Counter()

    def define(self, sid, bs):
        for k, b in enumerate(bs):
            key = (sid, k)
            assert key not in self.fb or self.fb[key] == b, ("redefined", key)
            self.fb[key] = b

    def define_len(self, sid, n):
        assert sid not in self.flen or self.flen[sid] == n, ("len redefined", sid)
        self.flen[sid] = n

    def use(self, sid, k):
        self.fb_use[(sid, k)] += 1
        return self.fb[(sid, k)]

    def use_bytes(self, sid, n):
        return [self.use(sid, k) for k in range(n)]

    def use_len(self, sid):
        self.flen_use[sid] += 1
        return self.flen[sid]


STRICT = True


def check(c, what):
    """a consistency check of the honest trace (mutants deliberately break some)"""
    if STRICT:
        assert c, what


def bits(v, n):
    assert 0 <= v < (1 << n), (v, n)
    return [(v >> i) & 1 for i in range(n)]


# ---------------------------------------------------------------------------------------------
def load_schema(air_dir):
    sch = json.load(open(f"{air_dir}/schema.json"))
    fields = sch["fields"]
    entries = [dict(zip(fields, e)) for e in sch["entries"]]
    by = {(e["mt"], e["s"]): (i, e) for i, e in enumerate(entries)}
    return fields, entries, by, sch["buses"]


def parse_message(by, mt, data, fields, qf0, define_mode):
    """Walk the schema of type `mt` over the message bytes `data`.  Returns a list of
    (entry, k, L, byte, qf, acc-info...) per byte; defines (parse) or checks (emit) fields."""
    out = []
    s, j, qf = 0, 0, qf0
    pending_len = None
    n = len(data)
    while True:
        _, e = by[(mt, s)]
        if e["newR"]:
            qf += 1
        kind = [x for x in ("kC", "kD", "kU", "kUV", "kLP", "kLE", "kCNT") if e[x]][0]
        sid = sidof(qf, e["fid"])
        if kind in ("kLP", "kLE", "kCNT"):
            L = 4
        elif kind == "kUV":
            L = fields.flen[sid]
        elif e["var"]:
            L = pending_len
        else:
            L = e["fixL"]
        seg = data[j:j + L]
        assert len(seg) == L, ("message too short", mt, s, j, L, n)
        acc = None
        if kind == "kC":
            check(seg[0] == e["cv"], ("constant mismatch", mt, s, seg[0], e["cv"]))
        elif kind == "kD":
            fields.define(sid, seg)
        elif kind in ("kU", "kUV"):
            want = [fields.fb.get((sid, k)) for k in range(L)]
            check(want == list(seg), ("use mismatch", mt, s, sid, bytes(seg).hex(), bytes(want).hex()))
            if kind == "kUV":
                assert fields.flen[sid] == L, ("kUV len", mt, s, sid)
        else:
            acc = val(seg)
            assert seg[3] == 0, "u32 top byte"
            if kind == "kLP" or kind == "kCNT":
                fields.define_len(sid, acc)
            else:
                check(fields.flen[sid] == acc, ("LE mismatch", mt, s, sid, acc, fields.flen.get(sid)))
        z = 1 if (kind in ("kLP", "kLE") and acc == 0) else 0
        for k in range(L):
            out.append(dict(e=e, s=s, k=k, L=L, b=seg[k], qf=qf, kind=kind, acc_seg=acc, z=z,
                            last=(k == L - 1), sid=sid))
        j += L
        if kind in ("kLP", "kLE"):
            pending_len = acc
        # next segment
        if z:
            if e["skipEnd"]:
                assert j == n, "skipEnd but bytes remain"
                out[-1]["endm"] = 1
                return out, qf
            s = e["skipS"]
        else:
            if e["endOK"] and (j == n or not e["cont"]):
                assert j == n, ("message has trailing bytes", mt, s, j, n)
                out[-1]["endm"] = 1
                return out, qf
            s = e["nextS"]


# ---------------------------------------------------------------------------------------------
def lin_carries(terms, r, top):
    """carries for `terms_k + cy_{k-1} = r_k + 256 cy_k`, cy_{N-1} = top"""
    N = len(terms)
    cy = []
    c = 0
    for k in range(N):
        t = terms[k] + c
        assert t >= r[k] and (t - r[k]) % 256 == 0, ("lin limb", k, terms[k], c, r[k])
        c = (t - r[k]) // 256
        cy.append(c)
    assert cy[-1] == top, ("lin top carry", cy[-1], top)
    return cy[:-1]


def mul_terms(a, b, N):
    return [sum(a[i] * b[k - i] for i in range(len(a)) if 0 <= k - i < len(b)) for k in range(N)]


def main():
    args = sys.argv[1:]
    mutant = None
    if "--mutant" in args:
        i = args.index("--mutant")
        mutant = args[i + 1]
        args = args[:i] + args[i + 2:]
    tmpl = None
    if "--template" in args:
        i = args.index("--template")
        tmpl = args[i + 1]
        args = args[:i] + args[i + 2:]
    plan = None
    if "--plan" in args:
        i = args.index("--plan")
        plan = args[i + 1]
        args = args[:i] + args[i + 2:]
    run_path, air_dir, out = args
    global STRICT
    STRICT = mutant is None
    import os
    os.makedirs(out, exist_ok=True)
    run = json.load(open(run_path))
    names = json.load(open(f"{air_dir}/names.json"))
    sch_fields, entries, by, buses = load_schema(air_dir)
    B = buses
    nb_sch = names["schNbits"]
    env = run["env"]
    fields = Fields()
    applied = []  # mutant bookkeeping

    # ----- the receipt list (family 0) --------------------------------------------------------
    rl = bytes.fromhex(run["encodeIncoming"])
    assert hashlib.sha256(rl).hexdigest() == run["appliedReceiptsHash"]
    recs = run["receipts"]
    n = len(run["incoming"])
    assert n == len(recs) and n >= 1
    messages = []  # (m, mf, mt, data, ts, ptr)
    messages.append((msg_id(0, MT["RL"]), 0, MT["RL"], list(rl), 0, 0))
    fields.define(msg_id(0, MT["RL"]), list(hashlib.sha256(rl).digest()))

    # ----- per receipt: the values, from the Lean run ---------------------------------------
    rxs = []
    t0 = 1
    pubs_in = None
    for q, R in enumerate(recs, start=1):
        rc = R["receipt"]
        body = rc["body"]
        assert body["kind"] == "action" and not body["yield"] and not body["v2"], "template: V1 action receipt"
        assert body["outputs"] == [] and body["inputs"] == [] and len(body["actions"]) == 1
        fc = body["actions"][0]["base"]
        assert fc["kind"] == "fcall", "template: one FunctionCall"
        assert len(R["calls"]) == 1
        call = R["calls"][0]
        run_ = call["run"]
        assert run_["kind"] == "done" and run_["err"] is None, "template: the call succeeds"
        assert run_["nActions"] == "0", "template: no promises"
        assert run_["ret"] is None or "value" in run_["ret"], "template: no promise_return"
        ctx = call["ctx"]
        before, after = R["before"], R["after"]
        acct0 = before["recvAcct"]
        acct1 = after["recvAcct"]
        assert not acct0["v2"] and not acct1["v2"], "template: V1 account"
        recv = bytes.fromhex(rc["recv"])
        x = dict(q=q, R=R, rc=rc, body=body, fc=fc, run=run_, ctx=ctx, recv=recv)
        x["pred"] = bytes.fromhex(rc["pred"])
        x["signer"] = bytes.fromhex(body["signer"])
        x["gp"] = int(body["gasPrice"])
        x["egp"] = int(R["env"]["gasPrice"])
        x["gas"] = int(fc["gas"])
        x["dep"] = int(fc["deposit"])
        x["method"] = bytes.fromhex(fc["method"])
        x["args"] = bytes.fromhex(fc["args"])
        pre = bytes.fromhex(acct0["encode"])
        post = bytes.fromhex(acct1["encode"])
        x["pre"], x["post"] = list(pre), list(post)
        x["amt"], x["lck"], x["ch"], x["use"] = val(pre[0:16]), val(pre[16:32]), list(pre[32:64]), val(pre[64:72])
        assert x["amt"] == int(acct0["amount"]) and x["use"] == int(acct0["usage"])
        x["vb"], x["vu"], x["vc"] = int(run_["burnt"]), int(run_["used"]), int(run_["compute"])
        x["vbal"], x["vus"], x["vsub"] = int(run_["balance"]), int(run_["storageUsage"]), int(run_["subsidized"])
        x["logs"] = [bytes.fromhex(l) for l in run_["logs"]]
        x["ret"] = bytes.fromhex(run_["ret"]["value"]) if run_["ret"] else b""
        assert len(x["logs"]) <= 4 and all(len(l) > 0 for l in x["logs"]), "template: ≤ 4 non-empty logs"
        # the outcome and the refund receipt the Lean run produced
        outs = after["outcomes"]
        assert len(outs) == len(before["outcomes"]) + 1
        x["out"] = outs[-1]
        assert len(after["outgoing"]) == len(before["outgoing"]) + 1, "template: the refund is forwarded"
        x["refund"] = after["outgoing"][-1]
        x["ts0"] = t0
        x["tse"] = t0 + 2
        t0 = x["tse"] + 2
        rxs.append(x)

    # ----- the arithmetic (RX), asserted against the Lean run --------------------------------
    for x in rxs:
        lm, la = len(x["method"]), len(x["args"])
        x["lm"], x["la"] = lm, la
        fcx = FC_BASE_EXEC + FC_BYTE_EXEC * (lm + la)
        gb = NAR_EXEC + fcx + x["vb"]
        gu = NAR_EXEC + fcx + x["vu"]
        cu = NAR_EXEC + fcx + x["vc"]
        assert gb == int(x["out"]["gasBurnt"]), "gas burnt != Lean outcome"
        burn = min(x["gp"], x["egp"])
        pexec = fcx + NAR_EXEC
        tot = x["gas"] + pexec
        gross = tot - gu
        assert gross >= 0
        unu = x["gp"] * gross
        gpb = x["gp"] - burn
        sur = gpb * gb
        bc = burn * CREATE_ACCOUNT_EXEC
        rf = unu + sur
        tb = burn * gb
        fc3 = 3 * x["vb"]
        q10, r10 = divmod(fc3, 10)
        rew = burn * q10
        amt2 = x["vbal"] + rew
        txb = tb - rew
        req = STORAGE_PER_BYTE * x["vus"]
        ak = x["vbal"] + x["lck"]
        x.update(fcx=fcx, gb=gb, gu=gu, cu=cu, burn=burn, pexec=pexec, tot=tot, gross=gross, unu=unu,
                 gpb=gpb, sur=sur, bc=bc, rf=rf, tb=tb, fc3=fc3, q10=q10, r10=r10, rew=rew,
                 amt2=amt2, txb=txb, req=req, ak=ak)
        # spec facts the Lean run already decided
        assert tb == int(x["out"]["tokensBurnt"]), "tokens burnt != Lean outcome"
        rbody = x["refund"]["body"]
        assert int(rbody["actions"][0]["base"]["deposit"]) == rf, "refund amount != Lean refund receipt"
        assert amt2 == val(x["post"][0:16]), "new amount != Lean account"
        assert x["vus"] == val(x["post"][64:72])
        assert ak >= req or x["vus"] <= ZERO_BALANCE_LIMIT
        assert x["pred"] != SYSTEM

    # mutants on values (consistent re-encoding where possible)
    def mut(name):
        return mutant == name

    # ----- fields every family defines from outside MSG ------------------------------------
    # RX-defined, VM-defined (lane A stand-in), env
    for x in rxs:
        qf = x["q"]
        S = lambda fid: sidof(qf, fid)
        if mut("refund"):
            x["rf"] += 10 ** 9  # the refund receipt carries a different amount (rows recomputed)
            applied.append("refund")
        if mut("gasburnt"):
            x["gb"] += 1  # the outcome claims 1 more gas burnt
            applied.append("gasburnt")
        if mut("acctpost"):
            # the account write carries a balance 1 yocto higher than the receipt step computes
            x["post"] = le(x["amt2"] + 1, 16) + x["post"][16:]
            fields.define(S(F["AMT2"]), le(x["amt2"] + 1, 16))
            applied.append("acctpost")
        else:
            fields.define(S(F["AMT2"]), le(x["amt2"], 16))
        fields.define(S(F["REFUND"]), le(x["rf"], 16))
        fields.define(S(F["GB"]), le(x["gb"], 8))
        fields.define(S(F["TB"]), le(x["tb"], 16))
        fields.define(S(F["LEAFN"]), [2 + len(x["logs"]), 0, 0, 0])
        fields.define(S(F["HEIGHT"]), le(int(env["height"]), 8))
        fields.define(S(F["RANDV"]), list(bytes.fromhex(env["randomValue"])))
        fields.define(S(F["TSTAMP"]), le(int(env["blockTimestamp"]), 8))
        fields.define(S(F["EPOCHH"]), le(int(env["epochHeight"]), 8))
        fields.define(S(F["VBURNT"]), le(x["vb"], 8))
        fields.define(S(F["VUSED"]), le(x["vu"], 8))
        fields.define(S(F["VCOMP"]), le(x["vc"], 8))
        fields.define(S(F["VBAL"]), le(x["vbal"], 16))
        fields.define(S(F["VUSAGE"]), le(x["vus"], 8))
        fields.define(S(F["VSUB"]), le(x["vsub"], 16))
        for i, l in enumerate(x["logs"]):
            fields.define(S(F["LOG0"] + i), list(l))
            fields.define_len(S(F["LOG0"] + i), len(l))
        fields.define(S(F["RET"]), list(x["ret"]))
        fields.define_len(S(F["RET"]), len(x["ret"]))

    # ----- messages ---------------------------------------------------------------------------
    # parse RL first (defines the receipt fields)
    rows_by_msg = {}
    rl_rows, qf_end = parse_message(by, MT["RL"], list(rl), fields, 0, True)
    assert qf_end == n
    rows_by_msg[msg_id(0, MT["RL"])] = rl_rows
    for x in rxs:
        qf = x["q"]
        key = [0] + list(x["recv"])
        x["key"] = key
        h = int(env["height"])
        rid = bytes.fromhex(x["rc"]["rid"])
        ah_pre = list(rid + h.to_bytes(8, "little") + (2 ** 64 - 1).to_bytes(8, "little"))
        ah = hashlib.sha256(bytes(ah_pre)).digest()
        assert ah.hex() == x["ctx"]["actionHash"]
        seed_pre = list(ah + bytes.fromhex(env["randomValue"]))
        assert hashlib.sha256(bytes(seed_pre)).hexdigest() == x["ctx"]["randomSeed"]
        rid_pre = list(rid + h.to_bytes(8, "little") + (0).to_bytes(8, "little"))
        rid2 = hashlib.sha256(bytes(rid_pre)).digest()
        assert rid2.hex() == x["refund"]["rid"] and x["out"]["receiptIds"] == [rid2.hex()]
        if mut("rcptid"):
            # the prover claims another receipt id for the refund (outcome + refund receipt agree)
            rid2 = bytes([rid2[0] ^ 1]) + rid2[1:]
            applied.append("rcptid")
        refund_enc = (u32(6) + list(SYSTEM) + u32(len(x["signer"])) + list(x["signer"]) + list(rid2) + [0] +
                      u32(len(x["signer"])) + list(x["signer"]) + [0] + list(bytes.fromhex(x["body"]["signerPk"])[1:]) +
                      [0] * 16 + u32(0) + u32(0) + u32(1) + [3] + le(x["rf"], 16))
        if not (mut("refund") or mut("rcptid")):
            assert bytes(refund_enc).hex() == x["refund"]["encode"], "refund receipt encoding"
        status = [2] + u32(len(x["ret"])) + list(x["ret"])
        if mut("status"):
            # the outcome claims an empty SuccessValue instead of the call's return value
            status = [2] + u32(0)
            applied.append("status")
        part = u32(1) + list(rid2) + le(x["gb"], 8) + le(x["tb"], 16) + u32(len(x["recv"])) + list(x["recv"]) + status
        check(bytes(part).hex() == x["out"]["partialEncode"], "outcome partialEncode")
        logs_d = [hashlib.sha256(l).digest() for l in x["logs"]]
        if mut("logbyte") and x["logs"]:
            logs_d[0] = hashlib.sha256(bytes([x["logs"][0][0] ^ 1]) + x["logs"][0][1:]).digest()
        leaf_pre = u32(2 + len(x["logs"])) + list(rid) + list(hashlib.sha256(bytes(part)).digest())
        for d in logs_d:
            leaf_pre += list(d)
        leaf = hashlib.sha256(bytes(leaf_pre)).digest()
        check(leaf.hex() == x["out"]["leaf"], "outcome leaf")
        x["leafd"] = list(leaf)
        x["rrh"] = list(hashlib.sha256(bytes(refund_enc)).digest())
        tsw = x["tse"] + 1
        msgs = [(MT["KEYR"], key, x["ts0"], PTR_KEY), (MT["APRE"], x["pre"], x["ts0"], PTR_VAL),
                (MT["KEYW"], key, tsw, PTR_KEY), (MT["APOST"], x["post"], tsw, PTR_VAL),
                (MT["AH"], ah_pre, 0, 0), (MT["SEED"], seed_pre, 0, 0), (MT["RID"], rid_pre, 0, 0),
                (MT["RREF"], refund_enc, 0, 0)]
        logm = [list(l) for l in x["logs"]]
        if mut("logbyte") and logm:
            # the hashed log differs from the bytes the Wasm side logged (one byte)
            logm[0][0] ^= 1
            applied.append("logbyte")
        msgs += [(MT["LOG0"] + i, l, 0, 0) for i, l in enumerate(logm)]
        msgs += [(MT["PART"], part, 0, 0), (MT["LEAF0"] + len(x["logs"]), leaf_pre, 0, 0)]
        # digests are fields of the family (the DG rows): define before the parse that uses them
        for mt, data, ts, ptr in msgs:
            m = msg_id(qf, mt)
            if mt not in (MT["KEYR"], MT["APRE"], MT["KEYW"], MT["APOST"]):
                fields.define(m, list(hashlib.sha256(bytes(data)).digest()))
            messages.append((m, qf, mt, data, ts, ptr))
        # APRE defines the account fields: parse it before the others use them
    messages.sort(key=lambda t: t[0])
    # parse in an order where definitions precede uses: RL, then APRE of every family, then the rest
    order = sorted(messages, key=lambda t: (0 if t[2] == MT["RL"] else 1 if t[2] == MT["APRE"] else 2, t[0]))
    for m, mf, mt, data, ts, ptr in order:
        if mt == MT["RL"]:
            continue
        rows, _ = parse_message(by, mt, data, fields, mf, True)
        rows_by_msg[m] = rows

    # ----- consumers (who reads FB / FLEN): MSG uses, RX, the stand-in tape ------------------
    for m, mf, mt, data, ts, ptr in messages:
        for r in rows_by_msg[m]:
            if r["kind"] in ("kU", "kUV"):
                fields.use(r["sid"], r["k"])
            if r["kind"] == "kUV" and r["k"] == 0:
                fields.use_len(r["sid"])
            if r["kind"] == "kLE" and r["last"]:
                fields.use_len(r["sid"])
    xtape = []  # (bus, send, msg)
    tape = []
    for x in rxs:
        qf = x["q"]
        S = lambda fid: sidof(qf, fid)
        x["in"] = dict(gp=fields.use_bytes(S(F["GPRICE"]), 16), gas=fields.use_bytes(S(F["GAS"]), 8),
                       dep=fields.use_bytes(S(F["DEPOSIT"]), 16), amt=fields.use_bytes(S(F["AMT"]), 16),
                       lck=fields.use_bytes(S(F["LOCKED"]), 16), ch=fields.use_bytes(S(F["CODEH"]), 32),
                       vb=fields.use_bytes(S(F["VBURNT"]), 8), vu=fields.use_bytes(S(F["VUSED"]), 8),
                       vc=fields.use_bytes(S(F["VCOMP"]), 8), vbal=fields.use_bytes(S(F["VBAL"]), 16),
                       vus=fields.use_bytes(S(F["VUSAGE"]), 8), vsub=fields.use_bytes(S(F["VSUB"]), 16),
                       rrh=fields.use_bytes(msg_id(qf, MT["RREF"]), 32),
                       leaf=fields.use_bytes(msg_id(qf, MT["LEAF0"] + len(x["logs"])), 32))
        assert fields.use_len(S(F["METHOD"])) == x["lm"] and fields.use_len(S(F["ARGS"])) == x["la"]
        x["lp"] = fields.use_len(S(F["PRED"]))
        if q == n:
            pass
        # lane A's call (stand-in): the context it reads, the answer it gives
        xtape.append((B["VMCALL"], False, [qf, x["ts0"] + 1]))
        ctx_fields = [F["METHOD"], F["ARGS"], F["RECV"], F["SIGNER"], F["PRED"]]
        for fid in ctx_fields:
            ln = fields.use_len(S(fid))
            xtape.append((B["FLEN"], False, [S(fid), ln]))
            for k in range(ln):
                xtape.append((B["FB"], False, [S(fid), k, fields.use(S(fid), k)]))
        for fid, w in [(F["PK"], 32), (F["GAS"], 8), (F["DEPOSIT"], 16), (F["AMT"], 16), (F["LOCKED"], 16),
                       (F["USAGE"], 8), (F["CODEH"], 32), (F["HEIGHT"], 8), (F["TSTAMP"], 8), (F["EPOCHH"], 8)]:
            for k in range(w):
                xtape.append((B["FB"], False, [S(fid), k, fields.use(S(fid), k)]))
        for mt in (MT["AH"], MT["SEED"]):
            for k in range(32):
                xtape.append((B["FB"], False, [msg_id(qf, mt), k, fields.use(msg_id(qf, mt), k)]))
        xtape.append((B["VMRES"], True, [qf, x["tse"], 1, len(x["logs"]), 0, 0]))
        # the VM answer's fields, one send per consumer (counted after all uses below)
        # lane B's account read / write (stand-in)
        kl = len(x["key"])
        x["kl"] = kl
        xtape.append((B["SRQ"], False, [x["ts0"], 0, kl, PTR_KEY]))
        for j, b in enumerate(x["key"]):
            xtape.append((B["HB"], False, [x["ts0"], PTR_KEY + j, b]))
        xtape.append((B["SRS"], True, [x["ts0"], 1, 72, PTR_VAL]))
        for j, b in enumerate(x["pre"]):
            xtape.append((B["HBR"], True, [x["ts0"], PTR_VAL + j, b]))
        tsw = x["tse"] + 1
        xtape.append((B["SREQ"], False, [tsw, 1, 0, kl, PTR_KEY, 72, PTR_VAL]))
        for j, b in enumerate(x["key"]):
            xtape.append((B["HB"], False, [tsw, PTR_KEY + j, b]))
        for j, b in enumerate(bytes.fromhex(x["R"]["after"]["recvAcct"]["encode"])):
            xtape.append((B["HB"], False, [tsw, PTR_VAL + j, b]))
        # statement: the outcome leaf and the outgoing refund receipt's hash
        tape.append((B["OUTC"], False, [qf] + [int(b) for b in bytes.fromhex(x["out"]["leaf"])]))
        tape.append((B["OUTR"], False, [qf] + [int(b) for b in bytes.fromhex(x["refund"]["hash"] if "hash" in x["refund"] else hashlib.sha256(bytes.fromhex(x["refund"]["encode"])).hexdigest())]))
    fields.use_len(sidof(0, F["COUNT"]))  # RX's last row
    # statement: the receipt list digest = w.appliedReceiptsHash (the witness's, bound by INTAKE)
    rdig = list(bytes.fromhex(run["appliedReceiptsHash"]))
    for k in range(32):
        assert fields.use(msg_id(0, MT["RL"]), k) == rdig[k]
        tape.append((B["FB"], False, [msg_id(0, MT["RL"]), k, rdig[k]]))
    # the VM-side fields are sent by the stand-in once per consumer
    for x in rxs:
        qf = x["q"]
        vm_fids = [F["VBURNT"], F["VUSED"], F["VCOMP"], F["VBAL"], F["VUSAGE"], F["VSUB"], F["RET"]] + \
                  [F["LOG0"] + i for i in range(len(x["logs"]))]
        for fid in vm_fids:
            sid = sidof(qf, fid)
            for (s_, k), b in sorted(fields.fb.items()):
                if s_ == sid:
                    for _ in range(fields.fb_use[(s_, k)]):
                        xtape.append((B["FB"], True, [sid, k, b]))
            if sid in fields.flen:
                for _ in range(fields.flen_use[sid]):
                    xtape.append((B["FLEN"], True, [sid, fields.flen[sid]]))

    # RX offers its fields with constant multiplicities (Rx.lean: hgt ×3, the others ×1)
    for x in rxs:
        qf = x["q"]
        for fid, w, mlt in [(F["AMT2"], 16, 1), (F["REFUND"], 16, 1), (F["GB"], 8, 1), (F["TB"], 16, 1),
                            (F["LEAFN"], 4, 1), (F["HEIGHT"], 8, 3), (F["RANDV"], 32, 1), (F["TSTAMP"], 8, 1),
                            (F["EPOCHH"], 8, 1)]:
            for k in range(w):
                check(fields.fb_use[(sidof(qf, fid), k)] == mlt, ("RX field multiplicity", fid, k, fields.fb_use[(sidof(qf, fid), k)]))

    # ----- MSG rows ----------------------------------------------------------------------------
    msg = Trace(names["MSG"])
    flat = []
    for m, mf, mt, data, ts, ptr in messages:
        for j, r in enumerate(rows_by_msg[m]):
            flat.append((m, mf, mt, ts, ptr, j, r))
    sch_count = Counter()
    for i, (m, mf, mt, ts, ptr, j, r) in enumerate(flat):
        row = msg.row()
        e = r["e"]
        for f in sch_fields:
            msg.set(row, f, e[f])
        sch_count[(e["mt"], e["s"])] += 1
        last_seg = r["last"]
        endm = r.get("endm", 0)
        nxt = flat[i + 1] if i + 1 < len(flat) else None
        msg.set(row, "mf", mf)
        msg.set(row, "qf", r["qf"])
        msg.set(row, "j", j)
        msg.set(row, "k", r["k"])
        msg.set(row, "L", r["L"])
        msg.set(row, "e", 1 if last_seg else 0)
        msg.set(row, "k0", 1 if r["k"] == 0 else 0)
        msg.set(row, "b", r["b"])
        msg.set(row, "first", 1 if j == 0 else 0)
        msg.set(row, "endm", endm)
        inm = 1 if (nxt is not None and nxt[0] == m) else 0
        msg.set(row, "inm", inm)
        z = r["z"] if last_seg else 0
        msg.set(row, "z", z)
        msg.set(row, "ns", e["nextS"] + z * (e["skipS"] - e["nextS"]))
        islenp = 1 if r["kind"] in ("kLP", "kLE") else 0
        msg.set(row, "setL", islenp * (1 if last_seg else 0) * (1 - z))
        if r["kind"] in ("kLP", "kLE", "kCNT"):
            pw = 256 ** r["k"]
            acc = val(data_slice(flat, i, r))
        else:
            pw, acc = 0, 0
        msg.set(row, "pw", pw)
        msg.set(row, "pb", pw * r["b"])
        msg.set(row, "acc", acc)
        if islenp and last_seg and acc != 0:
            msg.set(row, "accInv", inv(acc))
        msg.set(row, "ts", ts)
        msg.set(row, "ptr", ptr)
        if endm and nxt is not None:
            gap = nxt[0] - m - 1
            assert gap >= 0
            msg.setv(row, "dm", le(gap, 3))
        if r["kind"] == "kD":
            msg.setv(row, "fm", bits(fields.fb_use[(r["sid"], r["k"])], 4))
        if r["kind"] in ("kLP", "kCNT") and last_seg:
            msg.setv(row, "lm", bits(fields.flen_use[r["sid"]], 4))
    n_msg_rows = len(msg.rows)
    h = 1 << max(2, (n_msg_rows - 1).bit_length())
    if tmpl:
        pin = json.load(open(tmpl))["heights"]["MSG"]
        assert n_msg_rows <= 1 << pin, f"MSG: {n_msg_rows} rows exceed the template's 2^{pin}"
        h = 1 << pin
    pad_e = by[(MT["PAD"], 0)][1]
    for _ in range(h - n_msg_rows):
        row = msg.row()
        for f in sch_fields:
            msg.set(row, f, pad_e[f])
        sch_count[(MT["PAD"], 0)] += 1

    # ----- SCHT: one row per schema entry (the entries are the preprocessed columns `e`; F-2) ---
    scht = Trace(names["SCHT"])
    for i in range(256):
        row = scht.row()
        e = entries[min(i, len(entries) - 1)]
        for j, f in enumerate(sch_fields):
            scht.set(row, "e", e[f], j)
        c = sch_count[(e["mt"], e["s"])] if i < len(entries) else 0
        for b, v in enumerate(bits(c, nb_sch)):
            scht.set(row, "m", v, b)

    # ----- DG ----------------------------------------------------------------------------------
    dg = Trace(names["DG"])
    sha_msgs = []
    for m, mf, mt, data, ts, ptr in messages:
        if mt in (MT["KEYR"], MT["APRE"], MT["KEYW"], MT["APOST"]):
            continue
        d = list(hashlib.sha256(bytes(data)).digest())
        sha_msgs.append({"id": m, "bytes": bytes(data).hex()})
        row = dg.row()
        dg.set(row, "act", 1)
        dg.set(row, "qf", mf)
        dg.set(row, "mt", mt)
        dg.set(row, "len", len(data))
        dg.setv(row, "d", d)
        uses = {fields.fb_use[(m, k)] for k in range(32)}
        assert len(uses) == 1, ("digest bytes used unevenly", m, uses)
        dg.setv(row, "fm", bits(uses.pop(), 3))

    # ----- RX ----------------------------------------------------------------------------------
    rx = Trace(names["RX"])
    pubnames = names["pub"]
    pubs = {}

    def setpub(name, vs):
        for j, v in enumerate(vs):
            pubs[name if len(vs) == 1 else f"{name}.{j}"] = v

    tot_in = dict(gin=int(recs[0]["before"]["gas"]), cin=int(recs[0]["before"]["compute"]),
                  tbin=int(recs[0]["before"]["txBurnt"]), oth=int(recs[0]["before"]["otherBurnt"]),
                  sbin=int(recs[0]["before"]["subsidized"]), wgin=int(recs[0]["before"]["wasmGas"]),
                  noin=int(recs[0]["before"]["nOutcomes"]), ngin=int(recs[0]["before"]["nOutgoing"]))
    cur = dict(tot_in)
    egp = int(env["gasPrice"])
    glim = int(env["gasLimit"])
    for x in rxs:
        r = rx.row()
        I = x["in"]
        if mut("vmburnt"):
            # the receipt row charges 1 gas less VM burnt gas than the Wasm side answered
            I = dict(I, vb=le(val(I["vb"]) - 1, 8))
            applied.append("vmburnt")
        A = 1
        rx.set(r, "act", 1)
        rx.set(r, "la1", 1 if x["q"] == n else 0)
        rx.set(r, "qf", x["q"])
        rx.set(r, "seg", 0)
        rx.set(r, "lm", x["lm"])
        rx.set(r, "la", x["la"])
        rx.set(r, "lp", x["lp"])
        rx.set(r, "kl", x["kl"])
        rx.set(r, "ts0", x["ts0"])
        rx.set(r, "tse", x["tse"])
        rx.set(r, "noin", cur["noin"])
        rx.set(r, "ngin", cur["ngin"])
        byte_vals = {}

        def B_(name, bs):
            rx.setv(r, name, bs)
            byte_vals[name] = bs

        B_("egp", le(egp, 16)); B_("hgt", le(int(env["height"]), 8)); B_("tst", le(int(env["blockTimestamp"]), 8))
        B_("eph", le(int(env["epochHeight"]), 8)); B_("rv", list(bytes.fromhex(env["randomValue"]))); B_("glim", le(glim, 8))
        B_("gin", le(cur["gin"], 8)); B_("cin", le(cur["cin"], 8)); B_("tbin", le(cur["tbin"], 16))
        B_("oth", le(cur["oth"], 16)); B_("sbin", le(cur["sbin"], 16)); B_("wgin", le(cur["wgin"], 16))
        for g in ("gp", "gas", "dep", "amt", "lck", "ch", "vb", "vu", "vc", "vbal", "vus", "vsub", "rrh", "leaf"):
            B_(g, I[g])
        gp, gas, dep = val(I["gp"]), val(I["gas"]), val(I["dep"])
        vb, vu, vc, vbal, vus, vsub = (val(I[g]) for g in ("vb", "vu", "vc", "vbal", "vus", "vsub"))
        amt, lck = val(I["amt"]), val(I["lck"])
        nbv = x["lm"] + x["la"]
        B_("nb", le(nbv, 3))
        fcx = FC_BASE_EXEC + FC_BYTE_EXEC * nbv
        B_("fcx", le(fcx, 8))
        cfx = lin_carries([le(FC_BASE_EXEC, 8)[k] + mul_terms(le(nbv, 3), le(FC_BYTE_EXEC, 3), 8)[k] for k in range(8)], le(fcx, 8), 0)
        rx.setv(r, "cfx", sum((le(c, 2) for c in cfx), []))

        def lin3(name, cyname, a, b_, c_, n_):
            v = a + b_ + c_
            B_(name, le(v, n_))
            cy = lin_carries([le(a, n_)[k] + le(b_, n_)[k] + le(c_, n_)[k] for k in range(n_)], le(v, n_), 0)
            rx.setv(r, cyname, cy)
            return v

        gb = lin3("gb", "cgb", NAR_EXEC, fcx, vb, 8)
        gu = lin3("gu", "cgu", NAR_EXEC, fcx, vu, 8)
        cu = lin3("cu", "ccu", NAR_EXEC, fcx, vc, 8)
        check(gb == x["gb"] or mut("gasburnt"), "gas burnt")
        if mut("gasburnt"):
            gb = x["gb"]
            B_("gb", le(gb, 8))  # the RX row too: its lin chain cannot hold

        def add2(name, cyname, a, b_, n_, rname=None, top=0, na=None, nb_=None):
            """a + b = r + 2^(8n) top, with `name` = b if rname given (sub form) else r"""
            pass

        def chain2(rbytes, abytes, bbytes, cyname, top):
            n_ = len(rbytes)
            cy = lin_carries([abytes[k] + bbytes[k] for k in range(n_)], rbytes, top)
            rx.setv(r, cyname, cy)

        # dvu: vb + dvu = vu
        B_("dvu", le(vu - vb, 8)); chain2(le(vu, 8), le(vb, 8), le(vu - vb, 8), "cdv", 0)
        B_("ad", le(amt + dep, 16)); chain2(le(amt + dep, 16), le(amt, 16), le(dep, 16), "cad", 0)
        rx.set(r, "iam", inv(sum(255 - b for b in I["amt"])))
        rx.set(r, "ich", inv(sum(I["ch"])))
        req = STORAGE_PER_BYTE * vus
        B_("req", le(req, 16))
        crq = lin_carries(mul_terms(le(vus, 8), le(STORAGE_PER_BYTE, 8), 16), le(req, 16), 0)
        rx.setv(r, "crq", sum((le(c, 2) for c in crq), []))
        ak = vbal + lck
        B_("ak", le(ak, 16)); chain2(le(ak, 16), le(vbal, 16), le(lck, 16), "cak", 0)
        b1 = 1 if ak < req else 0
        s1 = (ak - req) % (1 << 128)
        B_("s1", le(s1, 16)); rx.set(r, "b1", b1)
        chain2(le(ak, 16), le(req, 16), le(s1, 16), "cs1", b1)
        b2 = 1 if vus > ZERO_BALANCE_LIMIT else 0
        s2 = (ZERO_BALANCE_LIMIT - vus) % (1 << 64)
        B_("s2", le(s2, 8)); rx.set(r, "b2", b2)
        chain2(le(ZERO_BALANCE_LIMIT, 8), le(vus, 8), le(s2, 8), "cs2", b2)
        assert b1 * b2 == 0
        bm = 1 if gp < egp else 0
        dmn = (gp - egp) % (1 << 128)
        B_("dmn", le(dmn, 16)); rx.set(r, "bm", bm)
        chain2(le(gp, 16), le(egp, 16), le(dmn, 16), "cmn", bm)
        burn = min(gp, egp)
        B_("burn", le(burn, 16))
        if len(x["pred"]) != 6:
            rx.set(r, "sA", 1)
            rx.set(r, "iA", inv(len(x["pred"]) - 6))
        else:
            rx.set(r, "sB", 1)
            pb = list(x["pred"])
            B_("pb", pb)
            rx.set(r, "iB", inv(sum((pb[k] - SYSTEM[k]) ** 2 for k in range(6))))
        if "pb" not in byte_vals:
            B_("pb", [0] * 6)
        pexec = fcx + NAR_EXEC
        B_("pexec", le(pexec, 8)); chain2(le(pexec, 8), le(fcx, 8), le(NAR_EXEC, 8), "cpx", 0)
        tot = gas + pexec
        B_("tot", le(tot, 8)); chain2(le(tot, 8), le(gas, 8), le(pexec, 8), "cto", 0)
        gross = tot - gu
        B_("gross", le(gross, 8)); chain2(le(tot, 8), le(gu, 8), le(gross, 8), "cgr", 0)

        def mul(name, cyname, a, na, b_, nb_, nr):
            v = a * b_
            B_(name, le(v, nr))
            cy = lin_carries(mul_terms(le(a, na), le(b_, nb_), na + nb_), le(v, nr) + [0] * (na + nb_ - nr), 0)
            rx.setv(r, cyname, sum((le(c, 2) for c in cy), []))
            return v

        unu = mul("unu", "cun", gp, 16, gross, 8, 16)
        gpb = gp - burn
        B_("gpb", le(gpb, 16)); chain2(le(gp, 16), le(burn, 16), le(gpb, 16), "cgp", 0)
        sur = mul("sur", "csu", gpb, 16, gb, 8, 16)
        mul("bc", "cbc", burn, 16, CREATE_ACCOUNT_EXEC, 6, 16)
        rf = unu + sur
        if mut("refund"):
            rf = x["rf"]  # the claimed refund: the chain unu + sur = rf cannot hold
        B_("rf", le(rf, 16))
        if not mut("refund"):
            chain2(le(rf, 16), le(unu, 16), le(sur, 16), "crf", 0)
        rx.set(r, "irf", inv(sum(le(rf, 16))))
        tb = mul("tb", "ctb", burn, 16, gb, 8, 16)
        fc3 = 3 * vb
        B_("fc3", le(fc3, 8))
        rx.setv(r, "cf3", lin_carries([3 * b for b in le(vb, 8)], le(fc3, 8), 0))
        q10, r10 = divmod(fc3, 10)
        B_("q10", le(q10, 8)); B_("r10", [r10])
        rx.setv(r, "cq", lin_carries([10 * le(q10, 8)[k] + (r10 if k == 0 else 0) for k in range(8)], le(fc3, 8), 0))
        rew = mul("rew", "crw", burn, 16, q10, 8, 16)
        amt2 = vbal + rew
        B_("amt2", le(amt2, 16)); chain2(le(amt2, 16), le(vbal, 16), le(rew, 16), "cam", 0)
        txb = tb - rew
        B_("txb", le(txb, 16)); chain2(le(tb, 16), le(rew, 16), le(txb, 16), "ctx", 0)
        nxt = dict(cur)
        nxt["tbin"] = cur["tbin"] + txb
        nxt["sbin"] = cur["sbin"] + vsub
        nxt["wgin"] = cur["wgin"] + vb
        nxt["gin"] = cur["gin"] + gb
        nxt["cin"] = cur["cin"] + cu
        nxt["noin"] = cur["noin"] + 1
        nxt["ngin"] = cur["ngin"] + 1
        B_("tbout", le(nxt["tbin"], 16)); chain2(le(nxt["tbin"], 16), le(cur["tbin"], 16), le(txb, 16), "ctbo", 0)
        B_("sbout", le(nxt["sbin"], 16)); chain2(le(nxt["sbin"], 16), le(cur["sbin"], 16), le(vsub, 16), "csbo", 0)
        B_("wgout", le(nxt["wgin"], 16)); chain2(le(nxt["wgin"], 16), le(cur["wgin"], 16), le(vb, 8) + [0] * 8, "cwg", 0)
        B_("gout", le(nxt["gin"], 8)); chain2(le(nxt["gin"], 8), le(cur["gin"], 8), le(gb, 8), "cgo", 0)
        B_("cout", le(nxt["cin"], 8)); chain2(le(nxt["cin"], 8), le(cur["cin"], 8), le(cu, 8), "cco", 0)
        dgl = glim - cur["cin"] - 1
        assert dgl >= 0, "compute >= gas limit: the receipt would be delayed"
        B_("dgl", le(dgl, 8))
        rx.setv(r, "cgl", lin_carries([le(cur["cin"], 8)[k] + le(dgl, 8)[k] + (1 if k == 0 else 0) for k in range(8)], le(glim, 8), 0))
        rx.set(r, "igs", inv(sum(I["gas"])))
        B_("e1", le(256 - x["lm"], 2)); B_("e2", le(4194304 - x["la"], 3))
        B_("lmb", le(x["lm"], 2)); B_("lab", le(x["la"], 3))
        B_("gte", le(x["tse"] - x["ts0"] - 2, 3))
        for i in range(len(x["logs"])):
            rx.set(r, "lg", 1, i)
        # Lean run's totals after the receipt
        aft = x["R"]["after"]
        check(nxt["gin"] == int(aft["gas"]) and nxt["cin"] == int(aft["compute"]), "gas / compute totals")
        check(nxt["tbin"] == int(aft["txBurnt"]) and nxt["sbin"] == int(aft["subsidized"]), "burnt / subsidized")
        check(nxt["wgin"] == int(aft["wasmGas"]) and int(aft["otherBurnt"]) == cur["oth"], "wasm gas / other burnt")
        cur = nxt
        x["byte_vals"] = byte_vals
    # the last receipt's outputs = public values
    setpub("egp", le(egp, 16)); setpub("hgt", le(int(env["height"]), 8))
    setpub("tst", le(int(env["blockTimestamp"]), 8)); setpub("eph", le(int(env["epochHeight"]), 8))
    setpub("rv", list(bytes.fromhex(env["randomValue"]))); setpub("glim", le(glim, 8)); setpub("seg", [0])
    setpub("tIn", [rxs[0]["ts0"]]); setpub("tOut", [rxs[-1]["tse"] + 2])
    for g, w in [("gin", 8), ("cin", 8), ("tbin", 16), ("oth", 16), ("sbin", 16), ("wgin", 16)]:
        setpub(g, le(tot_in[g], w))
    setpub("noin", [tot_in["noin"]]); setpub("ngin", [tot_in["ngin"]])
    last = recs[-1]["after"]
    want_out = dict(gout=int(last["gas"]), cout=int(last["compute"]), tbout=int(last["txBurnt"]),
                    othout=int(last["otherBurnt"]), sbout=int(last["subsidized"]), wgout=int(last["wasmGas"]))
    for g, w in [("gout", 8), ("cout", 8), ("tbout", 16), ("othout", 16), ("sbout", 16), ("wgout", 16)]:
        setpub(g, le(want_out[g], w))
    setpub("noout", [int(last["nOutcomes"])]); setpub("ngout", [int(last["nOutgoing"])])
    # F-2: the `rt` resume edge's boundary pair (lane I's driver plan), checked against the Lean run
    assert plan, "--plan PLAN.json (lane I's driver plan) is required: the resume leaf's public values"
    import rtbnd
    b_in, b_out, e_in, e_out, d_in, d_out = rtbnd.pair(plan, "RT resume")
    assert len(rxs) == 1, "one receipt per resume segment"
    x0 = rxs[0]
    check(b_in["phase"] == 6 and b_in["inCall"] and b_out["phase"] == 1 and not b_out["inCall"], "resume phases")
    check(b_in["gasUsed"] == tot_in["gin"] == b_in["gasBurnt"] and b_in["compute"] == tot_in["cin"], "B_in totals = Lean RS before")
    check(b_out["gasUsed"] == want_out["gout"] == b_out["gasBurnt"] and b_out["compute"] == want_out["cout"], "B_out totals = Lean RS after")
    check(b_in["balanceBurnt"] == tot_in["tbin"] and b_out["balanceBurnt"] == want_out["tbout"], "balance burnt = RS txBurnt")
    check(b_in["rPrepaid"] == x0["gas"] and b_out["rBurnt"] == x0["vb"] and b_out["rUsed"] == x0["vu"], "prepaid / VM burnt / used")
    if mut("bndgas"):
        # the claimed output boundary charges the chunk 1 more gas than the receipt step
        e_out = rtbnd.bndrec.encode(dict(b_out, gasUsed=b_out["gasUsed"] + 1, gasBurnt=b_out["gasBurnt"] + 1))
        applied.append("bndgas")
    if mut("bndprepaid"):
        # the call's boundary claims 1 gas more prepaid than the receipt attached
        e_in = rtbnd.bndrec.encode(dict(b_in, rPrepaid=b_in["rPrepaid"] + 1))
        applied.append("bndprepaid")
    if mut("bndburnt"):
        # the output boundary's in-flight burnt gas differs from the VM's answer
        e_out = rtbnd.bndrec.encode(dict(b_out, rBurnt=b_out["rBurnt"] - 1))
        applied.append("bndburnt")
    setpub("bin", list(e_in)); setpub("bout", list(e_out))
    print(f"resume boundary: d_in {d_in[:16]}.. d_out {d_out[:16]}.. (lane I plan) = bdigest of the public records")
    pub_vals = [pubs[nm] for nm in pubnames]
    with open(f"{out}/expected_pubs.bin", "wb") as f:
        f.write(struct.pack(f"<{len(pub_vals)}I", *[v % P for v in pub_vals]))
    if mut("statement"):
        # the statement claims one more gas used by the chunk than the Lean run
        pub_vals[pubnames.index("gout.0")] += 1
        applied.append("statement")

    # ----- RNG ---------------------------------------------------------------------------------
    rng_count = Counter()
    for (m, mf, mt, ts, ptr, j, rr) in flat:
        rng_count[rr["b"]] += 1
    for row in msg.rows[:len(flat)]:
        for d in range(3):
            rng_count[msg.get(row, "dm", d)] += 1
    for row in msg.rows[len(flat):]:
        pass
    for x in rxs:
        rrow = rx.rows[x["q"] - 1]
        for g, w in names_groups(names["RX"], names["rxBytes"]):
            for k in range(w):
                rng_count[rx.get(rrow, g, k if w > 1 else None)] += 1
        rng_count[rx.get(rrow, "r10") + 246] += 1
    rng = Trace(names["RNG"])
    for v in range(256):
        row = rng.row()
        rng.set(row, "v", v)
        rng.setv(row, "m", bits(rng_count[v], 20))
    assert sum(rng_count[v] for v in range(256)) == sum(rng_count.values()), "RNG value >= 256"

    # ----- write -------------------------------------------------------------------------------
    for name, t in [("RNG", rng), ("SCHT", scht), ("MSG", msg), ("DG", dg), ("RX", rx)]:
        t.write(f"{out}/{name}.bin")
    json.dump(sha_msgs, open(f"{out}/sha_msgs.json", "w"))
    json.dump([[b, s, m] for b, s, m in tape], open(f"{out}/tape.json", "w"))
    json.dump([[b, s, m] for b, s, m in xtape], open(f"{out}/xtape.json", "w"))
    with open(f"{out}/pubs.bin", "wb") as f:
        f.write(struct.pack(f"<{len(pub_vals)}I", *[v % P for v in pub_vals]))
    # F-2: the boundary pair's place in the public values; the template's tables
    json.dump([pubnames.index("bin.0"), 784, 408], open(f"{out}/bnd.json", "w"))
    json.dump(["SHA", "RNG", "SCHT", "MSG", "DG", "RX"], open(f"{out}/tables.json", "w"))
    if tmpl:
        json.dump(json.load(open(tmpl)), open(f"{out}/template.json", "w"), indent=1)
    expected = dict(
        appliedReceiptsHash=run["appliedReceiptsHash"],
        outcomes=[dict(q=x["q"], leaf=x["out"]["leaf"], gasBurnt=x["out"]["gasBurnt"],
                       tokensBurnt=x["out"]["tokensBurnt"], status=x["out"]["status"],
                       receiptIds=x["out"]["receiptIds"], refundHash=hashlib.sha256(bytes.fromhex(x["refund"]["encode"])).hexdigest(),
                       refundAmount=x["refund"]["body"]["actions"][0]["base"]["deposit"],
                       accountPost=x["R"]["after"]["recvAcct"]["encode"]) for x in rxs],
        totalsOut=want_out)
    json.dump(expected, open(f"{out}/expected.json", "w"), indent=1)
    print(f"M5T1 trace: {n} receipt(s), MSG rows {len(flat)} (2^{(len(msg.rows) - 1).bit_length()}), "
          f"messages {len(messages)}, SHA messages {len(sha_msgs)}, DG {len(dg.rows)}, tape {len(tape)}, "
          f"xtape {len(xtape)}")
    if mutant and not applied:
        print(f"mutant {mutant}: NOT APPLICABLE")
        sys.exit(3)
    if mutant:
        print(f"mutant applied: {applied}")


def names_groups(names, groups):
    """(group, width) for the byte groups of RX, from the column names."""
    out = []
    for g in groups:
        w = sum(1 for nm in names if nm == g or nm.startswith(g + "."))
        out.append((g, w))
    return out


def data_slice(flat, i, r):
    """the 4 bytes of the u32 segment the row `i` belongs to, up to and including this row"""
    k = r["k"]
    bs = [flat[i - k + t][6]["b"] for t in range(k + 1)]
    return bs


if __name__ == "__main__":
    main()
