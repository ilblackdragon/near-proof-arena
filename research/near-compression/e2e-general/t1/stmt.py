#!/usr/bin/env python3
"""The D-2 public statement of a claim-v3 case, with byte offsets, and statement mutants.

Plan: docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md §2.1 (D-2), §3.4; Lean
`NearSpecV3.E2E.Statement` (`PublicStmt = ChunkPub + SecC`, `assemble`).

* Section A (`ChunkPub`: protocol_version, chain_id, epoch_id, chunk_inner) and section C (`SecC`:
  rs parts, epochs, epoch_start_after, apply_facts, tx_valid, genesis_chunk_extra) are public.
* Section B (the block records) is private (D-2).
* `S` (the statement bytes the wrap hashes into `claimDigest`) is lane E's canonical encoding
  (plan §3.4.1, Lean `E2E/StmtEnc.lean`, `PublicStmt.encode`): the claim-v3 encoding of the claim
  with an **empty** section B, `S = stmtPre ++ 00 00 00 00 ++ stmtPost`, i.e. the claim bytes with
  the block vector (count included, `claim[b0:b1]`) replaced by `u32 0`. `claimDigest = bdigest(S)`
  (42-B SHA-384). T1: |S| = 1,007 B, claimDigest `bb5aad11…9f2f01` (`RealChunkT1.t1_S_len`,
  `t1_claimDigest`); `lean/StmtEval.lean` evaluates the Lean definitions on any claim file and
  `t1.py run` checks this module against it byte for byte. (I-1 used the claim with the vector and
  its count cut out: 1,003 B, superseded.)

Mutants change one public field each (section A or C, never B) and are re-spliced with the
original section B and witness, so the Lean checker sees `assemble(ci', secB, secC')`.
"""
import hashlib
import json
import os
import struct
import subprocess


class Field:
    def __init__(self, name, sec, off, size, kind):
        self.name, self.sec, self.off, self.size, self.kind = name, sec, off, size, kind

    def __repr__(self):
        return f"Field({self.name},{self.sec},{self.off},{self.size},{self.kind})"


class Rd:
    """borsh reader that records field offsets."""

    def __init__(self, b, base=0, sec="A"):
        self.b, self.i, self.base, self.sec, self.fields = b, 0, base, sec, []

    def take(self, n, name=None, kind="raw"):
        if self.i + n > len(self.b):
            raise ValueError("truncated")
        if name:
            self.fields.append(Field(name, self.sec, self.base + self.i, n, kind))
        r = self.b[self.i:self.i + n]
        self.i += n
        return r

    def u8(self, name=None): return self.take(1, name, "u8")[0]
    def u16(self, name=None): return struct.unpack("<H", self.take(2, name, "u16"))[0]
    def u32(self, name=None): return struct.unpack("<I", self.take(4, name, "u32"))[0]
    def u64(self, name=None): return struct.unpack("<Q", self.take(8, name, "u64"))[0]
    def u128(self, name=None): return int.from_bytes(self.take(16, name, "u128"), "little")
    def hash(self, name=None): return self.take(32, name, "hash")

    def bytes(self, name=None):
        n = self.u32()
        return self.take(n, name, "bytes")


PK_LEN = {0: 32, 1: 64}


def parse_inner(inner):
    """ShardChunkHeaderInner V4/V5 (spec_check_v3.read_inner) with field offsets relative to the
    inner bytes. Returns (fields, info)."""
    r = Rd(inner, 0, "A.inner")
    info = {}
    info["version"] = r.u8("inner.version")
    for f in ("prev_block_hash", "prev_state_root", "prev_outcome_root", "encoded_merkle_root"):
        info[f] = r.hash("inner." + f).hex()
    info["encoded_length"] = r.u64("inner.encoded_length")
    info["height_created"] = r.u64("inner.height_created")
    info["shard_id"] = r.u64("inner.shard_id")
    info["prev_gas_used"] = r.u64("inner.prev_gas_used")
    info["gas_limit"] = r.u64("inner.gas_limit")
    info["prev_balance_burnt"] = r.u128("inner.prev_balance_burnt")
    info["prev_outgoing_receipts_root"] = r.hash("inner.prev_outgoing_receipts_root").hex()
    info["tx_root"] = r.hash("inner.tx_root").hex()
    r.fields.append(Field("inner.prev_validator_proposals.count", r.sec, r.i, 4, "u32"))
    props = []
    for k in range(r.u32()):
        assert r.u8() == 0
        acc = r.bytes(f"inner.prev_validator_proposals[{k}].account")
        t = r.u8()
        pk = r.take(PK_LEN[t])
        stake = r.u128(f"inner.prev_validator_proposals[{k}].stake")
        props.append((acc.hex(), t, pk.hex(), stake))
    info["prev_validator_proposals"] = props
    info["proposals_end"] = r.i
    assert r.u8() == 0  # CongestionInfo tag
    info["congestion"] = dict(delayed_receipts_gas=r.u128("inner.congestion.delayed_receipts_gas"),
                              buffered_receipts_gas=r.u128("inner.congestion.buffered_receipts_gas"),
                              receipt_bytes=r.u64("inner.congestion.receipt_bytes"),
                              allowed_shard=r.u16("inner.congestion.allowed_shard"))
    assert r.u8() == 0  # BandwidthRequests tag
    r.fields.append(Field("inner.bandwidth_requests.count", r.sec, r.i, 4, "u32"))
    bw = []
    for k in range(r.u32()):
        bw.append((r.u16(f"inner.bandwidth_requests[{k}].to_shard"),
                   r.take(5, f"inner.bandwidth_requests[{k}].bitmap", "raw").hex()))
    info["bandwidth_requests"] = bw
    info["bw_end"] = r.i
    if info["version"] == 4:
        info["proposed_split_off"] = r.i
        t = r.u8()
        info["proposed_split"] = None if t == 0 else "some"
        if t == 1:
            r.bytes(); r.u64(); r.u64()
    assert r.i == len(inner), "inner trailing bytes"
    return r.fields, info


def parse_claim(b):
    """Claim-v3 (spec_check_v3.decode_claim) with offsets. Returns dict with `fields` (public
    fields, absolute offsets), `inner_off`/`inner_len`, `secB` = (start, end) of the block vector
    (count included), and decoded summaries."""
    r = Rd(b, 0, "A")
    fmt = r.bytes(); stmt_id = r.bytes()
    out = {"format": fmt.decode(), "statement": stmt_id.decode()}
    out["pv"] = r.u32("A.protocol_version")
    out["chain_id"] = r.bytes("A.chain_id").decode()
    out["epoch_id"] = r.hash("A.epoch_id").hex()
    n = r.u32()
    out["inner_off"], out["inner_len"] = r.i, n
    r.i += n
    b0 = r.i
    nb = r.u32()
    for _ in range(nb):
        r.u8(); r.hash(); r.bytes(); r.bytes()
        for _ in range(r.u32()):
            r.bytes(); r.u64()
    out["secB"] = (b0, r.i)
    out["n_blocks"] = nb
    r.sec = "C"
    out["rs"] = (r.u16("C.rs_data_parts"), r.u16("C.rs_total_parts"))
    epochs = []
    for e in range(r.u32()):
        eid = r.hash(f"C.epochs[{e}].epoch_id").hex()
        epv = r.u32(f"C.epochs[{e}].protocol_version")
        eh = r.u64(f"C.epochs[{e}].height")
        lay = r.bytes(f"C.epochs[{e}].layout")
        r.fields.append(Field(f"C.epochs[{e}].validators.count", "C", r.i, 4, "u32"))
        vals = []
        for v in range(r.u32()):
            acc = r.bytes(f"C.epochs[{e}].validators[{v}].account")
            st = r.u128(f"C.epochs[{e}].validators[{v}].stake")
            vals.append((acc.decode(), st))
        epochs.append(dict(epoch_id=eid, pv=epv, height=eh, layout_len=len(lay), validators=vals))
    out["epochs"] = epochs
    r.fields.append(Field("C.epoch_start_after.count", "C", r.i, 4, "u32"))
    out["epoch_start_after"] = [r.u8(f"C.epoch_start_after[{k}]") for k in range(r.u32())]
    facts = []
    for k in range(r.u32()):
        vu_off = r.i
        t = r.u8(f"C.apply_facts[{k}].validator_update.tag")
        if t == 1:
            for _ in range(2):
                for _ in range(r.u32()):
                    r.bytes(); r.u128()
            if r.u8() == 1:
                r.bytes()
        ms = r.u128(f"C.apply_facts[{k}].minimum_stake")
        sg = r.u8(f"C.apply_facts[{k}].split_gate.tag")
        if sg == 1:
            r.u64(); r.u64(); r.u64()
            for _ in range(r.u32()):
                r.u64()
            for _ in range(r.u32()):
                r.u64()
        facts.append(dict(validator_update=bool(t), minimum_stake=ms, split_gate=bool(sg), vu_off=vu_off))
    out["apply_facts"] = facts
    r.fields.append(Field("C.tx_valid.count", "C", r.i, 4, "u32"))
    out["tx_valid"] = [r.u8(f"C.tx_valid[{k}]") for k in range(r.u32())]
    out["gce_off"] = r.i
    t = r.u8("C.genesis_chunk_extra.tag")
    out["genesis_chunk_extra"] = None if t == 0 else r.bytes().hex()
    assert r.i == len(b), "claim trailing bytes"
    inner = b[out["inner_off"]:out["inner_off"] + n]
    ifields, iinfo = parse_inner(inner)
    for f in ifields:
        f.off += out["inner_off"]
    out["inner"] = iinfo
    out["fields"] = r.fields + ifields
    return out


EMPTY_B = b"\x00\x00\x00\x00"  # encList BlockRec.encode [] (StmtEnc.encList_blocks_nil)


def statement_bytes(claim, pc=None):
    """S = PublicStmt.encode: stmtPre ++ u32 0 ++ stmtPost (StmtEnc.encode_splice)."""
    pc = pc or parse_claim(claim)
    b0, b1 = pc["secB"]
    return claim[:b0] + EMPTY_B + claim[b1:]


def stmt_pre_post(s_bytes, b0):
    """(stmtPre, stmtPost) of S, whose empty block vector sits at `b0`."""
    assert s_bytes[b0:b0 + 4] == EMPTY_B, "S: no empty block vector at b0"
    return s_bytes[:b0], s_bytes[b0 + 4:]


def splice_secB(s_bytes, secB, b0):
    """assemble (StmtEnc.assemble_splice): stmtPre ++ encList BlockRec.encode secB ++ stmtPost, where
    `secB` is the block vector's bytes, count included."""
    pre, post = stmt_pre_post(s_bytes, b0)
    return pre + secB + post


def sha384(b):
    return hashlib.sha384(b).digest()


def claim_digest(s_bytes):
    """`claimDigest` = the 42-B truncated SHA-384 of S (U-10; Lean `bdigest`)."""
    return sha384(s_bytes)[:42]


# T1 (`d3c8/d3/02-h10196-s3`): the kernel-evaluated values (`RealChunkT1.t1_S_len`, `t1_claimDigest`)
T1_S_LEN = 1007
T1_CLAIM_DIGEST = "bb5aad11ba6ba32d91739f13a2dbd544f2420d770bcd2c3fde9ddc0e1c02710caee28e5e9e4e299f2f01"

LEAN_PKG = "/data/illia/nearproof/spec/lean/v3"
STMT_EVAL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "StmtEval.lean")


def lean_stmt(claim_paths, pkg=LEAN_PKG):
    """Evaluate lane E's `PublicStmt.encode` / `claimDigest` (`E2E/StmtEnc.lean`) on claim files with
    `lean/StmtEval.lean` (`lake env lean --run`, the v3 package's oleans; no build). Returns
    {path: row} (row: S_len, pre_len, post_len, wf, splice, decode_roundtrip, claimDigest, S hex; or
    `error`), or None when Lean could not be run."""
    try:
        p = subprocess.run(["lake", "env", "lean", "--run", STMT_EVAL] + list(claim_paths), cwd=pkg,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600)
    except (OSError, subprocess.TimeoutExpired):
        return None
    rows = {}
    for ln in p.stdout.decode(errors="replace").splitlines():
        if ln.startswith("{"):
            d = json.loads(ln)
            rows[d["file"]] = d
    return rows


def lean_stmt_compare(claim, row, pc=None):
    """Byte-for-byte comparison of this module's S / claimDigest with a `lean_stmt` row."""
    s = statement_bytes(claim, pc)
    b0 = (pc or parse_claim(claim))["secB"][0]
    pre, post = stmt_pre_post(s, b0)
    if row is None or "error" in row:
        return {"ok": False, "error": (row or {}).get("error", "Lean not run")}
    r = {"S_equal": row["S"] == s.hex(), "claimDigest_equal": row["claimDigest"] == claim_digest(s).hex(),
         "pre_len_equal": row["pre_len"] == len(pre), "post_len_equal": row["post_len"] == len(post),
         "lean_wf": row["wf"], "lean_splice": row["splice"], "lean_decode_roundtrip": row["decode_roundtrip"],
         "S_len": row["S_len"], "claimDigest": row["claimDigest"]}
    r["ok"] = all(v for k, v in r.items() if k not in ("S_len", "claimDigest"))
    return r


# ---------------------------------------------------------------------------
# FinalOut: the header outputs vs the Lean run's outputs (Lean `headerOk`)
# ---------------------------------------------------------------------------
def final_out_table(pc, lean_outputs):
    """Rows (header field, header value, Lean output key, Lean value, equal)."""
    h, o = pc["inner"], lean_outputs
    cong = o["congestion"]
    rows = [
        ("prev_state_root", h["prev_state_root"], "stateRoot", o["stateRoot"]),
        ("prev_outcome_root", h["prev_outcome_root"], "outcomeRoot", o["outcomeRoot"]),
        ("prev_gas_used", h["prev_gas_used"], "gasUsed", int(o["gasUsed"])),
        ("prev_balance_burnt", h["prev_balance_burnt"], "balanceBurnt", int(o["balanceBurnt"])),
        ("prev_outgoing_receipts_root", h["prev_outgoing_receipts_root"], "outgoingReceiptsRoot",
         o["outgoingReceiptsRoot"]),
        ("prev_validator_proposals", len(h["prev_validator_proposals"]), "proposals", len(o["proposals"])),
        ("congestion.delayed_receipts_gas", h["congestion"]["delayed_receipts_gas"], "congestion.delayedReceiptsGas",
         int(cong["delayedReceiptsGas"])),
        ("congestion.buffered_receipts_gas", h["congestion"]["buffered_receipts_gas"],
         "congestion.bufferedReceiptsGas", int(cong["bufferedReceiptsGas"])),
        ("congestion.receipt_bytes", h["congestion"]["receipt_bytes"], "congestion.receiptBytes",
         int(cong["receiptBytes"])),
        ("congestion.allowed_shard", h["congestion"]["allowed_shard"], "congestion.allowedShard",
         int(cong["allowedShard"])),
        ("bandwidth_requests", len(h["bandwidth_requests"]), "bwRequests", len(o["bwRequests"])),
        ("encoded_merkle_root", h["encoded_merkle_root"], "encodedMerkleRoot", o["encodedMerkleRoot"]),
        ("encoded_length", h["encoded_length"], "encodedLength", int(o["encodedLength"])),
        ("tx_root", h["tx_root"], "txRoot", o["txRoot"]),
    ]
    return [dict(header=a, header_value=b, lean=c, lean_value=d, equal=(b == d)) for a, b, c, d in rows]


# ---------------------------------------------------------------------------
# mutants of S
# ---------------------------------------------------------------------------
def _put_int(buf, off, size, v):
    buf[off:off + size] = (v % (1 << (8 * size))).to_bytes(size, "little")


def _get_int(buf, off, size):
    return int.from_bytes(buf[off:off + size], "little")


def mutants(claim):
    """Yield (name, section, mutated claim bytes). One public field changed per mutant; section B
    untouched. Same-length edits (the claim still decodes) plus a few structural ones."""
    pc = parse_claim(claim)
    io, il = pc["inner_off"], pc["inner_len"]
    inner = claim[io:io + il]
    fields = {f.name: f for f in pc["fields"]}

    def edit(f, fn):
        b = bytearray(claim)
        fn(b, f)
        return bytes(b)

    def flip(bit_byte):
        def fn(b, f):
            b[f.off + {"first": 0, "mid": f.size // 2, "last": f.size - 1}[bit_byte]] ^= 0x01
        return fn

    def add(d):
        def fn(b, f):
            _put_int(b, f.off, f.size, _get_int(b, f.off, f.size) + d)
        return fn

    def with_inner(new_inner):
        return claim[:io - 4] + struct.pack("<I", len(new_inner)) + new_inner + claim[io + il:]

    out = []
    for f in pc["fields"]:
        n = f.name
        if n.endswith(".count") or n.startswith("C.apply_facts") and n.endswith(".tag") \
                or n == "C.genesis_chunk_extra.tag" or n == "inner.version":
            continue
        if f.kind == "hash":
            for where in ("first", "mid", "last"):
                out.append((f"{n}:flip-{where}", f.sec, edit(f, flip(where))))
        elif f.kind in ("u16", "u32", "u64", "u128"):
            out.append((f"{n}:+1", f.sec, edit(f, add(1))))
            v = _get_int(claim, f.off, f.size)
            out.append((f"{n}:-1" if v > 0 else f"{n}:max", f.sec,
                        edit(f, add(-1))))
        elif f.kind == "u8":  # flags
            out.append((f"{n}:toggle", f.sec, edit(f, lambda b, f: b.__setitem__(f.off, b[f.off] ^ 1))))
        elif f.kind == "bytes" and f.size > 0:
            # an account / chain id / layout byte: change the last byte to another printable one
            def fn(b, f):
                c = b[f.off + f.size - 1]
                b[f.off + f.size - 1] = c + 1 if c not in (0x7a, 0x39, 0x7e, 0xff) else c - 1
            out.append((f"{n}:last-byte", f.sec, edit(f, fn)))
        elif f.kind == "raw":
            out.append((f"{n}:flip-last", f.sec, edit(f, flip("last"))))
    # structural: chunk_inner
    pe = pc["inner"]["proposals_end"]
    fake = b"\x00" + struct.pack("<I", 7) + b"mutant1" + b"\x00" + b"\x11" * 32 + (10 ** 24).to_bytes(16, "little")
    poff = fields["inner.prev_validator_proposals.count"].off - io
    nprop = _get_int(inner, poff, 4)
    ni = bytearray(inner)
    _put_int(ni, poff, 4, nprop + 1)
    ni[pe:pe] = fake
    out.append(("inner.prev_validator_proposals:append", "A.inner", with_inner(bytes(ni))))
    bwoff = fields["inner.bandwidth_requests.count"].off - io
    be = pc["inner"]["bw_end"]
    ni = bytearray(inner)
    _put_int(ni, bwoff, 4, _get_int(inner, bwoff, 4) + 1)
    ni[be:be] = struct.pack("<H", (pc["inner"]["shard_id"] + 1) % 6) + b"\x01\x00\x00\x00\x00"
    out.append(("inner.bandwidth_requests:append", "A.inner", with_inner(bytes(ni))))
    if pc["inner"]["version"] == 4 and pc["inner"]["proposed_split"] is None:
        so = pc["inner"]["proposed_split_off"]
        ni = bytearray(inner)
        ni[so:so + 1] = b"\x01" + struct.pack("<I", 8) + b"mutant.x" + struct.pack("<QQ", 1, 1)
        out.append(("inner.proposed_split:some", "A.inner", with_inner(bytes(ni))))
    # structural: section C
    tv = fields["C.tx_valid.count"]
    b = bytearray(claim)
    _put_int(b, tv.off, 4, _get_int(claim, tv.off, 4) + 1)
    b[tv.off + 4:tv.off + 4] = b"\x01"
    out.append(("C.tx_valid:append", "C", bytes(b)))
    go = pc["gce_off"]
    if pc["genesis_chunk_extra"] is None:
        b = bytearray(claim)
        b[go:go + 1] = b"\x01" + struct.pack("<I", 1) + b"\x00"
        out.append(("C.genesis_chunk_extra:some", "C", bytes(b)))
    if pc["epochs"] and pc["epochs"][0]["validators"]:
        vc = fields["C.epochs[0].validators.count"]
        b = bytearray(claim)
        # drop the last validator of epoch 0
        last_acc = fields[f"C.epochs[0].validators[{len(pc['epochs'][0]['validators']) - 1}].account"]
        start = last_acc.off - 4
        end = last_acc.off + last_acc.size + 16
        _put_int(b, vc.off, 4, _get_int(claim, vc.off, 4) - 1)
        del b[start:end]
        out.append(("C.epochs[0].validators:drop-last", "C", bytes(b)))
    af = pc["apply_facts"]
    if af and not af[0]["validator_update"]:
        b = bytearray(claim)
        o = af[0]["vu_off"]
        b[o:o + 1] = b"\x01" + struct.pack("<I", 0) + struct.pack("<I", 0) + b"\x00"
        out.append(("C.apply_facts[0].validator_update:some-empty", "C", bytes(b)))
    return pc, out


def patch_witness_inner(witness, claim, mclaim):
    """The witness with its own copy of `chunk_inner` (ChunkStateWitness.chunk_header.inner, which
    the relation compares with the claim's: `w.innerBytes == c.chunkInner`) replaced by the
    mutant's, and the outer payload length fixed. The original inner occurs once in the witness."""
    pc, pm = parse_claim(claim), parse_claim(mclaim)
    old = claim[pc["inner_off"]:pc["inner_off"] + pc["inner_len"]]
    new = mclaim[pm["inner_off"]:pm["inner_off"] + pm["inner_len"]]
    assert witness.count(old) == 1, "witness inner not unique"
    i = witness.index(old)
    w = bytearray(witness[:i] + new + witness[i + len(old):])
    # outer framing: u32 length + format id, then the u32 payload length
    flen = struct.unpack("<I", witness[:4])[0]
    lo = 4 + flen
    plen = struct.unpack("<I", witness[lo:lo + 4])[0]
    # the ChunkStateWitness payload (code blobs may follow it) must contain the inner
    assert lo + 4 <= i and i + len(old) <= lo + 4 + plen <= len(witness), "witness framing"
    w[lo:lo + 4] = struct.pack("<I", plen + len(new) - len(old))
    return bytes(w)
