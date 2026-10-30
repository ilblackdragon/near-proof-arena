#!/usr/bin/env python3
"""Versioned claim/witness schema check (spec/claim-v3-versioning.md).

Every `claim.bin` / `witness.bin` has a schema version:

* the **versioned envelope** carries it explicitly:
    claim.bin   = bytes "near-arena-claim"   ‖ u32 schema_version ‖ body
    witness.bin = bytes "near-arena-witness" ‖ u32 schema_version ‖ u8 encoding ‖ body
* an **unversioned (legacy) file** is schema version 3 by rule: `near-arena-claim-v3`,
  `near-arena-witness-v3` (encoding 0) and `near-arena-cwitness-v3` (encoding 1).

Schema version 3 is the only one defined. This module decodes the header, then checks the body
structurally against spec/claim-v3.md §2/§3 (field order, lengths, option/flag tags, counts,
strictly ascending epochs, no trailing bytes). It does not judge the relation; that is the Lean
checker's job (`Successor/SchemaVersion.lean` is the Lean side of the same envelope).

CLI:
  claim_schema.py --verify PATH...          case dirs (claim.bin + witness.bin) or single files
  claim_schema.py --to-versioned SRC DST    write the version-3 envelope of a case dir
  claim_schema.py --self-test               built-in positive/negative checks (no corpora needed)
  claim_schema.py --check-env MANIFEST      the package environment manifest (spec/environment-v3.json)
Exit 0 iff every input passes.
"""
import argparse
import json
import os
import shutil
import struct
import sys

CLAIM_FAMILY = b"near-arena-claim"
WITNESS_FAMILY = b"near-arena-witness"
LEGACY_CLAIM = b"near-arena-claim-v3"
LEGACY_WITNESS = {b"near-arena-witness-v3": 0, b"near-arena-cwitness-v3": 1}
STATEMENT = b"near/pv86/chunk-validation/v0"
SUPPORTED = {3}
ENCODINGS = {0: "clear", 1: "zstd"}
MAX_DECODED = 64 * 1024 * 1024          # MAX_UNCOMPRESSED_STATE_WITNESS_SIZE
MAX_ENCODED = 48 * 1024 * 1024          # MAX_COMPRESSED_STATE_WITNESS_SIZE


class SchemaError(Exception):
    pass


class R:
    def __init__(self, b):
        self.b, self.i = b, 0

    def take(self, n, what):
        if self.i + n > len(self.b):
            raise SchemaError(f"truncated {what}")
        v = self.b[self.i:self.i + n]
        self.i += n
        return v

    def u(self, n, what):
        return int.from_bytes(self.take(n, what), "little")

    def bytes_(self, what):
        return self.take(self.u(4, what + " length"), what)

    def vec(self, what, f):
        return [f() for _ in range(self.u(4, what + " count"))]

    def option(self, what, f):
        t = self.u(1, what + " option tag")
        if t == 0:
            return None
        if t == 1:
            return f()
        raise SchemaError(f"bad option tag {t} in {what}")

    def done(self, what):
        if self.i != len(self.b):
            raise SchemaError(f"{len(self.b) - self.i} trailing bytes in {what}")


def header(data):
    """(kind, schema_version, encoding, legacy, body offset) of a claim or witness file."""
    r = R(data)
    tag = r.bytes_("format tag")
    if tag == CLAIM_FAMILY:
        v = r.u(4, "schema version")
        if v not in SUPPORTED:
            raise SchemaError(f"unsupported claim schema version {v}")
        return "claim", v, None, False, r.i
    if tag == WITNESS_FAMILY:
        v = r.u(4, "schema version")
        if v not in SUPPORTED:
            raise SchemaError(f"unsupported witness schema version {v}")
        e = r.u(1, "witness encoding")
        if e not in ENCODINGS:
            raise SchemaError(f"unsupported witness encoding {e}")
        return "witness", v, e, False, r.i
    if tag == LEGACY_CLAIM:
        return "claim", 3, None, True, r.i
    if tag in LEGACY_WITNESS:
        return "witness", 3, LEGACY_WITNESS[tag], True, r.i
    raise SchemaError(f"unknown format tag {tag[:40]!r}")


def check_claim_body_v3(r):
    if r.bytes_("statement_id") != STATEMENT:
        raise SchemaError("statement_id is not near/pv86/chunk-validation/v0")
    r.u(4, "protocol_version")
    chain = r.bytes_("chain_id")
    if not (1 <= len(chain) <= 64 and all(0x21 <= c <= 0x7E for c in chain)):
        raise SchemaError("chain_id out of range")
    r.take(32, "epoch_id")
    r.bytes_("chunk_inner")
    n_blocks = r.u(4, "n_blocks")
    if n_blocks < 1:
        raise SchemaError("n_blocks = 0")
    for _ in range(n_blocks):
        r.u(1, "header_version")
        r.take(32, "prev_hash")
        r.bytes_("inner_lite")
        r.bytes_("inner_rest")
        r.vec("slots", lambda: (r.bytes_("slot inner"), r.u(8, "height_included")))
    r.u(2, "rs_data_parts")
    r.u(2, "rs_total_parts")
    stakes = lambda w: r.vec(w, lambda: (r.bytes_(w + " account"), r.u(16, w + " stake")))

    def epoch():
        eid = r.take(32, "epoch_id")
        r.u(4, "epoch protocol_version")
        r.u(8, "epoch_height")
        r.bytes_("shard_layout")
        stakes("validators")
        return eid
    eids = r.vec("epochs", epoch)
    if any(a >= b for a, b in zip(eids, eids[1:])):
        raise SchemaError("epochs not strictly ascending by epoch_id")
    flags = r.vec("epoch_start_after", lambda: r.u(1, "flag"))
    if len(flags) != n_blocks or any(f > 1 for f in flags):
        raise SchemaError("epoch_start_after must be n_blocks 0/1 flags")

    def apply_facts():
        r.option("validator_update", lambda: (stakes("stake_info"), stakes("validator_rewards"),
                                              r.option("treasury", lambda: r.bytes_("treasury"))))
        r.u(16, "minimum_stake")
        r.option("split_gate", lambda: (r.u(8, "memory_usage_threshold"), r.u(8, "min_child"),
                                        r.u(8, "max_shards"), r.vec("force", lambda: r.u(8, "s")),
                                        r.vec("block", lambda: r.u(8, "s"))))
    r.vec("apply_facts", apply_facts)
    if any(f > 1 for f in r.vec("tx_valid", lambda: r.u(1, "tx_valid flag"))):
        raise SchemaError("tx_valid flag is not 0/1")
    r.option("genesis_chunk_extra", lambda: r.bytes_("genesis_chunk_extra"))
    r.done("claim.bin")


def check_witness_body_v3(r, encoding):
    sw = r.bytes_("state_witness")
    cap = MAX_ENCODED if encoding == 1 else MAX_DECODED
    if len(sw) > cap:
        raise SchemaError(f"state witness {len(sw)} B exceeds {cap} B")
    r.vec("contract_code", lambda: r.bytes_("code"))
    r.done("witness.bin")


def check_file(data, want=None):
    kind, v, enc, legacy, off = header(data)
    if want and kind != want:
        raise SchemaError(f"expected a {want} file, found a {kind} file")
    r = R(data)
    r.i = off
    if kind == "claim":
        check_claim_body_v3(r)
    else:
        check_witness_body_v3(r, enc)
    return {"kind": kind, "schema_version": v, "encoding": ENCODINGS.get(enc) if enc is not None else None,
            "rule": "legacy (unversioned => 3)" if legacy else "explicit"}


def to_versioned(data):
    kind, v, enc, legacy, off = header(data)
    if not legacy:
        return data
    fam = CLAIM_FAMILY if kind == "claim" else WITNESS_FAMILY
    out = struct.pack("<I", len(fam)) + fam + struct.pack("<I", v)
    if kind == "witness":
        out += bytes([enc])
    return out + data[off:]


def to_legacy(data):
    kind, v, enc, legacy, off = header(data)
    if legacy:
        return data
    tag = LEGACY_CLAIM if kind == "claim" else [t for t, e in LEGACY_WITNESS.items() if e == enc][0]
    return struct.pack("<I", len(tag)) + tag + data[off:]


def verify_paths(paths):
    ok, bad, counts = 0, [], {}
    for p in paths:
        files = [(os.path.join(p, f), f.split(".")[0]) for f in ("claim.bin", "witness.bin")] \
            if os.path.isdir(p) else [(p, None)]
        for f, want in files:
            try:
                info = check_file(open(f, "rb").read(), want)
                key = f"{info['kind']} v{info['schema_version']} {info['encoding'] or ''} {info['rule']}".replace("  ", " ")
                counts[key] = counts.get(key, 0) + 1
                ok += 1
            except (SchemaError, OSError) as e:
                bad.append((f, str(e)))
    return ok, bad, counts


def self_test():
    """Positive and negative checks on a synthetic minimal claim/witness (no corpora needed)."""
    def b(x):
        return struct.pack("<I", len(x)) + x
    body = (b(STATEMENT) + struct.pack("<I", 86) + b(b"test") + b"\0" * 32 + b(b"inner") +
            struct.pack("<I", 1) + b"\x05" + b"\0" * 32 + b(b"l") + b(b"r") + struct.pack("<I", 0) +
            struct.pack("<HH", 1, 4) + struct.pack("<I", 1) + b"\1" * 32 + struct.pack("<IQ", 86, 0) +
            b(b"layout") + struct.pack("<I", 0) + struct.pack("<I", 1) + b"\0" +
            struct.pack("<I", 1) + b"\0" + b"\0" * 16 + b"\0" + struct.pack("<I", 0) + b"\0")
    claim = b(LEGACY_CLAIM) + body
    wit = b(b"near-arena-witness-v3") + b(b"sw") + struct.pack("<I", 0)
    cases = [("legacy claim", claim, True), ("legacy witness", wit, True),
             ("versioned claim", to_versioned(claim), True), ("versioned witness", to_versioned(wit), True),
             ("round trip claim", to_legacy(to_versioned(claim)) == claim, None),
             ("round trip witness", to_legacy(to_versioned(wit)) == wit, None),
             ("claim v4", b(CLAIM_FAMILY) + struct.pack("<I", 4) + body, False),
             ("witness encoding 2", b(WITNESS_FAMILY) + struct.pack("<I", 3) + b"\2" + wit[25:], False),
             ("trailing byte", claim + b"\0", False), ("truncated", claim[:-1], False),
             ("bad tx_valid flag", claim[:-6] + struct.pack("<I", 1) + b"\2" + b"\0", False),
             ("unknown tag", b(b"near-arena-claim-v9") + body, False)]
    fails = 0
    for name, data, want in cases:
        if want is None:
            got = data
        else:
            try:
                check_file(data)
                got = True
            except SchemaError:
                got = False
        good = got is True if want is None else got == want
        fails += not good
        print(f"{'ok ' if good else 'BAD'} {name}")
    return fails


def check_env(path):
    """The package's environment manifest (spec/environment-v3.json) must state the reference
    validator, the host-state assumptions and a status for every architecture."""
    with open(path) as f:
        doc = json.load(f)
    errs = []
    if doc.get("schema") != "near-arena-environment-v1":
        errs.append("schema is not near-arena-environment-v1")
    ref = doc.get("reference_validator", {})
    for k in ("nearcore_commit", "protocol_version", "target_arch", "wasm_engine", "wasm_compiler"):
        if not ref.get(k):
            errs.append(f"reference_validator.{k} missing")
    if ref.get("nearcore_commit") != "44f7ae6cd7ef08bab604e20a473bf77e35d4c993":
        errs.append("reference_validator.nearcore_commit is not the pin")
    if not doc.get("assumptions") or any(not (a.get("id") and a.get("statement") and a.get("source"))
                                         for a in doc["assumptions"]):
        errs.append("assumptions must be non-empty, each with id/statement/source")
    archs = doc.get("architectures", {})
    if archs.get(ref.get("target_arch"), {}).get("status") != "reference":
        errs.append("the reference target_arch must have status 'reference'")
    for name, a in archs.items():
        if a.get("status") not in ("reference", "excluded"):
            errs.append(f"architecture {name}: status must be reference|excluded")
    return errs


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verify", nargs="+")
    ap.add_argument("--verify-list", help="file with one case dir per line")
    ap.add_argument("--to-versioned", nargs=2, metavar=("SRC", "DST"))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--check-env", metavar="MANIFEST")
    a = ap.parse_args()
    if a.check_env:
        errs = check_env(a.check_env)
        print("\n".join(errs) if errs else "environment manifest ok")
        return 1 if errs else 0
    if a.self_test:
        return 1 if self_test() else 0
    if a.to_versioned:
        src, dst = a.to_versioned
        os.makedirs(dst, exist_ok=True)
        for f in ("claim.bin", "witness.bin"):
            open(os.path.join(dst, f), "wb").write(to_versioned(open(os.path.join(src, f), "rb").read()))
        if os.path.exists(os.path.join(src, "meta.json")):
            shutil.copy(os.path.join(src, "meta.json"), os.path.join(dst, "meta.json"))
        return 0
    paths = list(a.verify or [])
    if a.verify_list:
        paths += [l.strip() for l in open(a.verify_list) if l.strip()]
    if not paths:
        ap.error("nothing to do")
    ok, bad, counts = verify_paths(paths)
    print(json.dumps({"files_ok": ok, "files_bad": len(bad), "by_schema": counts, "bad": bad[:20]}, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
