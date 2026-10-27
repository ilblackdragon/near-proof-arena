"""Build `hdr.bandwidth_requests.own_only(derived)` mutants.

For each honest V2-parent-map case whose header carries nearcore's (parent-chained) bandwidth
requests, replace the header's requests by the value the pre-fix Lean rule computes (own buffer
only, read from the pre-fix checker's --blind output). nearcore's verdict is derived, not run:
`validate_bandwidth_requests` (chain/chain/src/validate.rs:280-299) rejects any header requests
that differ from the chunk extra nearcore computes, and the honest header *is* that extra (the cold
validator accepted it). A mutant whose replacement equals the honest value is skipped.

usage: bw_own_only_mutants.py OLD_CHECKER FIXED_CHECKER CASES_FILE OUT_DIR
(OLD_CHECKER: a checker built before the V2 parent-map rule; FIXED_CHECKER: after it)
"""
import json, os, shutil, struct, subprocess, sys

old, new_checker, cases_file, out = sys.argv[1:5]
os.makedirs(out, exist_ok=True)
made = []
for case in open(cases_file).read().split():
    row = json.loads(subprocess.run([old, "--tier", "allFeatures", "--blind", case], capture_output=True,
                                    text=True, check=True).stdout.splitlines()[0])
    assert row["verdict"] == "accept", row
    reqs = row["outputs"]["bwRequests"]
    claim = open(f"{case}/claim.bin", "rb").read()
    # claim layout: ... u32 len(chunk_inner) at a fixed offset, then chunk_inner; the inner ends with
    # BandwidthRequests::V1 = tag 0, u32 count, count x (u16 to_shard, [u8; 5] bitmap).
    off = 110
    n = struct.unpack_from("<I", claim, off)[0]
    inner = claim[off + 4:off + 4 + n]
    # the honest header's requests are what the fixed checker computes (it accepts the case), so
    # their count fixes where the block starts; the bytes are checked against that value below
    fixed = json.loads(subprocess.run([new_checker, "--tier", "allFeatures", "--blind", case],
                                      capture_output=True, text=True, check=True).stdout.splitlines()[0])
    assert fixed["verdict"] == "accept", fixed
    honest = [(int(r["toShard"]), list(bytes.fromhex(r["bitmap"]))) for r in fixed["outputs"]["bwRequests"]]
    cnt = len(honest)
    enc_h = bytes([0]) + struct.pack("<I", cnt) + b"".join(struct.pack("<H", t) + bytes(bm) for t, bm in honest)
    # BandwidthRequests is followed only by the (absent) proposed split: `0` option tag
    assert inner.endswith(enc_h + bytes([0])), (case, inner[-60:].hex(), enc_h.hex())
    start = len(inner) - len(enc_h) - 1
    new = [(int(r["toShard"]), list(bytes.fromhex(r["bitmap"]))) for r in reqs]
    if new == honest:
        continue
    enc = bytes([0]) + struct.pack("<I", len(new)) + b"".join(
        struct.pack("<H", s) + bytes(bm) for s, bm in new)
    inner2 = inner[:start] + enc + bytes([0])
    claim2 = claim[:off] + struct.pack("<I", len(inner2)) + inner2 + claim[off + 4 + n:]
    name = os.path.basename(case) + "-hdr.bandwidth_requests.own_only(derived)"
    d = os.path.join(out, name)
    os.makedirs(d, exist_ok=True)
    open(f"{d}/claim.bin", "wb").write(claim2)
    # the witness embeds the same chunk header inner once, inside a u32-length-prefixed blob that
    # follows the `near-arena-witness-v3` tag (as the generator's own `hdr.*` mutants patch it)
    w = open(f"{case}/witness.bin", "rb").read()
    assert w.count(inner) == 1, case
    wi = w.find(inner)
    tag_len = struct.unpack_from("<I", w, 0)[0]
    lo = 4 + tag_len
    blob = struct.unpack_from("<I", w, lo)[0]
    assert lo + 4 <= wi and wi + len(inner) <= lo + 4 + blob, case
    w2 = w[:wi] + inner2 + w[wi + len(inner):]
    w2 = w2[:lo] + struct.pack("<I", blob + len(inner2) - len(inner)) + w2[lo + 4:]
    open(f"{d}/witness.bin", "wb").write(w2)
    meta = json.load(open(f"{case}/meta.json"))
    m = {"base": os.path.basename(case), "case": name, "kind": "mutant",
         "mutation": "hdr.bandwidth_requests.own_only(derived)",
         "d3_violations": meta.get("d3_violations", []), "in_d2": meta.get("in_d2"), "in_d3": meta.get("in_d3"),
         "expected_rel": False, "expected_rel_d2": False, "expected_rel_d3": False,
         "features": meta.get("features", {}),
         "nearcore": "derived: validate: InvalidBandwidthRequests (header requests differ from the "
                     "chunk extra the cold validator accepted; chain/chain/src/validate.rs:280-299)",
         "verdict_source": "derived(honest header = nearcore chunk extra)",
         "honest_requests": honest, "own_only_requests": new}
    json.dump(m, open(f"{d}/meta.json", "w"), indent=1)
    made.append(d)
print(len(made))
open(os.path.join(out, "cases.txt"), "w").write("\n".join(made) + "\n")
