#!/usr/bin/env python3
"""Check the complete-code witness policy against raw cold nearcore, without relabeling it.

Each pair contains an independently nearcore-accepted complete witness and a code-only mutant.
Normalization restores the source registry's hash-verified code vector and must reproduce the
original accepted witness byte-for-byte. Complete and restored witnesses must accept. Since
2026-10-29 the incomplete mutant must reproduce its own raw cold nearcore verdict (`expected_rel`),
or be the named preparation-race exclusion; before, the policy rejected every incomplete witness
with `w.code_complete`, including the ones nearcore deterministically accepts.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import struct
import sys

from replay_successor import REPO, run_batch, sha256

TAG = b"near-arena-witness-v3"
POLICY_PREFIX = "invalid witness (w.code_complete):"
RACE_PREFIX = "out of domain (e.code_prep_race):"


def decode_envelope(data):
    offset = 0

    def u32():
        nonlocal offset
        if len(data) - offset < 4:
            raise ValueError("truncated witness envelope length")
        value = struct.unpack_from("<I", data, offset)[0]
        offset += 4
        return value

    def vector():
        nonlocal offset
        count = u32()
        if count > len(data) - offset:
            raise ValueError("truncated witness envelope bytes")
        value = data[offset:offset + count]
        offset += count
        return value

    if vector() != TAG:
        raise ValueError("wrong witness envelope tag")
    state = vector()
    count = u32()
    if count > (len(data) - offset) // 4:
        raise ValueError("impossible witness code vector length")
    codes = [vector() for _ in range(count)]
    if offset != len(data):
        raise ValueError("trailing witness envelope bytes")
    return state, codes


def encode_envelope(state, codes):
    def vector(value):
        return struct.pack("<I", len(value)) + value
    return vector(TAG) + vector(state) + struct.pack("<I", len(codes)) + b"".join(map(vector, codes))


def base58(raw):
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    number = int.from_bytes(raw, "big")
    result = ""
    while number:
        number, digit = divmod(number, 58)
        result = alphabet[digit] + result
    return "1" * (len(raw) - len(raw.lstrip(b"\0"))) + result


def registry(codes, meta):
    declared = meta.get("codes")
    if not isinstance(declared, list) or len(declared) != len(codes) or not codes:
        raise ValueError("source must declare a nonempty complete code registry")
    rows = []
    for code, entry in zip(codes, declared):
        digest = hashlib.sha256(code).digest()
        if entry.get("hash") != base58(digest) or entry.get("len") != len(code):
            raise ValueError("source registry code hash/length mismatch")
        rows.append({"sha256": digest.hex(), "near_hash": base58(digest), "bytes": len(code)})
    return rows


def prepare_pair(pair, base, out):
    name = pair["name"]
    if not isinstance(name, str) or not name or Path(name).name != name or name in (".", ".."):
        raise ValueError("unsafe pair name")
    complete = (base / pair["complete"]).resolve()
    incomplete = (base / pair["incomplete"]).resolve()
    inputs = {str(p): sha256(p) for directory in (complete, incomplete)
              for p in (directory / "claim.bin", directory / "witness.bin", directory / "meta.json")}
    meta = json.loads((complete / "meta.json").read_text())
    mutant = json.loads((incomplete / "meta.json").read_text())
    if meta.get("expected_rel") is not True or type(mutant.get("expected_rel")) is not bool:
        raise ValueError("pair needs accepted source and unchanged boolean raw mutant verdict")
    if (complete / "claim.bin").read_bytes() != (incomplete / "claim.bin").read_bytes():
        raise ValueError("pair changes the claim, not only code supply")
    original = (complete / "witness.bin").read_bytes()
    changed = (incomplete / "witness.bin").read_bytes()
    state, codes = decode_envelope(original)
    mutant_state, _ = decode_envelope(changed)
    if state != mutant_state or original == changed:
        raise ValueError("pair must be a nontrivial code-only witness mutation")
    code_registry = registry(codes, meta)
    restored = encode_envelope(mutant_state, codes)
    if restored != original:
        raise ValueError("normalized witness differs from independently judged complete source")
    dirs = {}
    for kind, source in (("complete", complete), ("incomplete", incomplete), ("normalized", complete)):
        dest = out / "cases" / name / kind
        dest.mkdir(parents=True, exist_ok=True)
        for file in ("claim.bin", "witness.bin", "meta.json"):
            shutil.copyfile(source / file, dest / file)
        if kind == "normalized":
            (dest / "witness.bin").write_bytes(restored)
        dirs[kind] = str(dest.resolve())
    return {"name": name, "cases": dirs, "inputs": inputs, "registry": code_registry,
            "raw_nearcore": {"complete_expected_rel": meta["expected_rel"],
                "incomplete_expected_rel": mutant["expected_rel"],
                "incomplete_reason": mutant.get("nearcore"),
                "incomplete_verdict_source": mutant.get("verdict_source")},
            "normalized_provenance": "byte-identical to independently nearcore-accepted complete witness",
            "policy_expectations": {"complete": "claim_accept", "incomplete": "raw_cold_nearcore_verdict",
                                    "normalized": "claim_accept"}}


def validate_rows(rows, pairs):
    for pair in pairs:
        for kind, case in pair["cases"].items():
            row = rows[case]
            if kind == "incomplete":
                # Since 2026-10-29 the complete policy resolves a missing blob exactly as the cold
                # validator does (an earlier in-chunk deploy serves it, or MissingTrieValue), so the
                # incomplete witness must reproduce the raw cold verdict. The only other admitted
                # result is the race exclusion (nearcore's own verdict is then timing-dependent).
                raw_accept = pair["raw_nearcore"]["incomplete_expected_rel"]
                verdict = row["verdict"]
                race = verdict == "out_of_domain" and row["reason"].startswith(RACE_PREFIX)
                if verdict == "accept" and not raw_accept:
                    raise ValueError(f"{pair['name']}: accepted an incomplete witness nearcore rejects: {row}")
                if verdict != ("accept" if raw_accept else "reject") and not race:
                    raise ValueError(f"{pair['name']}: incomplete witness: nearcore "
                                     f"{'accepts' if raw_accept else 'rejects'}, got {row}")
            elif row["verdict"] != "accept":
                raise ValueError(f"{pair['name']}: complete source/normalized bytes did not accept: {row}")


def check(binary, pairs_file, out, tier="completeCodeGlobal", repeats=2, timeout=600):
    out.mkdir(parents=True, exist_ok=True)
    report_file = out / "report.json"
    report = {"schema": "complete-code-witness-policy-v1", "status": "running",
              "comparison": "complete-witness claim validity and separately classified witness-policy failure",
              "raw_nearcore_mutant_expectations_relabelled": False}
    def save():
        report_file.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    save()
    try:
        if repeats < 2 or timeout <= 0:
            raise ValueError("need at least two repeated runs and positive timeout")
        binary, pairs_file = binary.resolve(), pairs_file.resolve()
        binary_hash, manifest_hash = sha256(binary), sha256(pairs_file)
        manifest = json.loads(pairs_file.read_text())
        pairs = manifest.get("pairs")
        if not isinstance(pairs, list) or not pairs or len({p["name"] for p in pairs}) != len(pairs):
            raise ValueError("empty/duplicate pair population")
        prepared = [prepare_pair(p, pairs_file.parent, out) for p in pairs]
        cases = [Path(case) for p in prepared for case in p["cases"].values()]
        artifact_hashes = {str(p): sha256(p) for case in cases
                           for p in (case / "claim.bin", case / "witness.bin", case / "meta.json")}
        report.update(binary={"path": str(binary), "sha256": binary_hash, "tier": tier},
                      manifest={"path": str(pairs_file), "sha256": manifest_hash}, pairs=prepared,
                      repeats=repeats, artifacts=artifact_hashes,
                      harness_sha256=sha256(Path(__file__)))
        save()
        first = None
        for attempt in range(repeats):
            rows = run_batch([str(binary), "--tier", tier], cases, timeout, tier)
            validate_rows(rows, prepared)
            if first is not None and rows != first:
                raise ValueError("non-repeatable witness-policy outcomes")
            first = rows
            (out / f"results-{attempt}.jsonl").write_text(
                "".join(json.dumps(rows[str(case)], sort_keys=True) + "\n" for case in cases))
        if sha256(binary) != binary_hash or sha256(pairs_file) != manifest_hash:
            raise ValueError("checker or manifest changed during run")
        for path, expected in artifact_hashes.items():
            if sha256(Path(path)) != expected:
                raise ValueError("test artifact changed during run")
        for pair in prepared:
            for path, expected in pair["inputs"].items():
                if sha256(Path(path)) != expected:
                    raise ValueError("source fixture changed during run")
        report.update(status="pass", pair_count=len(prepared), cases_per_run=len(cases),
                      raw_mutant_accepts=sum(p["raw_nearcore"]["incomplete_expected_rel"] for p in prepared),
                      raw_mutant_rejects=sum(not p["raw_nearcore"]["incomplete_expected_rel"] for p in prepared))
        save()
        return report
    except Exception as exc:
        report.update(status="fail", error=f"{type(exc).__name__}: {exc}")
        save()
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor")
    parser.add_argument("--pairs", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--tier", default="completeCodeGlobal")
    parser.add_argument("--repeats", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    try:
        result = check(args.binary, args.pairs, args.out, args.tier, args.repeats, args.timeout)
        print(json.dumps({k: result[k] for k in ("status", "pair_count", "cases_per_run", "repeats",
                                                "raw_mutant_accepts", "raw_mutant_rejects")}))
        return 0
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    sys.exit(main())
