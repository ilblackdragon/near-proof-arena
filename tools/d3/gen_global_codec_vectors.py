#!/usr/bin/env python3
"""Generate independent nearcore Borsh map-normalization vectors for successor codecs.

Signatures are structural placeholders. This probes decoding/canonical encoding/hash derivation,
not signature validity or transaction admission. The expected canonical bytes are also constructed
independently in Python, then compared with pinned nearcore's actual Borsh implementation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def u(n, size):
    return n.to_bytes(size, "little")


def string(value):
    return u(len(value), 4) + value


def state(entries):
    return b"\0\0" + bytes(32) + u(len(entries), 4) + b"".join(
        string(key) + string(value) for key, value in entries)


def wrap(kind, init):
    if kind == "state-init":
        return init
    action = b"\x0b" + init + u(7, 16)
    if kind == "action":
        return action
    pk = b"\0" + bytes(32)
    sig = b"\0" + bytes(64)
    if kind == "signed-transaction":
        return (string(b"alice") + pk + u(1, 8) + string(b"bob") + bytes(32)
                + u(1, 4) + action + sig)
    if kind == "signed-delegate":
        return (string(b"alice") + string(b"bob") + u(1, 4) + action
                + u(1, 8) + u(1000, 8) + pk + sig)
    raise ValueError(kind)


def probe(binary, kind, data):
    result = subprocess.run([str(binary), "codec-roundtrip", kind, data.hex()],
                            capture_output=True, text=True, timeout=30)
    row = json.loads(result.stdout)
    if result.returncode not in (0, 1):
        raise ValueError(result.stderr)
    assert (row["status"] == "ok") == (result.returncode == 0)
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for family, entries in [
        ("reversed", [(b"z", b"last"), (b"a", b"first")]),
        ("duplicate-last-wins", [(b"a", b"first"), (b"z", b"last"), (b"a", b"replacement")]),
    ]:
        canonical = state(sorted(dict(entries).items()))
        for kind in ("state-init", "action", "signed-transaction", "signed-delegate"):
            data = wrap(kind, state(entries))
            row = probe(args.binary, kind, data)
            assert row["status"] == "ok", row
            assert row["canonical_hex"] == wrap(kind, canonical).hex(), row
            stable = probe(args.binary, kind, bytes.fromhex(row["canonical_hex"]))
            assert stable["canonical_hex"] == row["canonical_hex"]
            assert stable["extra"] == row["extra"]
            if kind == "signed-transaction":
                assert row["extra"]["transaction_hash_hex"] == hashlib.sha256(
                    bytes.fromhex(row["canonical_hex"])[:-65]).hexdigest()
            rows.append({"family": family, **row})
    for family, kind, data in [
        ("unknown-state-version", "state-init", b"\x7f" + state([])[1:]),
        ("truncated-map-value", "action", wrap("action", state([(b"x", b"y")]))[:-17]),
        ("trailing-bytes", "signed-transaction", wrap("signed-transaction", state([])) + b"\0"),
        ("unknown-action-tag", "action", b"\xff"),
    ]:
        row = probe(args.binary, kind, data)
        assert row["status"] == "error", row
        rows.append({"family": family, "kind": kind, "input_hex": data.hex(), **row})
    report = {"schema": "near-global-codec-vectors-v1", "status": "pass",
              "nearcore_pin": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
              "binary_sha256": hashlib.sha256(args.binary.read_bytes()).hexdigest(),
              "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": rows, "scope": "Borsh canonicalization and derived hashes, not cryptographic validity"}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"PASS: {len(rows)} independent nearcore codec vectors")


if __name__ == "__main__":
    main()
