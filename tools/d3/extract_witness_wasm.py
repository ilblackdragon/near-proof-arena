#!/usr/bin/env python3
"""Collect the distinct wasm modules embedded in chunk witnesses (W02 fuel certificate census).

    extract_witness_wasm.py OUT_DIR ROOT [ROOT ...]

Walks every `witness.bin` under each ROOT (and every `*.tar.gz` holding case directories), finds
each embedded module by its magic `\\0asm\\1\\0\\0\\0` with the borsh `u32` length in the four
bytes before it, and writes each distinct module once as `OUT_DIR/<sha256>.wasm`. Prints one JSON
summary line. This is measurement input only: a blob that is not really a module is rejected by
`prepare` and reported as unprepared by `nearspec-v3-fuel-cert`.
"""
import hashlib
import json
import os
import sys
import tarfile

MAGIC = b"\x00asm\x01\x00\x00\x00"


def blobs(data):
    i = data.find(MAGIC)
    while i != -1:
        if i >= 4:
            n = int.from_bytes(data[i - 4:i], "little")
            if 8 <= n <= len(data) - i:
                yield data[i:i + n]
        i = data.find(MAGIC, i + 1)


def main():
    out, roots = sys.argv[1], sys.argv[2:]
    os.makedirs(out, exist_ok=True)
    seen, witnesses, tars = set(), 0, 0
    for root in roots:
        for dirpath, _, files in os.walk(root):
            for f in files:
                p = os.path.join(dirpath, f)
                if f == "witness.bin":
                    witnesses += 1
                    with open(p, "rb") as fh:
                        datas = [fh.read()]
                elif f.endswith(".tar.gz"):
                    tars += 1
                    datas = []
                    try:
                        with tarfile.open(p) as t:
                            for m in t.getmembers():
                                if m.isfile() and m.name.endswith("witness.bin"):
                                    witnesses += 1
                                    datas.append(t.extractfile(m).read())
                    except (tarfile.TarError, OSError):
                        continue
                else:
                    continue
                for d in datas:
                    for b in blobs(d):
                        h = hashlib.sha256(b).hexdigest()
                        if h not in seen:
                            seen.add(h)
                            with open(os.path.join(out, h + ".wasm"), "wb") as fh:
                                fh.write(b)
    print(json.dumps({"witnesses": witnesses, "tarballs": tars, "modules": len(seen)}))


if __name__ == "__main__":
    main()
