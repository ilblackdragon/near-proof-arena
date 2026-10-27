#!/usr/bin/env python3
"""Convert an in-the-clear `witness.bin` (`near-arena-witness-v3`) to the versioned compressed
format (`near-arena-cwitness-v3`), whose state-witness field carries the distributed
`EncodedChunkStateWitness` zstd bytes produced by nearcore's own codec (zstd level 1, 4 workers).

The compression is delegated to the `zref` reference harness
(`docs/evidence/lean-chunk-completion/size-limits/zref/`), which links the exact vendored zstd
`2.0.10+zstd.1.5.6` and mirrors `CompressedData::encode`. The claim is untouched; only the witness
format changes. A cold validator at `--tier allFeatures` must give the same verdict on both.

  python3 tools/d3/make_compressed_witness.py --zref PATH --in CASE_DIR --out CASE_DIR [--level 1 --workers 4]
"""
import argparse
import struct
import subprocess
from pathlib import Path

OLD_TAG = b"near-arena-witness-v3"
NEW_TAG = b"near-arena-cwitness-v3"


def read_bytes(buf, off):
    (n,) = struct.unpack_from("<I", buf, off)
    off += 4
    return buf[off:off + n], off + n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zref", required=True, type=Path, help="path to the zref binary")
    ap.add_argument("--in", dest="src", required=True, type=Path, help="case dir with claim.bin/witness.bin")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--level", type=int, default=1)
    ap.add_argument("--workers", type=int, default=4)
    a = ap.parse_args()

    raw = (a.src / "witness.bin").read_bytes()
    off = 0
    tag, off = read_bytes(raw, off)
    assert tag == OLD_TAG, f"not an in-the-clear witness.bin: {tag!r}"
    sw, off = read_bytes(raw, off)
    codes_region = raw[off:]  # borsh Vec<bytes> of contract code, carried through unchanged

    a.out.mkdir(parents=True, exist_ok=True)
    tmp_in, tmp_out = a.out / ".sw", a.out / ".sw.zst"
    tmp_in.write_bytes(sw)
    subprocess.run([str(a.zref), "encode", str(tmp_in), str(tmp_out), str(a.level), str(a.workers)], check=True)
    comp = tmp_out.read_bytes()
    tmp_in.unlink(); tmp_out.unlink()

    wb = struct.pack("<I", len(NEW_TAG)) + NEW_TAG + struct.pack("<I", len(comp)) + comp + codes_region
    (a.out / "witness.bin").write_bytes(wb)
    (a.out / "claim.bin").write_bytes((a.src / "claim.bin").read_bytes())
    meta = a.src / "meta.json"
    if meta.exists():
        (a.out / "meta.json").write_bytes(meta.read_bytes())
    print(f"sw {len(sw)} -> encoded {len(comp)} (zstd-{a.level},{a.workers}w); witness.bin {len(wb)}")


if __name__ == "__main__":
    main()
