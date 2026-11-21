#!/usr/bin/env python3
"""pad_encoded_witness.py ZREF BASE_CASE OUT_ROOT : whole-chunk 48 MiB encoded-witness boundary fixtures.

The base case's state witness is encoded exactly as nearcore distributes it (`zref encode`, zstd
level 1, 4 workers = `CompressedData::encode`), then a zstd skippable frame (magic 0x184D2A50,
RFC 8878 §3.1.2) is appended so the `EncodedChunkStateWitness` length is exactly the target.
zstd's stream decoder skips it, so the decoded witness is byte-identical (checked with
`zref decode` under the 64 MiB limit). Variants: at-1, at (= 50,331,648), over (= at + 1), with
zero padding, plus `at.random` / `over.random` with SHA-256-counter padding."""
import hashlib, json, os, struct, subprocess, sys
from pathlib import Path

CAP = 50_331_648
zref, base, out = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])

def rb(buf, off):
    (n,) = struct.unpack_from('<I', buf, off)
    return buf[off + 4:off + 4 + n], off + 4 + n

raw = (base / 'witness.bin').read_bytes()
tag, off = rb(raw, 0)
assert tag == b'near-arena-witness-v3', tag
sw, off = rb(raw, off)
codes_region = raw[off:]
out.mkdir(parents=True, exist_ok=True)
tmp = out / '.sw'
tmp.write_bytes(sw)
subprocess.run([zref, 'encode', str(tmp), str(out / '.sw.zst'), '1', '4'], check=True)
comp = (out / '.sw.zst').read_bytes()

def payload(n, kind):
    if kind == 'zero':
        return bytes(n)
    blocks, i = [], 0
    while 32 * len(blocks) < n:
        blocks.append(hashlib.sha256(b'pad48' + i.to_bytes(8, 'little')).digest()); i += 1
    return b''.join(blocks)[:n]

rows = []
for name, target, kind in (('at-minus-1', CAP - 1, 'zero'), ('at', CAP, 'zero'), ('over', CAP + 1, 'zero'),
                           ('at.random', CAP, 'random'), ('over.random', CAP + 1, 'random')):
    n = target - len(comp) - 8
    assert n >= 0
    frame = comp + struct.pack('<II', 0x184D2A50, n) + payload(n, kind)
    assert len(frame) == target
    fz = out / '.frame'
    fz.write_bytes(frame)
    r = subprocess.run([zref, 'decode', str(fz), str(out / '.dec'), str(64 << 20)], capture_output=True, text=True)
    dec_ok = r.stdout.startswith('OK') and (out / '.dec').read_bytes() == sw
    d = out / f'pad48.{name}'
    d.mkdir(exist_ok=True)
    tagc = b'near-arena-cwitness-v3'
    (d / 'witness.bin').write_bytes(struct.pack('<I', len(tagc)) + tagc + struct.pack('<I', len(frame)) + frame + codes_region)
    (d / 'claim.bin').write_bytes((base / 'claim.bin').read_bytes())
    bm = json.loads((base / 'meta.json').read_text())
    over = target > CAP
    meta = {
        'case': f'pad48.{name}', 'kind': 'mutant', 'mutation': f'w.encoded_pad.{name}', 'base': bm['case'],
        'encoded_length': target, 'cap': CAP, 'padding': kind, 'base_encoded_length': len(comp),
        'zref_decode': r.stdout.strip(), 'decodes_to_base_witness': dec_ok,
        'verdict_source': 'nearcore rule: validate.rs:82-88 rejects encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE before any decode'
                          if over else 'nearcore(cold) verdict of the base witness: the frame decodes byte-identically (zref = vendored zstd 1.5.6)',
        'nearcore': 'reject: encoded_length exceeds witness size cap' if over else bm['nearcore'],
        'expected_rel': (not over) and bm['nearcore'] == 'ok',
    }
    (d / 'meta.json').write_text(json.dumps(meta, indent=1))
    rows.append((name, target, kind, r.stdout.strip(), dec_ok, meta['nearcore']))
for f in ('.sw', '.sw.zst', '.frame', '.dec'):
    (out / f).unlink(missing_ok=True)
print('base', base, 'sw', len(sw), 'encoded', len(comp))
for r in rows:
    print(*r, sep='\t')
