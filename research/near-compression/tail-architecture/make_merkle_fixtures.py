#!/usr/bin/env python3
"""Generate independent D0a wire/root fixtures from original SHA-r messages."""
import argparse
import hashlib
import json
import struct
from audit_hash_events import expected_dense
from audit_public_merkle import reconstruct
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('corpus', type=Path)
p.add_argument('output', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
cases = [(f.parent.name, json.loads(f.read_text())) for f in sorted(a.corpus.glob('*/sha_r.json'))]
assert len(cases) == 64
for n in [0, 1, 2, 3, 5]:
    messages = [{'id': 4 + 16*i, 'bytes': [i]*68, 'dmult': 1} for i in range(n)]
    nodes, _ = reconstruct([hashlib.sha256(bytes(m['bytes'])).digest() for m in messages])
    messages += [{'id': ident, 'bytes': list(pre), 'dmult': 1} for ident, (pre, _) in nodes.items()]
    cases.append((f'synthetic-{n}', messages))
for name, messages in cases:
    dense, wire = expected_dense(messages)
    rows = [wire[i:i+41] for i in range(12, len(wire), 41) if int.from_bytes(wire[i:i+4], 'little') % 16 != 6]
    (a.output / f'{name}.wire').write_bytes(b'NPNOMRK1' + struct.pack('<I', len(rows)) + b''.join(rows))
    (a.output / f'{name}.root').write_bytes(hashlib.sha512(dense).digest())
print(f'Generated {len(cases)} independent fixtures')
