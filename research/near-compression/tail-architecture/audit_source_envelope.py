#!/usr/bin/env python3
"""Reproduce source-envelope membership/mutation checks (not inner proof verification)."""
import argparse
import hashlib
import json
from pathlib import Path
from source_envelope import encode, check_membership
from receipt_list_public import emit

p = argparse.ArgumentParser(description=__doc__)
for name in ['packet', 'fixture', 'roots', 'auth', 'output']:
    p.add_argument(name, type=Path)
p.add_argument('--index', type=int, required=True)
p.add_argument('--capacity', type=int, required=True)
a = p.parse_args()
packet = a.packet.read_bytes()
roots = json.loads(a.roots.read_text())
auth = json.loads(a.auth.read_text())
public = emit(a.fixture.read_bytes(), a.capacity)
envelope = encode(packet, a.index, auth['sources'][a.index]['path'])
assert check_membership(envelope, public, roots['sources'], roots['own']) == packet
end = 12 + len(packet)
mutants = [envelope[:-1], envelope + b'\0']
for offset in [0, 8, end, end+4, 12+24+40]:
    x = bytearray(envelope)
    x[offset] ^= 1
    mutants.append(bytes(x))
for step in range(len(auth['sources'][a.index]['path'])):
    for offset in [end+8+33*step, end+9+33*step]:
        x = bytearray(envelope)
        x[offset] ^= 1
        mutants.append(bytes(x))
for mutant in mutants:
    try:
        check_membership(mutant, public, roots['sources'], roots['own'])
    except ValueError:
        pass
    else:
        raise AssertionError('mutant accepted')
a.output.write_bytes(envelope)
print(json.dumps({'bytes': len(envelope), 'extra_bytes': len(envelope)-len(packet),
                  'sha256': hashlib.sha256(envelope).hexdigest(),
                  'negative_checks': len(mutants), 'inner_proof_verified_here': False}))
