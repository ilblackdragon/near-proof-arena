#!/usr/bin/env python3
"""Check full source sets and outcomes for a multi-list diagnostic packet."""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from audit_claim_outcome import claim_root
from multi_statement import check, encode

p = argparse.ArgumentParser(description=__doc__)
for name in ['packet', 'public', 'roots', 'auth', 'claim', 'envelope', 'report']:
    p.add_argument(name, type=Path)
p.add_argument('--capacities', required=True)
a = p.parse_args()
caps = [int(x) for x in a.capacities.split(',')]
expected = json.loads(a.roots.read_text())
auth = json.loads(a.auth.read_text())
cb = a.claim.read_bytes()
assert bytes(expected['claim_sha256']) == hashlib.sha256(cb).digest()
assert expected['witness_loaded'] is False
root = claim_root(cb)
packet = a.packet.read_bytes()
paths = [s['path'] for s in auth['sources']]
envelope = encode(packet, paths)
inner, public, counts = check(envelope, caps, 1, expected, root)
assert inner == packet and public == a.public.read_bytes()
mutants = [envelope[:-1], envelope+b'\0', encode(packet, paths[:-1]), encode(packet, paths[::-1])]
# Change list count/capacity/mode, each list's context, count, source hash and outcome.
header = 16+4*len(caps)
offsets = [0, 8, 12+8, 12+12, 12+12+4*len(caps)]
off = 12+header+8
for cap in caps:
    offsets += [off, off+3*8, off+4*8, off+5*8, off+9*8+7*8]
    off += 8*(9+11*cap)
for at in offsets:
    x = bytearray(envelope)
    x[at] ^= 1
    mutants.append(bytes(x))
rejected = 0
for x in mutants:
    if x == envelope:  # identical empty paths do not represent a changed statement
        continue
    try:
        check(x, caps, 1, expected, root)
    except ValueError:
        rejected += 1
    else:
        raise AssertionError('mutant accepted')
a.envelope.write_bytes(envelope)
report = {'status': 'HOST_SOURCE_SET_AND_OUTCOME_BINDING_NOT_STATE_VALIDITY', 'counts': counts,
          'packet_bytes': len(packet), 'envelope_bytes': len(envelope),
          'packet_sha256': hashlib.sha256(packet).hexdigest(),
          'envelope_sha256': hashlib.sha256(envelope).hexdigest(),
          'claim_sha256': hashlib.sha256(cb).hexdigest(), 'outcome_root': root.hex(),
          'negative_checks': rejected, 'inner_proof_verified_here': False}
a.report.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
