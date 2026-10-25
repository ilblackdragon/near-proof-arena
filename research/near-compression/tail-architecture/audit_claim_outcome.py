#!/usr/bin/env python3
"""Independent outcome-root field audit; deliberately not a full claim validator."""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from audit_public_merkle import reconstruct


def claim_root(data):
    pos=0
    def take(n):
        nonlocal pos
        out=data[pos:pos+n];assert len(out)==n;pos+=n;return out
    def vec():return take(struct.unpack('<I',take(4))[0])
    assert vec()==b'near-arena-claim-v3'
    assert vec()==b'near/pv86/chunk-validation/v0'
    assert struct.unpack('<I',take(4))[0]==86
    vec();take(32);inner=vec()
    assert len(inner)>=97 and inner[0] in [3,4]
    return inner[65:97]


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('claims',type=Path);p.add_argument('messages',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rows=[]
    for f in sorted(a.messages.glob('*/sha_r.json')):
        cb=(a.claims/f.parent.name/'claim.bin').read_bytes();root=claim_root(cb)
        messages=json.loads(f.read_text());leaves=sorted((m for m in messages if m['id']%16==4),key=lambda m:m['id'])
        _,derived=reconstruct([hashlib.sha256(bytes(m['bytes'])).digest() for m in leaves]);derived=derived or bytes(32)
        assert root==derived
        rows.append({'case':f.parent.name,'claim_sha256':hashlib.sha256(cb).hexdigest(),'messages_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'outcome_root':root.hex(),'leaf_count':len(leaves)})
    assert len(rows)==64
    a.output.write_text(json.dumps({'status':'CLAIM_OUTCOME_EQUALITY_ONLY_NOT_EXECUTION_VALIDITY','cases':rows},indent=2)+'\n');print('All 64 outcome roots match original claims')

if __name__=='__main__':main()
