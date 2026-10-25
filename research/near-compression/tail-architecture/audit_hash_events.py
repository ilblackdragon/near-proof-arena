#!/usr/bin/env python3
"""Independently check public job records against source messages, not NEAR semantics."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import struct
from audit_export import Reader
from hash_template_root import POLICY


def expected_dense(messages):
    ids=[m['id'] for m in messages];assert len(ids)==len(set(ids))
    buckets=[[] for _ in POLICY]
    for m in messages:
        assert 0<=m['id']<2**32 and m['dmult'] in (0,1)
        raw=bytes(m['bytes']);bi=next(i for i,(blocks,_) in enumerate(POLICY) if (len(raw)+72)//64<=blocks)
        buckets[bi].append(m)
    dense=bytearray(b'NEARSHATEMPL0001'+struct.pack('>Q',3088));compact=bytearray(b'NPEVTS01'+struct.pack('<I',len(messages)))
    for bucket,(_,capacity) in zip(buckets,POLICY):
        bucket.sort(key=lambda m:m['id']);assert len(bucket)<=capacity
        for i in range(capacity):
            if i<len(bucket):
                m=bucket[i];raw=bytes(m['bytes']);digest=hashlib.sha256(raw).digest()
                active,tag=1,(m['id']<<32)|(len(raw)<<1)|m['dmult']
                compact.extend(struct.pack('<IIB',m['id'],len(raw),m['dmult'])+digest)
            else:active,tag,digest=0,0,hashlib.sha256(b'').digest()
            dense.extend(struct.pack('>QQ',active,tag)+digest)
    return bytes(dense),bytes(compact)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('packet',type=Path);p.add_argument('messages',type=Path);p.add_argument('root',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data=a.packet.read_bytes();r=Reader(data);assert r.take(8)==b'NPEVENT2'
    parts=[r.take(r.integer()) for _ in range(7)];r.done()
    messages=json.loads(a.messages.read_text());dense,compact=expected_dense(messages)
    assert parts[0]==compact,'wire events differ from independently rebuilt source records'
    assert hashlib.sha512(dense).digest()==a.root.read_bytes(),'expected root mismatch'
    report={'status':'PUBLIC_EVENTS_MATCH_SOURCE_MESSAGES_NOT_FULL_NEAR_PROOF','packet_bytes':len(data),
        'packet_sha256':hashlib.sha256(data).hexdigest(),'messages':len(messages),
        'sections':dict(zip(['public_events','tape','claim','left_rns','opening_rns','norms','backend'],map(len,parts))),
        'framing_bytes':64,'dense_public_bytes':len(dense),'root_hex':a.root.read_bytes().hex(),
        'source_sha256':hashlib.sha256(a.messages.read_bytes()).hexdigest(),
        'job_kind_counts':dict(sorted(Counter(m['id']%16 for m in messages).items())),
        'digest_consumer_jobs':sum(m['dmult'] for m in messages),
        'same_canonical_public_vector':True,'no_private_bytes_in_public_records':True,
        'limitations':['Metadata/digests are public; no zero-knowledge claim.',
            'Expected root is a job-interface root, not yet derived by a proof from the NEAR chunk claim.',
            'Receipt byte-bus binding, other SHA bin and all execution semantics remain required.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
