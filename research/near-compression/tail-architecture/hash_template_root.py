#!/usr/bin/env python3
"""Independent expected template root from exported messages, without reading a proof."""
import argparse
import hashlib
import json
from pathlib import Path
import struct

POLICY = [(1,1024), (2,2048), (4,8), (8,4), (16,2), (32,1), (2048,1)]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('messages', type=Path)
    p.add_argument('output', type=Path)
    a = p.parse_args()
    messages = json.loads(a.messages.read_text())
    assert len({m['id'] for m in messages}) == len(messages)
    buckets = [[] for _ in POLICY]
    for m in messages:
        blocks = (len(m['bytes'])+72)//64
        index = next(i for i,(capacity,_) in enumerate(POLICY) if blocks <= capacity)
        assert 0 <= m['id'] < 2**32 and m['dmult'] in [0,1]
        buckets[index].append(m)
    data = bytearray(b'NEARSHATEMPL0001'+struct.pack('>Q',sum(n for _,n in POLICY)))
    for bucket, (_, slots) in zip(buckets,POLICY):
        bucket.sort(key=lambda m:m['id'])
        assert len(bucket) <= slots
        for i in range(slots):
            if i < len(bucket):
                m = bucket[i]
                raw = bytes(m['bytes'])
                active,tag = 1,(m['id']<<32)|(len(raw)<<1)|m['dmult']
            else:
                raw = b''
                active,tag = 0,0
            data.extend(struct.pack('>QQ',active,tag))
            data.extend(hashlib.sha256(raw).digest())
    root = hashlib.sha512(data).digest()
    a.output.write_bytes(root)
    print(json.dumps({'messages':len(messages),'root_hex':root.hex(),
        'message_export_sha256':hashlib.sha256(a.messages.read_bytes()).hexdigest(),
        'root_preimage_bytes':len(data),'proof_read':False}))


if __name__ == '__main__':
    main()
