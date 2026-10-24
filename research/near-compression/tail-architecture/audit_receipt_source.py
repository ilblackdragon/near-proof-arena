#!/usr/bin/env python3
"""Parse original RC hash messages and link their fields to kernel fixtures.
Host evidence only: these equalities still must be constrained in the proof.
"""
import argparse
import hashlib
import json
import struct
from pathlib import Path

class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0
    def take(self, n):
        assert 0 <= n <= len(self.data)-self.pos, 'truncated source'
        start = self.pos
        self.pos += n
        return self.data[start:self.pos], [start, self.pos]
    def integer(self, n):
        return int.from_bytes(self.take(n)[0], 'little')
    def vector(self):
        n = self.integer(4)
        assert n <= 64, 'account length'
        return self.take(n)

def parse(data):
    r = Reader(data)
    shard, count = r.integer(8), r.integer(4)
    assert count <= 65535
    rows = []
    for _ in range(count):
        row = {'start': r.pos}
        for name in ['predecessor', 'receiver']:
            row[name], row[name+'_span'] = r.vector()
        row['rid'], row['rid_span'] = r.take(32)
        assert r.integer(1) == 0, 'not action receipt'
        row['signer'], row['signer_span'] = r.vector()
        kind = r.integer(1)
        assert kind in (0, 1), 'public key kind'
        row['pk'], row['pk_span'] = r.take(32 if kind == 0 else 64)
        row['gas_price'], row['gas_price_span'] = r.take(16)
        assert r.take(13)[0] == bytes(8)+b'\x01\0\0\0\x03', 'not one transfer'
        row['deposit'], row['deposit_span'] = r.take(16)
        row['end'] = r.pos
        rows.append(row)
    assert r.pos == len(data), 'trailing source bytes'
    return shard, rows

def check(row, kernel):
    assert len(kernel) == 360
    p_len = int.from_bytes(kernel[96:104], 'little')
    v_len = int.from_bytes(kernel[168:176], 'little')
    assert row['predecessor'] == kernel[104:168][:p_len] and len(row['predecessor']) == p_len
    assert row['receiver'] == kernel[176:240][:v_len] and len(row['receiver']) == v_len
    assert row['rid'] == kernel[240:272]
    assert row['gas_price'] == kernel[64:80]
    assert row['deposit'] == kernel[16:32]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('exports', type=Path)
    ap.add_argument('batches', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    cases, mutations = [], 0
    for file in sorted(args.exports.glob('*/sha_r.json')):
        batch = (args.batches/(file.parent.name+'.batch')).read_bytes()
        assert batch[:8] == b'NPRCB001'
        count = struct.unpack_from('<I', batch, 32)[0]
        assert len(batch) == 36+364*count
        jobs = sorted((m for m in json.loads(file.read_text()) if m['id'] % 16 == 1), key=lambda m:m['id'])
        index, lists = 0, []
        for job in jobs:
            data = bytes(job['bytes'])
            shard, rows = parse(data)
            spans = []
            for row in rows:
                offset = 36+364*index
                assert struct.unpack_from('<I', batch, offset)[0] == index
                kernel = batch[offset+4:offset+364]
                check(row, kernel)
                for field in ['predecessor', 'receiver', 'rid', 'gas_price', 'deposit']:
                    if not row[field]:
                        continue
                    changed = dict(row)
                    changed[field] = bytes([row[field][0]^1])+row[field][1:]
                    try:
                        check(changed, kernel)
                    except AssertionError:
                        mutations += 1
                    else:
                        raise AssertionError('source mutation survived')
                spans.append({'index':index, 'start':row['start'], 'end':row['end'], **{k:v for k,v in row.items() if k.endswith('_span')}})
                index += 1
            lists.append({'job_id':job['id'], 'shard':shard, 'bytes':len(data), 'sha_blocks':(len(data)+9+63)//64, 'sha256':hashlib.sha256(data).hexdigest(), 'receipts':spans})
        assert index == count
        cases.append({'case':file.parent.name, 'receipts':count, 'lists':lists})
    report = {'status':'HOST_SOURCE_TO_KERNEL_CONFORMANCE_NOT_PROOF', 'cases':cases, 'rejected_field_mutations':mutations,
              'unbound_source_fields':['signer','key type/public key','list shard/count/order'],
              'non_source_kernel_inputs':['before balance','locked balance','storage usage','block gas price','height'],
              'remaining':'Constrain parser/serialization on shared kernel wires; authenticate RC digests, list inclusion/order and account state.'}
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'cases':len(cases),'receipts':sum(c['receipts'] for c in cases),'mutations':mutations,'max_source_sha_blocks':max(sum(l['sha_blocks'] for l in c['lists']) for c in cases)}))

if __name__ == '__main__':
    main()
