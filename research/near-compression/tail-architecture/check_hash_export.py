#!/usr/bin/env python3
"""Match exported NEAR hash messages to the byte/digest buses of an existing SHA trace."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import numpy as np


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--messages',type=Path,required=True);p.add_argument('--trace',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    ms=json.loads(a.messages.read_text());assert len({m['id'] for m in ms})==len(ms)
    with a.trace.open('rb') as f:log,width=struct.unpack('<II',f.read(8))
    assert width==544
    tr=np.memmap(a.trace,dtype='<u4',mode='r',offset=8,shape=(1<<log,width))
    flags=tr[:,520:536];assert np.all(flags<=1)
    base=tr[:,537].astype(np.int64)-flags.sum(axis=1,dtype=np.int64)
    keys=[];values=[]
    for q in range(16):
        rows=np.flatnonzero(flags[:,q]);pos=base[rows]+q;assert np.all(pos>=0)
        keys.append((tr[rows,538].astype(np.uint64)<<32)+pos.astype(np.uint64))
        start=256+32*(q//4)+8*(3-q%4)
        bits=tr[rows,start:start+8];assert np.all(bits<=1)
        values.append((bits*(1<<np.arange(8,dtype=np.uint32))).sum(axis=1).astype(np.uint8))
    keys=np.concatenate(keys);values=np.concatenate(values);order=np.argsort(keys)
    expected_keys=np.concatenate([(np.uint64(m['id'])<<np.uint64(32))+np.arange(len(m['bytes']),dtype=np.uint64) for m in ms])
    expected_values=np.concatenate([np.asarray(m['bytes'],dtype=np.uint8) for m in ms]);expected_order=np.argsort(expected_keys)
    assert np.array_equal(keys[order],expected_keys[expected_order])
    assert np.array_equal(values[order],expected_values[expected_order])
    assert np.all(tr[:,543]<=1)
    digests={}
    for row in np.flatnonzero(tr[:,543]):
        ident=int(tr[row,538]);assert ident not in digests
        output=bytearray()
        for w in range(8):
            col=32*(3-w) if w<4 else 128+32*(7-w)
            bits=tr[row,col:col+32];assert np.all(bits<=1)
            word=sum(int(v)<<i for i,v in enumerate(bits))
            output.extend(word.to_bytes(4,'big'))
        digests[ident]=(int(tr[row,537]),bytes(output))
    expected={m['id']:(len(m['bytes']),hashlib.sha256(bytes(m['bytes'])).digest()) for m in ms if m['dmult']}
    assert digests==expected
    report={'status':'EXPORTED_MESSAGES_MATCH_EXISTING_SHA_BUS_TRAFFIC',
            'messages':len(ms),'byte_bus_messages':len(keys),'digest_bus_messages':len(digests),
            'messages_sha256':sha(a.messages),'trace_sha256':sha(a.trace),
            'all_byte_positions_values_and_ids_equal':True,'all_enabled_digests_and_lengths_equal':True,
            'limitations':['Off-chain consistency check, not a succinct hash/receipt bus argument.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
