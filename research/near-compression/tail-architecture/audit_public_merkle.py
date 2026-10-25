#!/usr/bin/env python3
"""Check D0a public outcome-tree reconstruction; no succinct statement binding claim."""
import argparse
import hashlib
import json
from pathlib import Path
import time


def reconstruct(leaves):
    level=list(leaves);jobs={};base=0
    while len(level)>1:
        nxt=[]
        for i in range(0,len(level),2):
            if i+1==len(level):nxt.append(level[i]);continue
            pre=level[i]+level[i+1];digest=hashlib.sha256(pre).digest()
            jobs[6+16*(base+i//2)]=(pre,digest);nxt.append(digest)
        base+=len(level)//2;level=nxt
    return jobs,level[0] if level else None


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('corpus',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    # Odd nodes are promoted unchanged, never duplicated and hashed again.
    one=bytes(range(32));two=bytes(reversed(range(32)));three=b'\x03'*32
    assert reconstruct([])==({},None) and reconstruct([one])==({},one)
    jobs,root=reconstruct([one,two,three]);assert len(jobs)==2
    assert jobs[6][0]==one+two and jobs[22][0]==hashlib.sha256(one+two).digest()+three
    rows=[]
    for path in sorted(a.corpus.glob('*/sha_r.json')):
        messages=json.loads(path.read_text());assert len({m['id'] for m in messages})==len(messages)
        leaves=sorted((m for m in messages if m['id']%16==4),key=lambda m:m['id'])
        assert [m['id'] for m in leaves]==[4+16*i for i in range(len(leaves))]
        assert all(m['dmult']==1 for m in leaves)
        public_leaves=[hashlib.sha256(bytes(m['bytes'])).digest() for m in leaves]
        start=time.perf_counter();derived,root=reconstruct(public_leaves);elapsed=time.perf_counter()-start
        actual={m['id']:m for m in messages if m['id']%16==6};assert derived.keys()==actual.keys()
        for ident,(pre,digest) in derived.items():
            m=actual[ident];assert m['dmult']==1 and bytes(m['bytes'])==pre
            assert hashlib.sha256(bytes(m['bytes'])).digest()==digest
        remaining=[m for m in messages if m['id']%16!=6]
        buckets=[0]*7;policy=[(1,1024),(2,1024),(4,8),(8,4),(16,2),(32,1),(2048,1)]
        for m in remaining:
            bi=next(i for i,(blocks,_) in enumerate(policy) if (len(m['bytes'])+72)//64<=blocks);buckets[bi]+=1
        assert all(n<=capacity for n,(_,capacity) in zip(buckets,policy))
        rows.append({'case':path.parent.name,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'leaves':len(leaves),'derived_nodes':len(derived),'removed_sha_compressions':2*len(derived),
            'remaining_jobs':len(remaining),'remaining_bucket_counts':buckets,
            'root_hex':root.hex() if root else None,'python_reconstruction_seconds':elapsed})
    assert rows
    report={'status':'ALL_D0A_MERKLE_PREIMAGES_MATCH_PUBLIC_RECONSTRUCTION','cases':rows,
        'case_count':len(rows),'candidate_non_merkle_policy':policy,
        'candidate_sha_block_slots':sum(b*n for b,n in policy),
        'limitations':['Input leaf digests must be authenticated by the proof, not merely supplied.',
            'Full expected job root/NEAR chunk claim binding is not implemented here.',
            'D1 transaction leaves and other outcome variants require their own semantics.',
            'Corpus fit is not a held-out capacity guarantee.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print('matched',len(rows),'cases; max nodes',max(x['derived_nodes'] for x in rows),'candidate slots',report['candidate_sha_block_slots'])


if __name__=='__main__':main()
