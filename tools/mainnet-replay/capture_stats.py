#!/usr/bin/env python3
"""Summarize JSONL from native/capture_stats.rs; payload counts are not execution traces."""
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import statistics


def distribution(values):
    s=sorted(values)
    return dict(total=sum(s),min=min(s),median=statistics.median(s),mean=round(statistics.mean(s),2),
                p95=s[math.ceil(len(s)*.95)-1],max=max(s))


def summarize(rows):
    if not rows:raise ValueError('empty population')
    ids=Counter(r['chunk_hash'] for r in rows)
    result=dict(scope='captured payload contents; source receipt proofs may be a superset of applied receipts',
                chunks=len(rows),distinct_chunks=len(ids),witnesses_per_chunk=dict(Counter(ids.values())),
                shards=dict(Counter(r['shard'] for r in rows)),
                heights=[min(r['height'] for r in rows),max(r['height'] for r in rows)])
    for field in ['witness_bytes','chunk_bytes','main_proof_entries','source_receipt_proofs']:
        result[field]=distribution([r[field] for r in rows])
    result['implicit_transitions']=distribution([len(r['implicit_proof_entries']) for r in rows])
    for field in ['chunk_transactions','witness_transactions','witness_new_transactions',
                  'witness_source_receipts','chunk_prev_outgoing_receipts']:
        d=dict(count=sum(r[field]['count'] for r in rows),chunks_nonempty=sum(r[field]['count']>0 for r in rows),
               per_chunk=distribution([r[field]['count'] for r in rows]))
        for sub in ['actions','types','function_methods','delegate_inner_actions','delegate_inner_methods']:
            c=Counter();chunks=Counter()
            for r in rows:c.update(r[field].get(sub,{}));chunks.update(r[field].get(sub,{}).keys())
            if c:d[sub]=dict(c.most_common());d[sub+'_chunks']=dict(chunks.most_common())
        result[field]=d
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('jsonl',type=Path);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();raw=a.jsonl.read_bytes();result=summarize([json.loads(l) for l in raw.splitlines()])
    result['decoded_jsonl_sha256']=hashlib.sha256(raw).hexdigest()
    a.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
