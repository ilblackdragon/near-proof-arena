#!/usr/bin/env python3
"""Count typed outcome capacities; corpus observations are not domain bounds."""
import argparse,json
from collections import Counter
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();maximum=Counter();rows=[]
for f in sorted(a.exports.glob('*/rcpt.json')):
 v=json.loads(f.read_text());c=Counter()
 for l in v['lists']:
  for r in l['rs']:
   key=('refund_le50' if len(r['v'])<=50 else 'refund_le64') if r['hr'] else ('no_refund_le18' if len(r['v'])<=18 else 'no_refund_le64');c[key]+=1
 for k,n in c.items():maximum[k]=max(maximum[k],n)
 rows.append({'case':f.parent.name,'classes':dict(c)})
assert len(rows)==64
report={'status':'CORPUS_CAPACITY_ONLY_NOT_IMPLEMENTED_BATCH_PROFILE','maximum_receipts_by_class':dict(maximum),'sha_blocks_per_peo':{'no_refund_le18':1,'no_refund_le64':2,'refund_le50':2,'refund_le64':3},'cases':rows,'limitations':['Unseen classes need explicit supported capacity; do not infer they are impossible.','Refund-ID SHA is extra unless moved to authenticated public verifier computation.','Batch proof and deadline not measured.']}
a.output.write_text(json.dumps(report,indent=2)+'\n');print(dict(maximum))
