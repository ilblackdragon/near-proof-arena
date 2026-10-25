#!/usr/bin/env python3
"""Pair independent kernel vectors with original case contexts and claim roots."""
import argparse,json,struct,hashlib
from pathlib import Path
from audit_claim_outcome import claim_root
p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('vectors',type=Path);p.add_argument('claims',type=Path);p.add_argument('output',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args();raw=a.vectors.read_bytes();assert raw[:8]==b'NPROU001';pos=12;cases=[];a.output.mkdir(parents=True,exist_ok=True)
for f in sorted(a.exports.glob('*/rcpt.json')):
 v=json.loads(f.read_text());count=sum(len(l['rs']) for l in v['lists']);ctx=v['bgp'].to_bytes(16,'little')+struct.pack('<Q',v['height']);records=[]
 for i in range(count):
  row=raw[pos:pos+361];pos+=361;assert row[-1]==1
  assert row[80:96]==ctx[:16] and row[272:280]==ctx[16:]
  records.append(struct.pack('<I',i)+row[:360])
 blob=b'NPRCB001'+ctx+struct.pack('<I',count)+b''.join(records)
 base=a.output/f.parent.name;base.with_suffix('.batch').write_bytes(blob);base.with_suffix('.context').write_bytes(ctx)
 claim=(a.claims/f.parent.name/'claim.bin').read_bytes();base.with_suffix('.root').write_bytes(claim_root(claim))
 cases.append({'case':f.parent.name,'receipts':count,'batch_sha256':hashlib.sha256(blob).hexdigest(),'claim_sha256':hashlib.sha256(claim).hexdigest()})
assert len(cases)==64 and sum(r['receipts'] for r in cases)==2138
a.report.write_text(json.dumps({'status':'INDEPENDENT_BATCH_FIXTURES_NOT_FULL_NEAR','cases':cases,'vectors_sha256':hashlib.sha256(raw).hexdigest()},indent=2)+'\n');print('Generated 64 batches / 2138 receipt witnesses')
