#!/usr/bin/env python3
"""Original multi-receipt RC messages plus shared source/kernel fixtures."""
import argparse,hashlib,json,struct
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('batches',type=Path);p.add_argument('output',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);cases=[]
 for f in sorted(a.exports.glob('*/rcpt.json')):
  view=json.loads(f.read_text());batch=(a.batches/(f.parent.name+'.batch')).read_bytes();messages={m['id']:bytes(m['bytes']) for m in json.loads(f.with_name('sha_r.json').read_text())};index=0
  for j,l in enumerate(view['lists']):
   records=[]
   for r in l['rs']:
    kernel=batch[40+364*index:400+364*index];index+=1;assert len(kernel)==360
    extra=struct.pack('<Q',len(r['s']))+bytes(r['s']).ljust(64,b'\0')+struct.pack('<Q',r['kt'])+bytes(r['pk']).ljust(64,b'\0')
    records.append(kernel[:280]+extra+kernel[280:])
   source=messages[1+16*j];n=len(records);assert source[:12]==struct.pack('<QI',view['own'],n)
   blob=b'NPLST001'+batch[8:32]+struct.pack('<QI',view['own'],n)+hashlib.sha256(source).digest()+b''.join(records)
   name=f'{f.parent.name}-list{j}';(a.output/(name+'.list')).write_bytes(blob);cases.append({'name':name,'count':n,'source_bytes':len(source),'sha256':hashlib.sha256(blob).hexdigest(),'source_sha256':hashlib.sha256(source).hexdigest()})
 a.report.write_text(json.dumps({'status':'ORIGINAL_LIST_FIXTURES_NOT_CLAIM_MEMBERSHIP','cases':cases},indent=2)+'\n');print(json.dumps({'lists':len(cases),'counts':sorted(set(c['count'] for c in cases)),'receipts':sum(c['count'] for c in cases)}))
if __name__=='__main__':main()
