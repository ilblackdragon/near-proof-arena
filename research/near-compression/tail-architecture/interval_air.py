#!/usr/bin/env python3
"""Check every local AIR constraint on intervals of constant column values.

Equivalent row coverage follows from splitting at every referenced column change,
including rotations/wrap and first/last/transition selectors. No PCS or bus proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import time
import numpy as np
P=2013265921


def dependencies(e):
    if e[0]=='v': return {(int(e[1]),int(e[2]))}
    if e[0] in ('+','*'): return dependencies(e[1]) | dependencies(e[2])
    if e[0]=='-': return dependencies(e[1])
    return set()


def evaluate(e, rows, data, pubs, mutations):
    op=e[0]; n=len(data)
    if op=='v':
        col,rot=e[1:]; assert rot in (0,1)
        idx=(rows+rot)%n
        values=data[idx,col].astype(np.uint64)
        for (mr,mc),value in mutations.items():
            if mc==col: values[idx==mr]=value
        return values
    if op=='p': return np.uint64(pubs[e[1]])
    if op=='c': return np.uint64(e[1]%P)
    if op=='first': return (rows==0).astype(np.uint64)
    if op=='last': return (rows==n-1).astype(np.uint64)
    if op=='trans': return (rows!=n-1).astype(np.uint64)
    if op=='-': return (P-evaluate(e[1],rows,data,pubs,mutations))%P
    a=evaluate(e[1],rows,data,pubs,mutations)
    b=evaluate(e[2],rows,data,pubs,mutations)
    if op=='+': return (a+b)%P
    if op=='*': return (a*b)%P
    raise ValueError(op)


def check(table,data,pubs,changes,mutations=None):
    mutations=mutations or {}; n=len(data); count=0; failures=[]
    start=time.monotonic()
    for ci,e in enumerate(table['constraints']):
        deps=dependencies(e); pieces=[np.array([0,1,n-1],dtype=np.int64)]
        for col,rot in deps:
            pieces.append((changes[col]-rot)%n)
            for mr,mc in mutations:
                if mc==col: pieces.append(np.array([(mr-rot)%n,(mr+1-rot)%n]))
        rows=np.unique(np.concatenate(pieces)); count+=len(rows)
        values=np.broadcast_to(evaluate(e,rows,data,pubs,mutations),(len(rows),))
        bad=rows[values!=0]
        if len(bad):failures.append({'constraint':ci,'first_bad_row':int(bad[0])})
    return {'wall_s':time.monotonic()-start,'constraint_interval_evaluations':count,
            'dense_constraint_row_evaluations':n*len(table['constraints']),
            'all_local_constraints_zero':not failures,'failures':failures}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--air',type=Path,required=True);p.add_argument('--dump',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    table=json.loads(a.air.read_text())['tables'][16];path=a.dump/'rcpt.bin'
    with path.open('rb') as f:log_h,width=struct.unpack('<II',f.read(8))
    data=np.memmap(path,dtype='<u4',mode='r',offset=8,shape=(1<<log_h,width))
    pubs=np.fromfile(a.dump/'pubs.bin',dtype='<u4')
    start=time.monotonic()
    changes=[np.concatenate(([0],np.flatnonzero(data[1:,c]!=data[:-1,c])+1)) for c in range(width)]
    prep=time.monotonic()-start
    honest=check(table,data,pubs,changes); assert honest['all_local_constraints_zero']
    mutants=[]
    for row in [0,777,len(data)-1]:
        bad=check(table,data,pubs,changes,{(row,0):2});assert not bad['all_local_constraints_zero']
        mutants.append({'mutation':{'row':row,'column':0,'value':2},**bad})
    report={'status':'INTERVAL_LOCAL_CONSTRAINT_CHECK','air_sha256':hashlib.sha256(a.air.read_bytes()).hexdigest(),
        'trace':str(path),'height':len(data),'width':width,'boundary_preparation_s':prep,
        'honest':honest,'mutants':mutants,
        'limitations':['Local constraints only; no bus-balance, commitment or succinct proof.',
            'Coverage argument implemented algorithmically, not kernel-checked.',
            'All 900 original receipt constraints retained; no altered relation.',
            'Timings are Python/NumPy, not an optimized native/GPU comparison.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
