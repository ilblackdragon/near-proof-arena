#!/usr/bin/env python3
"""Audit this fixed template's local packet parameters; not a proof verifier."""
import argparse
import hashlib
import json
import math
import struct
import subprocess
from pathlib import Path
from audit_export import Reader
from sis_screen import screen, check_model


def audit(path, reference, profile="three"):
    count,left,right=(24,4,9) if profile=="three" else ((36,4,11) if profile=="non_leaf" else (36,5,11))
    data=path.read_bytes()
    r=Reader(data)
    assert r.take(8)=={'events':b'NPEVENT2','non_merkle':b'NPNOMRK2','non_leaf':b'NPNOLEF2'}.get(profile,b'NPTMPL01')
    parts=[r.take(r.integer()) for _ in range(7)]
    assert r.pos==len(data)
    assert len(parts[3])==left*1024 and len(parts[4])==right*1024
    assert len(parts[5])==count*8
    norms=struct.unpack('<'+str(count)+'Q',parts[5])
    # Fixed templates: only vector 1 (u) is binary, degree 64.
    # Column log 9 uses rank 1536; column log 10 uses rank 3072.
    # Others use norm.max(1) plus LOGQ-1 binary slack, matching statement.rs
    # and simple_reduce. This does not trust the proof's vector-rank metadata.
    binary_rank=1536 if profile=="non_leaf" else 3072
    source=sum(binary_rank*64 if i==1 else max(1,n)+47 for i,n in enumerate(norms))
    rows=screen(parts[6],source)
    for row in rows:
        model=row['model']
        fields=subprocess.check_output([str(reference.resolve()),str(row['module_rank']),
            str(row['ring_columns']),repr(row['collision_bound'])],text=True).split()
        assert fields[:2]==['1','1'],fields
        assert model['kind']=='finite',model
        assert (model['beta'],model['dimension'])==(int(fields[2]),int(fields[3]))
        assert math.isclose(model['quantum_bits'],float(fields[4]),abs_tol=1e-7)
    bits=[r['model']['quantum_bits'] for r in rows]
    return {'packet':str(path),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),
        'initial_statement_normsq':source,'levels':1+max(r['level'] for r in rows),
        'c_crosschecks':len(rows),'minimum_scalar_quantum_bits':min(bits),
        'all_screened_obligations_meet_128':min(bits)>=128,'instances':rows}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('packets',nargs='+',type=Path)
    p.add_argument('--reference-model',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--profile',choices=['three','five','events','non_merkle','non_leaf'],default='three')
    a=p.parse_args();check_model()
    report={'status':'BACKEND_PARAMETER_SCREEN_ONLY_NOT_PQ_CERTIFICATION',
        'limitations':['Initial commitment and outer PCS excluded.',
            'Scalar model omits structured attacks and Fiat-Shamir/QROM.',
            'Collision bounds ported from research reference; not independently proved.',
            'This reader only accepts trusted local fixed-template packets.'],
        'packets':[audit(path,a.reference_model,a.profile) for path in a.packets]}
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    for x in report['packets']:print(x['packet'],x['bytes'],x['minimum_scalar_quantum_bits'],x['all_screened_obligations_meet_128'])
