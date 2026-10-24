#!/usr/bin/env python3
"""Diagnostic scalar Euclidean SIS cost model; NOT a security certification.

Model transcribed from LayerZero-Labs/greyhound-reference commit
672e74100496f6ef698ba35e241cf7593e3d57af, labrador.c.
Derived from Copyright 2024 IBM Corp., Apache-2.0; see evidence/security/LICENSE.
This does not price ring/module/CRT attacks or Fiat-Shamir composition.
"""
import argparse
import hashlib
import json
import math
import subprocess
from pathlib import Path
from audit_export import Reader


def rhf(beta):
    if beta <= 40:
        return 1.01295
    return (beta/(2*math.pi*math.e)*(math.pi*beta)**(1/beta))**(1/(2*(beta-1)))


def estimate(n, m, q, bound):
    assert n > 0 and m > 0 and math.isfinite(bound) and bound > 0
    if bound >= q:
        return {'kind':'trivial_bound_ge_q','quantum_bits':0}
    bound = math.ceil(bound)
    logq, logbound = math.log2(q), math.log2(bound)
    if logbound == 0:
        return {'kind':'no_finite_reduction_in_model'}
    logdelta = logbound**2/(4*n*logq)
    dimension = min(math.floor(math.sqrt(n*logq/logdelta)), m)
    assert dimension > 1
    target = 2**((logbound-n/dimension*logq)/(dimension-1))
    beta = 0
    if target >= 1 and target >= rhf(65536):
        lo, hi = 40, 65536
        while lo < hi:
            mid = (lo+hi)//2
            if rhf(mid) <= target+1e-13:
                hi = mid
            else:
                lo = mid+1
        beta = lo
    lower = .5*min(math.log(n*math.log(q)), math.log(dimension)+2*n/dimension*math.log(q))
    if not beta or beta > dimension or math.log(bound) <= lower:
        return {'kind':'no_finite_reduction_in_model','dimension':dimension}
    return {'kind':'finite','beta':beta,'dimension':dimension,'quantum_bits':.265*beta}


def check_model():
    for rank,width,bound,beta,dim in [(21,1700,499535789,507,2976),
            (14,592,16228284,486,2394),(11,250,1707129,522,2176),
            (24,115856,2568883812,491,3144)]:
        result = estimate(rank*64,width*64,2**32-99,bound)
        assert (result['beta'],result['dimension']) == (beta,dim), result
    assert estimate(64,128,2**32-99,2**32-99)['quantum_bits'] == 0


def screen(data):
    r = Reader(data)
    assert r.take(8) == b'NPLAB001'
    degree, logq, levels = [r.integer() for _ in range(3)]
    assert (degree,logq) == (64,48)
    cr,fu,bu,k,k1 = [r.integer() for _ in range(5)]
    r.take(cr*8)
    r.take(r.integer()*64*6)
    rows=[]
    for level in range(levels):
        count,tail = r.integer(),r.integer()
        pairs=[(r.integer(),r.integer()) for _ in range(count)]
        f,fu,fg,b,bu,bg,k,k1,u1,u2=[r.integer() for _ in range(10)]
        r.take(8+1024)
        normsq=r.integer()
        for _ in range(3):
            r.take(r.integer()*64*6)
        groups=sum(nu for _,nu in pairs)
        width,pending=0,0
        for n,nu in pairs:
            pending+=n
            if nu:
                width=max(width,(pending+nu-1)//nu)
                pending=0
        assert pending == 0
        tri=groups*(groups+1)//2
        # Exact legacy bounds used by the measured verifier's reduce_amortize.
        instances=[('inner_legacy_bound',k,width,6*14*2*2**((f-1)*b)*math.sqrt(normsq))]
        if not tail:
            instances += [('outer1',k1,fu*groups*k+fg*tri,4*math.sqrt(normsq)),
                          ('outer2',k1,fu*tri,4*math.sqrt(normsq))]
        for role,rank,columns,bound in instances:
            rows.append({'level':level,'role':role,'module_rank':rank,'ring_columns':columns,
                'output_normsq':normsq,'collision_bound':bound,
                'legacy_gate_accepts':math.log2(bound)<min(48,2*math.sqrt(48*math.log2(1.00444)*64*rank)),
                'model':estimate(rank*64,columns*64,2**48-59,bound)})
    return rows


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('backend',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--reference-model',type=Path,help='Compiled adjacent reference_model.c; crosscheck finite instances')
    a=p.parse_args()
    check_model()
    data=a.backend.read_bytes()
    rows=screen(data)
    report={'status':'DIAGNOSTIC_MODEL_NOT_SECURITY_PROOF','backend_sha256':hashlib.sha256(data).hexdigest(),
        'model_regressions_passed':5,'instances':rows,
        'limitations':['Uses exact legacy verifier collision bounds, not a proof those bounds are sufficient.',
            'Omits the initial Dachshund commitment and the outer LaBinius PCS.',
            'Scalar Euclidean model only; no structured attacks, QROM or recursion composition.',
            'New reference fork uses revised inner collision bounds; not substituted silently.',
            'No finite reduction in this model is not an unconditional security claim.']}
    if a.reference_model:
        checked=0
        for row in rows:
            model=row['model']
            assert model['kind']=='finite', 'Crosscheck currently covers finite instances only'
            fields=subprocess.check_output([str(a.reference_model.resolve()),str(row['module_rank']),
                str(row['ring_columns']),repr(row['collision_bound'])],text=True).split()
            assert fields[:2]==['1','1'], fields
            assert (int(fields[2]),int(fields[3]))==(model['beta'],model['dimension']), fields
            assert abs(float(fields[4])-model['quantum_bits'])<1e-7, fields
            checked+=1
        report['c_reference_crosschecks_passed']=checked
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    for row in rows: print(row['level'],row['role'],row['legacy_gate_accepts'],row['model'])


if __name__ == '__main__':
    main()
