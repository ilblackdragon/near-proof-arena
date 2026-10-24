#!/usr/bin/env python3
"""Conservative range certificates from unconditional BabyBear AIR constraints.

Recognizes only explicit boolean constraints and affine equalities whose solved
nonnegative integer RHS cannot wrap modulo p. No witness-based range assumptions.
Certificates are diagnostic algebraic derivations, not Lean refinement proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path

P = 2013265921


def affine(e):
    op = e[0]
    if op == 'c':
        return int(e[1]) % P, {}
    if op == 'v':
        return 0, {(int(e[1]), int(e[2])): 1}
    if op == '-':
        c, v = affine(e[1]); return -c % P, {k:-x % P for k,x in v.items()}
    if op == '+':
        c,v = affine(e[1]); d,w = affine(e[2])
        for k,x in w.items(): v[k] = (v.get(k,0)+x) % P
        return (c+d) % P, {k:x for k,x in v.items() if x}
    if op == '*':
        c,v = affine(e[1]); d,w = affine(e[2])
        if v and w: raise ValueError('nonlinear')
        terms = {k:x*(c if w else d) % P for k,x in (w or v).items()}
        return c*d % P, {k:x for k,x in terms.items() if x}
    raise ValueError('unsupported expression')


def derive(table):
    bounds = [P-1]*table['width']
    certificates = []
    for ci,e in enumerate(table['constraints']):
        for col in range(table['width']):
            v = ['v',col,0]
            if e == ['*',v,['+',v,['-',['c',1]]]]:
                bounds[col] = 1
                certificates.append({'kind':'boolean','column':col,'bound':1,'constraint':ci})
    linear = []
    for ci,e in enumerate(table['constraints']):
        try:
            c,v = affine(e)
            if v: linear.append((ci,c,v))
        except ValueError: pass
    changed = True
    while changed:
        changed = False
        for ci,c,v in linear:
            for target, coefficient in v.items():
                inv = pow(coefficient,-1,P)
                offset = -c*inv % P
                terms = [(k,-x*inv % P) for k,x in v.items() if k != target]
                maximum = offset + sum(w*bounds[k[0]] for k,w in terms)
                if maximum < bounds[target[0]] and maximum < P:
                    certificates.append({'kind':'affine_no_wrap','column':target[0],
                        'rotation':target[1],'bound':maximum,'constraint':ci,
                        'offset':offset,'terms':[{'column':k[0],'rotation':k[1],
                             'weight':w,'prior_bound':bounds[k[0]]} for k,w in terms]})
                    bounds[target[0]] = maximum
                    changed = True
    return bounds, certificates


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--air',type=Path,required=True)
    p.add_argument('--census',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); air=json.loads(a.air.read_text()); census=json.loads(a.census.read_text())
    indices={'sha_t':0,'sha_r':1,'rcpt':16,'walk':5}
    out={'air_sha256':hashlib.sha256(a.air.read_bytes()).hexdigest(),'field_modulus':P,
         'status':'UNCONDITIONAL_AIR_RANGE_DERIVATIONS','tables':[],
         'limitations':['Syntactic certificates, not kernel-checked Lean proofs.',
                        'Static bit representation size, not proof size or prover work.',
                        'No modular arithmetic or cross-field constraint checks may be removed.']}
    for row in census['tables']:
        name=Path(row['path']).stem; table=air['tables'][indices[name]]
        assert table['width']==row['width']
        bounds, certs=derive(table)
        assert all(c['max'] <= bounds[c['column']] for c in row['columns'])
        bitwidths=[x.bit_length() for x in bounds]
        out['tables'].append({'name':name,'index':indices[name],'height':row['height'],
            'width':row['width'],'static_bits_per_row':sum(bitwidths),
            'raw_field_bytes':row['raw_field_bytes'],
            'static_payload_bytes':(sum(bitwidths)*row['height']+7)//8,
            'bit_columns':sum(b==1 for b in bounds),'byte_or_smaller_columns':sum(b<256 for b in bounds),
            'bounds':bounds,'certificates':certs,'observed_trace_respects_bounds':True})
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    for row in out['tables']:print({k:v for k,v in row.items() if k not in ['bounds','certificates']})


if __name__=='__main__': main()
