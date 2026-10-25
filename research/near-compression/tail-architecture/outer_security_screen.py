#!/usr/bin/env python3
"""Conditional outer commitment scalar-model screen, not security certification."""
import argparse
import hashlib
import json
import math
from pathlib import Path
from sis_screen import estimate, check_model


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('setup_log',type=Path)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();check_model()
    groups=[]
    for line in a.setup_log.read_text().splitlines():
        if not line.startswith('{'):continue
        x=json.loads(line)
        base=math.sqrt(x['normsq_cap'])
        x['direct_two_opening_model']=estimate(x['rank']*64,x['columns']*64,2**48-59,2*base)
        x['legacy_extraction_factor_model']=estimate(x['rank']*64,x['columns']*64,2**48-59,168*base)
        for rank in range(1,33):
            m=estimate(rank*64,x['columns']*64,2**48-59,168*base)
            if m.get('quantum_bits',0)>=128:
                x['selected_rank']=rank;x['selected_rank_model']=m;break
        assert 'selected_rank' in x
        groups.append(x)
    fold_normsq=108*1024*648*1024
    main=[]
    primes=[3889,2917,4861,9721,12637]
    for count in range(3,6):
        q=math.prod(primes[:count]);factor=8*12*math.sqrt(3)
        main.append({'primes':primes[:count],'n':648,'m':1024*648,'q':q,
            'fold_normsq_cap':fold_normsq,'extraction_factor':factor,
            'direct_two_opening_model':estimate(648,1024*648,q,2*math.sqrt(fold_normsq)),
            'notebook_extraction_model':estimate(648,1024*648,q,factor*math.sqrt(fold_normsq))})
    report={'status':'CONDITIONAL_MODEL_SCREEN_NOT_CERTIFICATION',
        'setup_log_sha256':hashlib.sha256(a.setup_log.read_bytes()).hexdigest(),
        'bridge_commitments':groups,'ring648_commitment':main,
        'short_challenge_support_log2_upper_bound':math.log2(math.comb(162,28)),
        'limitations':['Extraction factors need protocol-specific justification; direct and extraction bounds are not interchangeable.',
            'Ring-648 screen uses enforced fold cap and notebook factor, not a newly verified extraction theorem.',
            'No structured/module/CRT attacks or Fiat-Shamir/QROM loss accounted for.',
            'Support of one challenge is not the soundness of the entire protocol.',
            'Increasing moduli and ranks alone does not establish PQ128.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print('screened',len(groups),'bridge configurations and',len(main),'main commitment configurations')


if __name__=='__main__':main()
