#!/usr/bin/env python3
"""Collect upstream benchmark output without upgrading analytic sizes to wire evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    repo=a.root/'labinius';rows=[]
    for suite,logn in [('m',20),('l',22)]:
        log=a.root/f'labinius-{suite}.log';s=log.read_text()
        assert 'verification: accepted' in s
        sections={};section='preamble'
        for line in s.splitlines():
            if line in ['PROVER','STATEMENT','VERIFIER']:
                section=line;sections[section]={}
            m=re.match(r'  (.*?)\s+([0-9.]+) ms$',line)
            if m and section in sections:sections[section][m[1]]=float(m[2])
        size=float(re.search(r'proof: ([0-9.]+) KB total',s)[1])
        rows.append({'suite':suite,'native_F162_elements':1<<logn,
            'witness_bits':(1<<logn)*162,'witness_payload_bytes':((1<<logn)*162+7)//8,
            'timings_ms_sum_of_stage_medians':sections,
            'analytic_total_KiB_rounded':size,'serialized_artifact_measured':False,
            'peak_rss_MB_upstream':float(re.search(r'peak resident set: ([0-9.]+) MB',s)[1]),
            'verification_accepted':True,'log_sha256':sha(log)})
        shutil.copyfile(log,a.output/log.name)
    tests=a.root/'opening-tests.log'
    assert '11 passed; 0 failed' in tests.read_text()
    shutil.copyfile(tests,a.output/tests.name)
    manifest=repo/'Cargo.toml'
    patch=subprocess.check_output(['git','-C',str(repo),'diff','--','Cargo.toml','Cargo.lock'])
    (a.output/'workspace.patch').write_bytes(patch)
    r={'upstream':'https://github.com/osdnk/labinius',
       'upstream_commit':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
       'rustflags':'-C target-cpu=native -C link-arg=-fuse-ld=mold',
       'binary_sha256':sha(a.root/'target/release/labinius'),
       'manifest_sha256':sha(manifest),'lock_sha256':sha(repo/'Cargo.lock'),
       'cpu':8,'threads':1,'repetitions_per_stage':10,
       'cases':rows,'upstream_opening_tests_passed':11,
       'limitations':['Random native binary-field witnesses, not a NEAR statement.',
         'Warm reusable buffers; totals sum per-stage medians, not cold end-to-end medians.',
         'LaBRADOR size is analytical; no serialized recursive proof or independent process replay.',
         'No full PQ security instantiation/composition audit.',
         'Public setup and witness generation excluded from displayed prover total.']}
    (a.output/'screen.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(rows,indent=2))


if __name__=='__main__':main()
