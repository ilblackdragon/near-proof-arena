#!/usr/bin/env python3
"""Emit distinct seeded whole-chunk contracts running all supported numeric float operators.

Each operator writes a distinct storage key. Successful contracts execute every operator;
trapping variants execute that same prefix then trap after a write, testing chunk rollback.
The companion runtime differential generator independently checks each operator's full output.
"""
import argparse
import json
from pathlib import Path
import random
import subprocess
from test_float_contracts import operations, contract, const, BITS
from replay_successor import sha256


def bundle(seed, trap, dynamic=False):
    rng=random.Random(seed)
    parts=[];names=[]
    for i,(op,out,args) in enumerate(operations()):
        # Trapping conversions use positive finite 0.5/1.5; NaNs and out-of-range values
        # are separately tested by the per-op runtime families and the final trap.
        values=[BITS[int(t[1:])][rng.choice((6,7))] if '.trunc_' in op and '.trunc_sat_' not in op
                else rng.choice(BITS[int(t[1:])]) for t in args]
        s=contract(op,out,args,values,rng.randrange(2))
        if dynamic:
            for j,(ty,v) in enumerate(zip(args,values)):
                w=int(ty[1:]); read=f'(i{w}.load (i32.const {64+8*j}))'
                if '.trunc_' in op and '.trunc_sat_' not in op:
                    repl=f'({ty}.convert_i{w}_u (i{w}.and {read} (i{w}.const 127)))'
                else:
                    n=v if v<2**(w-1) else v-2**w
                    mixed=f'(i{w}.xor {read} (i{w}.const {n}))'
                    repl=f'({ty}.reinterpret_i{w} {mixed})' if ty[0]=='f' else mixed
                s='\n'.join(line.replace(const(ty,v),repl) if '(local.set $x' in line else line
                            for line in s.split('\n'))
        g=s[s.index(' (global'):s.index(' (data')].replace('$g',f'$g{i}')
        f=s[s.index(' (func $run'):].rstrip()[:-1]
        f=f.replace('(export "run") (export "main") (export "cb")','').replace('$run',f'$op{i}').replace('$g',f'$g{i}')
        f=f.replace('(drop (call $write',f'(i32.store (i32.const 0) (i32.const {i}))\n  (drop (call $write',1)
        parts += [g,f];names.append(f'$op{i}')
    tail=''
    if trap:
        tail='''(i32.store (i32.const 0) (i32.const 999))
  (drop (call $write (i64.const 5) (i64.const 0) (i64.const 1) (i64.const 0) (i64.const 7)))
  (drop (i64.trunc_f64_s (f64.const nan:0x12345)))'''
    inputs='''(import "env" "input" (func $input (param i64)))
 (import "env" "read_register" (func $read (param i64 i64)))''' if dynamic else ''
    init='(call $input (i64.const 0)) (call $read (i64.const 0) (i64.const 64))' if dynamic else ''
    return '(module\n'+inputs+'''
 (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
 (import "env" "value_return" (func $return (param i64 i64)))
 (memory (export "memory") 1)
'''+ '\n'.join(parts)+ '\n(func (export "run") (export "main") (export "cb")\n'+ init+'\n'.join(f'(call {n})' for n in names)+tail+'))\n'


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--dynamic',action='store_true');a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=True);rows=[]
    for seed in (17,29,43,71):
        for trap in (False,True):
            stem=f'float-{seed}-'+('trap' if trap else 'success')
            wat=a.out/(stem+'.wat');wasm=a.out/(stem+'.wasm');wat.write_text(bundle(seed,trap,a.dynamic))
            subprocess.run(['wasm-tools','parse',str(wat),'-o',str(wasm)],check=True,timeout=30)
            rows.append(dict(seed=seed,trap=trap,dynamic=a.dynamic,wasm=str(wasm),wat_sha256=sha256(wat),wasm_sha256=sha256(wasm),operators=len(operations())))
    (a.out/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')

if __name__=='__main__': main()
