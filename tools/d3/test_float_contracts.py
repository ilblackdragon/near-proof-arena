#!/usr/bin/env python3
"""Independent WAT float families with observable storage, return, globals and control flow.

This is executable parity evidence, not a floating-point refinement proof. Each result records
its source/wasm identity; --golden replays saved nearcore outputs without a nearcore installation.
"""
import argparse
import json
from pathlib import Path
import random
import subprocess
import tempfile
from replay_successor import REPO, sha256


def operations():
    out = []
    for ty in ('f32', 'f64'):
        for op in ('eq','ne','lt','gt','le','ge'):
            out.append((f'{ty}.{op}', 'i32', (ty,ty)))
        for op in ('abs','neg','ceil','floor','trunc','nearest','sqrt'):
            out.append((f'{ty}.{op}', ty, (ty,)))
        for op in ('add','sub','mul','div','min','max','copysign'):
            out.append((f'{ty}.{op}', ty, (ty,ty)))
    for dst in ('i32','i64'):
        for src in ('f32','f64'):
            for sign in ('s','u'):
                for kind in ('trunc','trunc_sat'):
                    out.append((f'{dst}.{kind}_{src}_{sign}', dst, (src,)))
    for dst in ('f32','f64'):
        for src in ('i32','i64'):
            for sign in ('s','u'):
                out.append((f'{dst}.convert_{src}_{sign}', dst, (src,)))
    out += [('f32.demote_f64','f32',('f64',)), ('f64.promote_f32','f64',('f32',))]
    for a,b in (('i32','f32'),('i64','f64'),('f32','i32'),('f64','i64')):
        out.append((f'{a}.reinterpret_{b}', a, (b,)))
    return out


BITS = {
    32: [0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x3f000000,0x3fc00000,
         0x40200000,0x7f800000,0xff800000,0x7fc12345,0xff812345,0x4f000000,0x4f800000],
    64: [0,0x8000000000000000,1,0x8000000000000001,0xfffffffffffff,0x10000000000000,
         0x3fe0000000000000,0x3ff8000000000000,0x4004000000000000,0x7ff0000000000000,
         0xfff0000000000000,0x7ff8123456789abc,0xfff0123456789abc,0x43e0000000000000,0x43f0000000000000],
}


def const(ty, value):
    width = int(ty[1:])
    n = value if value < 2**(width-1) else value-2**width
    expr = f'(i{width}.const {n})'
    return f'({ty}.reinterpret_i{width} {expr})' if ty[0]=='f' else expr


def contract(op, out, args, values, variant):
    expr = f'({op} ' + ' '.join(const(t,v) for t,v in zip(args,values)) + ')'
    # Float globals/local/select/load/store all carry actual results to storage and return.
    branch = f'(if (result {out}) (i32.const {variant % 2}) (then {expr}) (else {expr}))'
    return f'''(module
 (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
 (import "env" "value_return" (func $return (param i64 i64)))
 (memory (export "memory") 1)
 (global $g (mut {out}) ({out}.const 0))
 (data (i32.const 0) "float")
 (func $run (export "run") (export "main") (export "cb") (local $x {out})
  (drop (call $write (i64.const 5) (i64.const 0) (i64.const 1) (i64.const 0) (i64.const 7)))
  (local.set $x {branch})
  (global.set $g (select (local.get $x) (local.get $x) (i32.const {variant%2})))
  ({out}.store (i32.const 16) (global.get $g))
  ({out}.store (i32.const 24) ({out}.load (i32.const 16)))
  (drop (call $write (i64.const 5) (i64.const 0) (i64.const {int(out[1:])//8}) (i64.const 24) (i64.const 7)))
  (call $return (i64.const {int(out[1:])//8}) (i64.const 24))))'''


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--golden',type=Path)
    ap.add_argument('--generated-per-seed',type=int,default=250)
    ap.add_argument('--lean',type=Path,default=REPO/'spec/lean/v3/.lake/build/bin/nearspec-v3-runtime')
    ap.add_argument('--harness',type=Path,default=Path('/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness'))
    a=ap.parse_args()
    if a.generated_per_seed<0: ap.error('negative population')
    a.out.mkdir(parents=True,exist_ok=True)
    report={'status':'running'}
    rp=a.out/'report.json';rp.write_text(json.dumps(report)+'\n')
    cases=[]
    for op,out,args in operations():
        for i in range(15):
            cases.append(dict(op=op,out=out,args=args,values=[BITS[int(t[1:])][i] for t in args],variant=i,seed=None))
    for seed in (17,29,43,71):
        rng=random.Random(seed)
        for i in range(a.generated_per_seed):
            op,out,args=rng.choice(operations())
            cases.append(dict(op=op,out=out,args=args,values=[rng.getrandbits(int(t[1:])) for t in args],variant=i,seed=seed))
    golden=[json.loads(s) for s in a.golden.read_text().splitlines()] if a.golden else None
    if golden is not None and len(golden)!=len(cases): raise ValueError('golden population differs')
    rows=[]
    with tempfile.TemporaryDirectory() as td:
        wat=Path(td)/'case.wat';wasm=Path(td)/'case.wasm'
        for i,c in enumerate(cases):
            wat.write_text(contract(**{k:v for k,v in c.items() if k!='seed'}))
            if golden is None:
                subprocess.run(['wasm-tools','parse',str(wat),'-o',str(wasm)],check=True,capture_output=True,timeout=30)
            else:
                wasm.write_bytes(bytes.fromhex(golden[i]['wasm_hex']))
            code=wasm.read_bytes()
            oracle=golden[i]['oracle'] if golden is not None else subprocess.run(
                [str(a.harness),'runtime-full'],input=f'300000000000000 {code.hex()}\n',
                capture_output=True,text=True,check=True,timeout=120).stdout.strip()
            if not (oracle.startswith('ok ') or (oracle.startswith('abort ') and 'WasmTrap(IllegalArithmetic)' in oracle)) or any(field not in oracle for field in (' || compute ', ' || logs ', ' || actions ', ' || trie')):
                raise ValueError(f'invalid or unexpected full float outcome: {oracle[:200]}')
            if golden is not None and (golden[i]['case']!=json.loads(json.dumps(c)) or golden[i]['wasm_sha256']!=sha256(wasm) or golden[i]['wat_sha256']!=sha256(wat)):
                raise ValueError('golden input differs')
            lean=subprocess.run([str(a.lean),str(wasm)],capture_output=True,text=True,check=True,timeout=120).stdout.strip()
            row=dict(case=c,wasm_hex=code.hex(),wasm_sha256=sha256(wasm),wat_sha256=sha256(wat),oracle=oracle,lean=lean,match=oracle==lean)
            rows.append(row)
            if oracle!=lean:
                (a.out/'failure.wat').write_text(wat.read_text())
                (a.out/'results.jsonl').write_text('\n'.join(json.dumps(r,sort_keys=True) for r in rows)+'\n')
                rp.write_text(json.dumps({'status':'fail','case':i,'row':row},indent=2)+'\n')
                raise RuntimeError(f'float mismatch at {i}: {c}:\n{oracle}\n{lean}')
    results=a.out/'results.jsonl';results.write_text('\n'.join(json.dumps(r,sort_keys=True) for r in rows)+'\n')
    report=dict(status='pass',per_seed={str(seed):sum(r['case']['seed']==seed for r in rows) for seed in (17,29,43,71)},cases=len(rows),operators=len(operations()),generated_per_seed=a.generated_per_seed,
                successes=sum(r['oracle'].startswith('ok ') for r in rows),traps=sum('WasmTrap' in r['oracle'] for r in rows),
                lean_sha256=sha256(a.lean),oracle_sha256=sha256(a.harness) if golden is None else None,
                generator_sha256=sha256(Path(__file__)),results_sha256=sha256(results))
    rp.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report))

if __name__=='__main__':
    # Any uncaught process/input failure exits nonzero; a stale pass was invalidated at entry.
    main()
