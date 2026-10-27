#!/usr/bin/env python3
"""Generate the NPMWASM01 KAT ladder for the LaBRADOR Wasm vertical slice.

Programs are drawn from the wasm-base generator families (gen.py's kat/ctrl/
hashloop/memkat/globkat shapes, re-emitted via wasm_trace_export) plus a
ladder-scaling hashloop. Div/rem and host-call programs are EXCLUDED from
rung fixtures per WASM_SLICE_DEF.md (in the corpus, deferred to a later rung).
"""
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE))
sys.path.insert(0, str(BASE / '../../native/wasm-base/programs'))
import random

from wasm_trace_export import emit_fixture, N_STACK, N_LOCALS, N_GLOBALS


def kat_i32_add(n):
    """Straight-line i32 add chain, n instructions (the 8/64/512/2048 rungs)."""
    body = [('i32.const', 1), ('local.set', 0)]
    for k in range(n - 4):
        body += [('local.get', 0), ('i32.const', (k * 2654435761) % (1 << 31)), 'i32.add', ('local.set', 0)]
    body += [('local.get', 0)]
    return {'name': f'addchain{n}', 'result': 'i32', 'locals': ['i32'], 'body': body}


def mixprog(n):
    """Mixed i32/i64 ops, locals/globals/stack churn — the realistic rung."""
    body = [('i64.const', 0xcbf29ce484222325), ('local.set', 0),
            ('i32.const', 0x12345678), ('local.set', 2)]
    for k in range(max(1, n // 12)):
        body += [
            ('local.get', 0), ('i64.const', 0x100000001b3), 'i64.mul', ('local.tee', 0),
            ('i64.const', 13), 'i64.rotl',
            ('local.get', 0), ('i64.const', 7), 'i64.shr_u', 'i64.xor', ('local.set', 0),
            ('local.get', 2), ('i32.const', 3), 'i32.shl',
            ('local.get', 2), ('i32.const', 2), 'i32.shr_s', 'i32.xor',
            ('i32.const', 0x9e3779b9), 'i32.add', ('local.tee', 2),
            ('global.set', 0),
            ('global.get', 0), ('i64.const', 31), 'i64.and', 'drop',
            ('local.get', 0), ('global.get', 0), 'i64.mul', ('local.set', 1),
        ]
    body += [('local.get', 0), ('local.get', 1), 'i64.xor',
             ('local.get', 1), ('i64.const', 29), 'i64.rotl', 'i64.xor']
    return {'name': f'mix{k and max(1, n // 12) or 1}', 'result': 'i64',
            'locals': ['i64', 'i64', 'i32'], 'globals': [('i64', True, 7)],
            'body': body}


def memprog_fixed(n):
    body = [('i32.const', 0), ('local.set', 3)]
    for k in range(max(1, n // 10)):
        off = (k * 8) % 128
        body += [
            ('local.get', 3), ('i32.const', off), 'i32.add',
            ('local.get', 0), ('i64.const', 0x9e3779b97f4a7c15), 'i64.mul', ('i64.const', k % 7), 'i64.rotl',
            'i64.store',
            ('local.get', 3), ('i32.const', off), 'i32.add', 'i64.load', ('local.set', 0),
            ('local.get', 3), ('i32.const', (off * 3) % 128), 'i32.add', ('local.get', 0), 'i64.store32',
            ('local.get', 3), ('i32.const', (off * 3) % 128), 'i32.add', 'i64.load32_u', ('local.tee', 2),
            'drop',
        ]
    body += [('local.get', 0), ('local.get', 0), ('i64.const', 17), 'i64.rotr', 'i64.xor',
             ('local.get', 2), 'i64.xor']
    return {'name': f'memmix{max(1, n // 10)}', 'result': 'i64',
            'locals': ['i64', 'i64', 'i32', 'i32'], 'body': body}


def ctrlprog():
    """Bounded control: block/br/br_if with fixed trip counts (unrolled by construction)."""
    b = [
        ('i32.const', 0), ('local.set', 0),
        ('block', 'i32'),
          ('i32.const', 5), ('i32.const', 6), 'i32.add',
          ('block',),
            ('local.get', 0), ('br_if', 0),
            ('i32.const', 1), ('local.set', 0),
          ('end',),
          ('local.get', 0), ('i32.const', 1), 'i32.eq', ('br_if', 0),
          ('i32.const', 99),
        ('end',),
        ('local.set', 1),
        ('local.get', 1), ('local.get', 0), 'i32.add',
    ]
    return {'name': 'ctrlbounded', 'result': 'i64', 'locals': ['i32', 'i32'], 'body': b}


def main():
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    progs = []
    # Rung targets are INSTRUCTION-COUNT classes, not exact step counts:
    # the fixture records actual steps (addchain2048 = 2048 steps exactly;
    # mix/mem rungs land proportionally under the 2048-step circuit bound).
    for steps in (8, 64, 512, 2044):
        progs.append(kat_i32_add((steps + 13) // 4))
    # block counts sized so every rung stays under the 2048-step circuit bound
    # mix: 16 instrs/block; the 2048-step rung = 120 blocks (1920+52=1972 fits).
    # mix120 measured 3612 — re-check: emit says 3612 steps for 120 blocks => 30/block.
    # Fit to the 2048 bound: mix <= 66 blocks (1986), memmix <= 140 (3510 > 2048 => 102 blocks = 1434+6).
    for blocks in (1, 5, 42, 66):
        progs.append(mixprog(blocks * 12))
    for blocks in (1, 5, 42, 80):
        progs.append(memprog_fixed(blocks * 10))
    progs.append(ctrlprog())
    for p in progs:
        n_steps, nbytes, result, kind = emit_fixture(p, out / (p['name'] + '.bin'))
        print(f'{p["name"]}: steps={n_steps} bytes={nbytes} result={result} kind={kind}')
    print(f'{len(progs)} fixtures -> {out}')


if __name__ == '__main__':
    main()
