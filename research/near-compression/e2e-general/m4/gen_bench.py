"""E2E M4 benchmark program: a long call that exercises every boundary component.

`segbench(n)`: the exported `main` loops `n` times over `f(i, h)`; `f` (depth 1) stores and loads
i64 words spread over 32 KiB of linear memory (32 of the 64 one-KiB blocks), updates a global,
calls `g` (depth 2) and returns; so a cut lands inside callee frames with live locals, call
records, operand-stack values, memory writes and globals.  About 42 Wasm steps per iteration.

    python3 gen_bench.py <out.wasm> <n>
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../native/wasm-base/programs'))
import wasmasm  # noqa: E402

wasmasm.NUM['i64.extend_i32_u'] = 0xAD
wasmasm.NUM['i32.wrap_i64'] = 0xA7


def segbench(n):
    base = 1024
    g = {'params': ['i64'], 'result': 'i64', 'locals': [],
         'body': [('local.get', 0), ('i64.const', 13), 'i64.rotl', ('i64.const', 0x9E3779B97F4A7C15), 'i64.mul']}
    # f(a: i32, x: i64) -> i64, local t: i64
    f = {'params': ['i32', 'i64'], 'result': 'i64', 'locals': ['i64'],
         'body': [
             ('local.get', 1), ('i64.const', 0x100000001B3), 'i64.mul', ('local.get', 0), 'i64.extend_i32_u', 'i64.add',
             ('local.set', 2),
             ('local.get', 0), ('i32.const', 72), 'i32.mul', ('i32.const', 0x7FF8), 'i32.and', ('local.get', 2),
             ('i64.store', base),
             ('local.get', 2),
             ('local.get', 0), ('i32.const', 40), 'i32.mul', ('i32.const', 0x7FF8), 'i32.and', ('i64.load', base),
             'i64.xor', ('local.set', 2),
             ('global.get', 0), ('local.get', 2), 'i64.add', ('global.set', 0),
             ('local.get', 2), ('call', 2)]}
    i, h = 0, 1
    b = [('i64.const', 7), ('local.set', h),
         ('loop',),
           ('local.get', i), ('local.get', h), ('call', 1), ('local.set', h),
           ('local.get', i), ('i32.const', 1), 'i32.add', ('local.tee', i),
           ('i32.const', n), 'i32.lt_u', ('br_if', 0),
         ('end',),
         ('local.get', h), ('global.get', 0), 'i64.xor', 'i32.wrap_i64', 'drop',
         ('local.get', h)]
    return {'name': f'segbench{n}', 'result': 'i64', 'locals': ['i32', 'i64'], 'body': b, 'memory': True,
            'globals': [('i64', True, 5)], 'funcs': [f, g]}


if __name__ == '__main__':
    out, n = sys.argv[1], int(sys.argv[2])
    with open(out, 'wb') as fh:
        fh.write(wasmasm.assemble(segbench(n)))
