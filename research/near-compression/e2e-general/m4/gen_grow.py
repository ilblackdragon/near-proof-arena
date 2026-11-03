"""E2E M4c test program: a call that grows memory mid-call (`wasmBaseSegAirG`).

`growbench(n)`: three phases of `n` iterations of `f(i, h)` (stores/loads over 8 KiB of the
initial memory, a global, a call of `g`), separated by memory operations:

* after phase 1: `memory.grow 1` (1024 -> 1025 pages: the tree depth goes 16 -> 17), a store into
  the grown page (address 64 MiB + 8) and a load of an untouched grown byte (zero);
* phase 2 also stores into the grown page (`f2`: address 64 MiB + 8·(i mod 64));
* after phase 2: `memory.size`, `memory.grow 2` (1025 -> 1027 pages, depth stays 17), a failing
  `memory.grow 5000` (-1), stores into the second grow's pages (64 MiB + 64 KiB + 16 and
  64 MiB + 3·64 KiB − 8), and loads back.

Cut every `K` steps, the grows land in middle segments.

    python3 gen_grow.py <out.wasm> <n>
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../native/wasm-base/programs'))
import wasmasm  # noqa: E402

wasmasm.NUM['i64.extend_i32_u'] = 0xAD
wasmasm.NUM['i32.wrap_i64'] = 0xA7
_instr = wasmasm.instr


def instr(i):
    op = i if isinstance(i, str) else i[0]
    if op == 'memory.size':
        return b'\x3F\x00'
    if op == 'memory.grow':
        return b'\x40\x00'
    return _instr(i)


wasmasm.instr = instr

GROWN = 1024 * 65536  # the first grown byte (NEAR: 1024 initial pages)


def growbench(n):
    base = 1024
    g = {'params': ['i64'], 'result': 'i64', 'locals': [],
         'body': [('local.get', 0), ('i64.const', 13), 'i64.rotl', ('i64.const', 0x9E3779B97F4A7C15), 'i64.mul']}
    # f(a: i32, x: i64) -> i64 (initial memory)
    f = {'params': ['i32', 'i64'], 'result': 'i64', 'locals': ['i64'],
         'body': [
             ('local.get', 1), ('i64.const', 0x100000001B3), 'i64.mul', ('local.get', 0), 'i64.extend_i32_u', 'i64.add',
             ('local.set', 2),
             ('local.get', 0), ('i32.const', 72), 'i32.mul', ('i32.const', 0x1FF8), 'i32.and', ('local.get', 2),
             ('i64.store', base),
             ('local.get', 2),
             ('local.get', 0), ('i32.const', 40), 'i32.mul', ('i32.const', 0x1FF8), 'i32.and', ('i64.load', base),
             'i64.xor', ('local.set', 2),
             ('global.get', 0), ('local.get', 2), 'i64.add', ('global.set', 0),
             ('local.get', 2), ('call', 2)]}
    # f2(a: i32, x: i64) -> i64: f, then a store into the first grown page
    f2 = {'params': ['i32', 'i64'], 'result': 'i64', 'locals': ['i64'],
          'body': [
              ('local.get', 0), ('local.get', 1), ('call', 1), ('local.set', 2),
              ('local.get', 0), ('i32.const', 8), 'i32.mul', ('i32.const', 0x1F8), 'i32.and', ('local.get', 2),
              ('i64.store', GROWN),
              ('local.get', 2)]}
    i, h = 0, 1

    def loop(fn):
        return [('i32.const', 0), ('local.set', i),
                ('loop',),
                ('local.get', i), ('local.get', h), ('call', fn), ('local.set', h),
                ('local.get', i), ('i32.const', 1), 'i32.add', ('local.tee', i),
                ('i32.const', n), 'i32.lt_u', ('br_if', 0),
                ('end',)]
    b = [('i64.const', 7), ('local.set', h)]
    b += loop(1)
    # grow 1 page: depth 16 -> 17; store into it, load an untouched grown byte
    b += [('i32.const', 1), 'memory.grow', 'drop',
          ('i32.const', GROWN + 8), ('local.get', h), ('i64.store', 0),
          ('local.get', h), ('i32.const', GROWN + 4000), ('i64.load', 0), 'i64.add', ('local.set', h)]
    b += loop(3)
    # memory.size; grow 2 pages (depth stays 17); a failing grow; stores into the new pages
    b += ['memory.size', 'i64.extend_i32_u', ('local.get', h), 'i64.add', ('local.set', h),
          ('i32.const', 2), 'memory.grow', 'i64.extend_i32_u', ('local.get', h), 'i64.add', ('local.set', h),
          ('i32.const', 5000), 'memory.grow', 'i64.extend_i32_u', ('local.get', h), 'i64.xor', ('local.set', h),
          ('i32.const', GROWN + 65536 + 16), ('local.get', h), ('i64.store', 0),
          ('i32.const', GROWN + 3 * 65536 - 8), ('local.get', h), ('i64.const', 3), 'i64.mul', ('i64.store', 0),
          ('i32.const', GROWN + 65536 + 16), ('i64.load', 0), ('i32.const', GROWN + 8), ('i64.load', 0), 'i64.xor',
          ('local.get', h), 'i64.add', ('local.set', h)]
    b += loop(1)
    b += [('local.get', h), ('global.get', 0), 'i64.xor', ('local.set', h), ('local.get', h)]
    return {'name': f'growbench{n}', 'result': 'i64', 'locals': ['i32', 'i64'], 'body': b, 'memory': True,
            'globals': [('i64', True, 5)], 'funcs': [f, g, f2]}


if __name__ == '__main__':
    out, n = sys.argv[1], int(sys.argv[2])
    with open(out, 'wb') as fh:
        fh.write(wasmasm.assemble(growbench(n)))
