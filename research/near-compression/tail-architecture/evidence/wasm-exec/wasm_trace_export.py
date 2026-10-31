#!/usr/bin/env python3
"""Trace export for the NPMWASM01 circuit fixtures (LaBRADOR vertical slice).

Re-implements the wasm-base refinterp.py execution loop as a TRACING variant:
same spec-derived semantics (the file imports refinterp's binop and shares no
prover code), but records per-step state. Emits both .trace.json (for the
audit) and the .bin NPMWASM01 fixture (for the circuit).

NPMWASM01 layout (all little-endian):
  magic(9) "NPMWASM01" || u32 version(=1)
  || u32 n_steps || u32 n_stack || u32 n_locals || u32 n_globals || u32 mem_words
  || u32 code_len || code bytes (wasmasm.assemble output)
  || u64 total_gas
  || initial state: stack u64[n_stack] || locals u64[n_locals] || globals u64[n_globals]
  || initial memory u64[mem_words]
  || per step: u32 pc || u32 opcode_tag || u64 a || u64 b || u64 out
       || u32 stack_height || stack u64[n_stack] || locals u64[n_locals]
  || final state: stack u64[n_stack] || locals u64[n_locals] || globals u64[n_globals]
  || u64 result || u32 result_kind (0=trap/1=value)
  || sha256(reference_digest over the whole preceding stream, 32 bytes)

Step encoding: one row per EXECUTED instruction. pc = index into the
flattened instruction list. a/b = the two popped operands (b first-pop first
in a, then b — i.e. for `a op b`, operand a then b; unused = 0), out = the
value pushed (if any; else 0), stack_height = height AFTER the step. The full
stack/locals arrays are snapshotted per step (the circuit binds step N's
state to step N+1's via these; memory rows only on load/store steps).

Opcode tags: a fixed u32 enum emitted alongside (see OP_TAGS), stable across
generator and circuit.
"""
import hashlib
import json
import struct
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
WASMBASE = Path('/data/illia/nearproof-wt/pq-tail-architecture/research/near-compression/native/wasm-base/programs')
sys.path.insert(0, str(WASMBASE))
from refinterp import binop, sg, Trap, M32, M64  # noqa: E402

# Copied verbatim from refinterp.run()'s locals (they are not module-level there).
LOADS = {'i32.load': (4, False, 32), 'i64.load': (8, False, 64), 'i32.load8_s': (1, True, 32),
         'i32.load8_u': (1, False, 32), 'i32.load16_s': (2, True, 32), 'i32.load16_u': (2, False, 32),
         'i64.load8_s': (1, True, 64), 'i64.load8_u': (1, False, 64), 'i64.load16_s': (2, True, 64),
         'i64.load16_u': (2, False, 64), 'i64.load32_s': (4, True, 64), 'i64.load32_u': (4, False, 64)}
STORES = {'i32.store': 4, 'i64.store': 8, 'i32.store8': 1, 'i32.store16': 2, 'i64.store8': 1,
          'i64.store16': 2, 'i64.store32': 4}

# Stable opcode tags for the circuit (u32). Not Wasm opcode bytes: the circuit
# works on this dense enum; the fixture's code bytes remain real Wasm.
OP_TAGS = {}
_I32 = ['i32.eqz', 'i32.eq', 'i32.ne', 'i32.lt_s', 'i32.lt_u', 'i32.gt_s',
        'i32.gt_u', 'i32.le_s', 'i32.le_u', 'i32.ge_s', 'i32.ge_u',
        'i32.add', 'i32.sub', 'i32.mul', 'i32.and', 'i32.or', 'i32.xor',
        'i32.shl', 'i32.shr_s', 'i32.shr_u', 'i32.rotl', 'i32.rotr']
_I64 = [o.replace('i32', 'i64') for o in _I32]
_MISC = ['i32.const', 'i64.const', 'drop', 'select', 'local.get', 'local.set',
         'local.tee', 'global.get', 'global.set', 'block', 'loop', 'br',
         'br_if', 'return', 'end', 'nop',
         'i32.load', 'i64.load', 'i32.load8_u', 'i64.load32_u',
         'i32.store', 'i64.store', 'i32.store8', 'i64.store32']
for _i, _op in enumerate(_I32 + _I64 + _MISC):
    OP_TAGS[_op] = _i + 1
OP_TAGS['other'] = 0

N_STACK, N_LOCALS, N_GLOBALS, MEM_WORDS = 64, 16, 8, 256


class TraceState:
    def __init__(self):
        self.steps = []       # dicts: pc, op, tag, a, b, out, gas
        self.stack = []       # logical stack (values)
        self.locals_ = []
        self.globals_ = []
        self.mem = {}


def run_traced(prog, n_steps_cap=4096):
    """Execute function 0 with tracing; returns (state, result, result_kind)."""
    st = TraceState()
    st.globals_ = [v & (M32 if t == 'i32' else M64) for t, _, v in prog.get('globals', [])]
    st.locals_ = [0] * max(len(prog.get('locals', [])), 1)
    body = [i if isinstance(i, tuple) else (i,) for i in prog['body']] + [('end',)]
    end_of, stack = {}, []
    for pc, i in enumerate(body):
        if i[0] in ('block', 'loop'):
            stack.append(pc)
        elif i[0] == 'end':
            if stack:
                end_of[stack.pop()] = pc
    labels = [('func', len(body), 1 if prog.get('result') else 0, 0)]
    pc = 0
    cnt = 0
    result = None
    kind = 1

    def record(op, tag, a=0, b=0, out=0, gas=1):
        st.steps.append({'pc': pc, 'op': op, 'tag': tag, 'a': a, 'b': b,
                         'out': out, 'gas': gas, 'stack': list(st.stack),
                         'locals': list(st.locals_), 'globals': list(st.globals_)})

    def do_branch(l):
        nonlocal pc, kind, result
        k, tgt, ar, h = labels[-1 - l]
        vals = st.stack[len(st.stack) - ar:] if ar else []
        del st.stack[h:]
        st.stack.extend(vals)
        if k == 'func':
            result = st.stack[-1] if st.stack else None
            return True
        del labels[len(labels) - (l if k == 'loop' else l + 1):]
        pc = tgt
        return False

    while True:
        cnt += 1
        if cnt > n_steps_cap:
            raise RuntimeError('step cap exceeded (fixture would overflow the circuit bound)')
        i = body[pc]
        op = i[0]
        if op in ('i32.const', 'i64.const'):
            v = i[1] & (M32 if op[1] == '3' else M64)
            st.stack.append(v)
            record(op, OP_TAGS[op], out=v)
            pc += 1
        elif op == 'drop':
            v = st.stack.pop()
            record(op, OP_TAGS[op], out=v)
            pc += 1
        elif op == 'select':
            c = st.stack.pop()
            b = st.stack.pop()
            a = st.stack.pop()
            out = a if c else b
            st.stack.append(out)
            record(op, OP_TAGS[op], a=a, b=b, out=out)
            pc += 1
        elif op == 'local.get':
            out = st.locals_[i[1]]
            st.stack.append(out)
            record(op, OP_TAGS[op], a=i[1], out=out)
            pc += 1
        elif op == 'local.set':
            out = st.stack.pop()
            st.locals_[i[1]] = out
            record(op, OP_TAGS[op], a=i[1], out=out)
            pc += 1
        elif op == 'local.tee':
            out = st.stack[-1]
            st.locals_[i[1]] = out
            record(op, OP_TAGS[op], a=i[1], out=out)
            pc += 1
        elif op == 'global.get':
            out = st.globals_[i[1]]
            st.stack.append(out)
            record(op, OP_TAGS[op], a=i[1], out=out)
            pc += 1
        elif op == 'global.set':
            out = st.stack.pop()
            st.globals_[i[1]] = out
            record(op, OP_TAGS[op], a=i[1], out=out)
            pc += 1
        elif op in LOADS:
            w, sgn, rw = LOADS[op]
            base = st.stack.pop()
            ea = base + (i[1] if len(i) > 1 else 0)
            v = sum(st.mem.get(ea + k, 0) << (8 * k) for k in range(w))
            if sgn and v >> (8 * w - 1):
                v = (v - (1 << (8 * w))) & ((1 << rw) - 1)
            st.stack.append(v)
            record(op, OP_TAGS.get(op, 0), a=base, out=v)
            pc += 1
        elif op in STORES:
            w = STORES[op]
            v = st.stack.pop()
            base = st.stack.pop()
            ea = base + (i[1] if len(i) > 1 else 0)
            for k in range(w):
                st.mem[ea + k] = (v >> (8 * k)) & 0xFF
            record(op, OP_TAGS.get(op, 0), a=base, b=v, out=ea)
            pc += 1
        elif op in ('i32.eqz', 'i64.eqz'):
            a = st.stack.pop()
            out = int(a == 0)
            st.stack.append(out)
            record(op, OP_TAGS[op], a=a, out=out)
            pc += 1
        elif op == 'block':
            ar = 0 if len(i) < 2 or i[1] is None else 1
            labels.append(('block', end_of[pc] + 1, ar, len(st.stack)))
            record(op, OP_TAGS[op])
            pc += 1
        elif op == 'loop':
            labels.append(('loop', pc + 1, 0, len(st.stack)))
            record(op, OP_TAGS[op])
            pc += 1
        elif op == 'end':
            record(op, OP_TAGS[op])
            if len(labels) == 1:
                result = st.stack[-1] if st.stack else None
                return st, result, 1
            labels.pop()
            pc += 1
        elif op == 'br':
            record(op, OP_TAGS[op])
            if do_branch(i[1]):
                return st, result, 1
        elif op == 'br_if':
            c = st.stack.pop()
            record(op, OP_TAGS[op], a=c)
            if c:
                if do_branch(i[1]):
                    return st, result, 1
            else:
                pc += 1
        elif op == 'return':
            record(op, OP_TAGS[op])
            result = st.stack[-1] if st.stack else None
            return st, result, 1
        elif op == 'nop':
            record(op, OP_TAGS[op])
            pc += 1
        else:
            b = st.stack.pop()
            a = st.stack.pop()
            out = binop(op, a, b)
            st.stack.append(out)
            record(op, OP_TAGS.get(op, 0), a=a, b=b, out=out)
            pc += 1


def emit_fixture(prog, out_path, n_steps_cap=4096):
    """Run traced, then write the NPMWASM01 binary + .trace.json."""
    try:
        st, result, kind = run_traced(prog, n_steps_cap)
    except Trap:
        # traps are outside the first rung (no div in circuit); record honestly
        raise
    n = len(st.steps)
    code = None
    # code: assemble via wasmasm for the real bytecode
    sys.path.insert(0, str(WASMBASE))
    import wasmasm
    code = wasmasm.assemble({k: v for k, v in prog.items() if k != 'body'} | {'body': prog['body']})
    total_gas = sum(s['gas'] for s in st.steps)

    def pad(vals, n_):
        return (list(vals) + [0] * n_)[:n_]

    buf = bytearray(b'NPMWASM01')
    buf += struct.pack('<I', 1)
    buf += struct.pack('<IIIII', n, N_STACK, N_LOCALS, N_GLOBALS, MEM_WORDS)
    buf += struct.pack('<I', len(code))
    buf += code
    buf += struct.pack('<Q', total_gas)
    for v in pad([], N_STACK):
        buf += struct.pack('<Q', v)
    for v in pad(st.locals_ if st.steps else prog.get('locals', []) and [0] * len(prog.get('locals', [])), N_LOCALS):
        buf += struct.pack('<Q', v)
    for v in pad(st.globals_, N_GLOBALS):
        buf += struct.pack('<Q', v)
    for w in range(MEM_WORDS):
        v = 0
        for k in range(8):
            v |= st.mem.get(8 * w + k, 0) << (8 * k)
        buf += struct.pack('<Q', v)
    for s in st.steps:
        buf += struct.pack('<IIQQQ', s['pc'], s['tag'], s['a'], s['b'], s['out'])
        buf += struct.pack('<I', len(s['stack']))
        for v in pad(s['stack'], N_STACK):
            buf += struct.pack('<Q', v)
        for v in pad(s['locals'], N_LOCALS):
            buf += struct.pack('<Q', v)
    for v in pad(st.stack, N_STACK):
        buf += struct.pack('<Q', v)
    for v in pad(st.locals_, N_LOCALS):
        buf += struct.pack('<Q', v)
    for v in pad(st.globals_, N_GLOBALS):
        buf += struct.pack('<Q', v)
    res = result if result is not None else 0
    buf += struct.pack('<QI', res, kind)
    digest = hashlib.sha256(bytes(buf)).digest()
    buf += digest
    Path(out_path).write_bytes(bytes(buf))
    Path(str(out_path) + '.trace.json').write_text(json.dumps({
        'name': prog.get('name'), 'n_steps': n, 'total_gas': total_gas,
        'result': result, 'result_kind': kind, 'steps': st.steps,
    }, indent=1))
    return n, len(buf), result, kind
