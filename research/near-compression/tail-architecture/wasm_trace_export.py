#!/usr/bin/env python3
"""Trace export for the NPMWASM02 circuit fixtures (LaBRADOR vertical slice).

Re-implements the wasm-base refinterp.py execution loop as a TRACING variant:
same spec-derived semantics (the file imports refinterp's binop and shares no
prover code), but records per-step state. Emits both .trace.json (for the
audit) and the .bin NPMWASM02 fixture (for the circuit).

v2 (NPMWASM02) — replaces v1 after the Phase-2 circuit design review found
v1 could not express the required constraint set: it recorded no select
condition, no load effective address (offset immediates live only in code),
no const immediate, no branch label metadata, and wrote the "initial"
locals/globals/memory from POST-execution state. v2 layout (all LE):

  magic(9) "NPMWASM02" || u32 version(=2)
  || u32 n_steps || u32 n_stack || u32 n_locals || u32 n_globals || u32 mem_words
  || u32 code_len || code bytes (wasmasm.assemble output)
  || u64 total_gas
  || u64 code_digest[4]  (sha256 of the code section bytes; the circuit's
     tight_sha over the committed code words must equal it)
  || u32 init_digest[8]  (sha256 of the initial state words — stack, locals,
     globals, memory in that order; binds the circuit's init witness)
  || INITIAL state (pre-execution): stack u64[n_stack] || locals u64[n_locals]
     || globals u64[n_globals] || memory u64[mem_words]
  || per step: u32 pc || u32 opcode_tag || u64 a || u64 b || u64 out || u64 c
       || u32 stack_height || u32 code_off || u64 br_taken || u64 br_h || u64 br_ar
       || u64 mem_addr || u64 mem_word
       || stack u64[n_stack] || locals u64[n_locals]
  || FINAL state: stack u64[n_stack] || locals u64[n_locals] || globals u64[n_globals]
  || u64 result || u32 result_kind (0=trap/1=value)
  || sha256 over the whole preceding stream (32 bytes)

Step semantics (the circuit's named constraints):
- One row per EXECUTED instruction; pc = index into the flattened list.
- a/b/out: for binops `a OP b` (a = second pop, b = top); eqz: a = operand;
  const: a = the immediate (masked to width); local.get/global.get: a = index,
  out = value; local.set/global.set/tee: a = index, out = value (popped or
  top); drop: out = popped; br_if: a = popped condition; select: a/b = the
  two data values, c = the popped condition, out = chosen value.
- stack_height = height AFTER the step; snapshots above height are zero.
- Branch steps (br always; br_if when taken): br_taken=1, br_h = the label's
  entry height, br_ar = the label arity (0/1 in this interpreter). The
  circuit enforces the move semantics from these; binding br_h/ar to the
  code's label structure is the code-walk follow-up, stated.
- Loads: mem_addr = effective address (base+offset), mem_word = the FULL
  addressed memory word at load time. Stores: mem_addr = effective address,
  mem_word = the full word AFTER the store. The circuit keeps a 256-word
  register bank and binds both against it (read-over-write by construction).
- gas = 1 per executed step (slice profile); total in the header.
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

# 128 u64 words = 1024 B — the WASM_SLICE_DEF.md circuit bound (the def's
# "256-word" wording meant 4-byte words; the corpus uses <= 128 B).
N_STACK, N_LOCALS, N_GLOBALS, MEM_WORDS = 64, 16, 8, 128


class TraceState:
    def __init__(self):
        self.steps = []       # dicts: pc, op, tag, a, b, out, c, gas, mem_addr, mem_word
        self.stack = []       # logical stack (values)
        self.locals_ = []
        self.globals_ = []
        self.mem = {}         # byte address -> byte value


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
    # code_off_at[pc] = MODULE-ABSOLUTE byte offset of instruction pc (the
    # circuit reads each step's opcode byte at this offset from the
    # committed module words — the tag<->code anti-fabrication binding).
    # Base = the position of the body's instruction bytes inside the module
    # (found by exact match; deterministic, so regeneration is identical).
    import wasmasm as _wa
    body_bytes = b''.join(_wa.instr(_i) for _i in body)
    _mod = _wa.assemble({k: v for k, v in prog.items() if k != 'body'} | {'body': prog['body']})
    _base = _mod.find(body_bytes)
    assert _base >= 0, 'body bytes not found in module'
    off = 0
    code_off_at = {}
    for _pc, _i in enumerate(body):
        code_off_at[_pc] = _base + off
        off += len(_wa.instr(_i))
    pc = 0
    cnt = 0
    result = None
    kind = 1

    def record(op, tag, a=0, b=0, out=0, c=0, gas=1, mem_addr=0, mem_word=0):
        st.steps.append({'pc': pc, 'op': op, 'tag': tag, 'a': a, 'b': b,
                         'out': out, 'c': c, 'gas': gas, 'mem_addr': mem_addr,
                         'mem_word': mem_word,
                         'code_off': code_off_at[pc],
                         'stack': list(st.stack), 'locals': list(st.locals_)})

    def mem_word_at(ea):
        """The full 8-byte word containing byte address ea (little-endian)."""
        w = 0
        for k in range(8):
            w |= st.mem.get((ea & ~7) + k, 0) << (8 * k)
        return w

    def do_branch(l):
        nonlocal pc, kind, result
        k, tgt, ar, h = labels[-1 - l]
        vals = st.stack[len(st.stack) - ar:] if ar else []
        del st.stack[h:]
        st.stack.extend(vals)
        if k == 'func':
            result = st.stack[-1] if st.stack else None
            return True, h, ar
        del labels[len(labels) - (l if k == 'loop' else l + 1):]
        pc = tgt
        return False, h, ar

    while True:
        cnt += 1
        if cnt > n_steps_cap:
            raise RuntimeError('step cap exceeded (fixture would overflow the circuit bound)')
        i = body[pc]
        op = i[0]
        if op in ('i32.const', 'i64.const'):
            v = i[1] & (M32 if op[1] == '3' else M64)
            st.stack.append(v)
            record(op, OP_TAGS[op], a=v, out=v)
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
            record(op, OP_TAGS[op], a=a, b=b, out=out, c=c)
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
            record(op, OP_TAGS.get(op, 0), a=base, out=v, mem_addr=ea,
                   mem_word=mem_word_at(ea))
            pc += 1
        elif op in STORES:
            w = STORES[op]
            v = st.stack.pop()
            base = st.stack.pop()
            ea = base + (i[1] if len(i) > 1 else 0)
            for k in range(w):
                st.mem[ea + k] = (v >> (8 * k)) & 0xFF
            record(op, OP_TAGS.get(op, 0), a=base, b=v, out=ea, mem_addr=ea,
                   mem_word=mem_word_at(ea))
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
            # The br row's snapshot is the POST-branch stack (the circuit
            # chains snapshots; br_h/br_ar let it constrain the move).
            bpc = pc
            fin, h, ar = do_branch(i[1])
            st.steps.append({'pc': bpc, 'op': op, 'tag': OP_TAGS[op], 'a': 0, 'b': 0,
                             'out': 0, 'c': 0, 'gas': 1, 'mem_addr': 0, 'mem_word': 0,
                             'br_taken': 1, 'br_h': h, 'br_ar': ar,
                             'code_off': code_off_at[pc],
                             'stack': list(st.stack), 'locals': list(st.locals_)})
            if fin:
                return st, result, 1
        elif op == 'br_if':
            bpc = pc
            c = st.stack.pop()
            fin, h, ar = False, 0, 0
            taken = 0
            if c:
                fin, h, ar = do_branch(i[1])
                taken = 1
            st.steps.append({'pc': bpc, 'op': op, 'tag': OP_TAGS[op], 'a': c, 'b': 0,
                             'out': 0, 'c': 0, 'gas': 1, 'mem_addr': 0, 'mem_word': 0,
                             'br_taken': taken, 'br_h': h, 'br_ar': ar,
                             'code_off': code_off_at[pc],
                             'stack': list(st.stack), 'locals': list(st.locals_)})
            if fin:
                return st, result, 1
            if not taken:
                pc += 1
        elif op == 'return':
            result = st.stack[-1] if st.stack else None
            st.steps.append({'pc': pc, 'op': op, 'tag': OP_TAGS[op], 'a': 0, 'b': 0,
                             'out': 0, 'c': 0, 'gas': 1, 'mem_addr': 0, 'mem_word': 0,
                             'br_taken': 0, 'br_h': 0, 'br_ar': 0,
                             'code_off': code_off_at[pc],
                             'stack': list(st.stack), 'locals': list(st.locals_)})
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
    """Run traced, then write the NPMWASM02 binary + .trace.json."""
    try:
        st, result, kind = run_traced(prog, n_steps_cap)
    except Trap:
        # traps are outside the first rung (no div in circuit); record honestly
        raise
    n = len(st.steps)
    sys.path.insert(0, str(WASMBASE))
    import wasmasm
    code = wasmasm.assemble({k: v for k, v in prog.items() if k != 'body'} | {'body': prog['body']})
    total_gas = sum(s['gas'] for s in st.steps)

    def pad(vals, n_):
        return (list(vals) + [0] * n_)[:n_]

    buf = bytearray(b'NPMWASM02')
    buf += struct.pack('<I', 2)
    buf += struct.pack('<IIIII', n, N_STACK, N_LOCALS, N_GLOBALS, MEM_WORDS)
    buf += struct.pack('<I', len(code))
    buf += code
    buf += struct.pack('<Q', total_gas)
    # code digest: sha256 over the code section bytes (public; the circuit's
    # tight_sha over the committed code words must equal it)
    cd = hashlib.sha256(bytes(code)).digest()
    buf += cd
    # INITIAL state — pre-execution (v1 wrongly emitted post-run state here):
    # stack empty, locals zero, globals = program inits, memory zero.
    init_globals = [gv & (M32 if gt == 'i32' else M64) for gt, _, gv in prog.get('globals', [])]
    # init-state digest: sha256 over the initial words (stack, locals,
    # globals, memory) — binds the circuit's init witness words. Uses the
    # same padded arrays as the sections below; written in the header
    # right after the code digest (the pinned v2 layout).
    init_words = (pad([], N_STACK)
                  + pad([0] * max(len(prog.get('locals', [])), 1), N_LOCALS)
                  + pad(init_globals, N_GLOBALS)
                  + [0] * MEM_WORDS)
    buf += hashlib.sha256(b''.join(struct.pack('<Q', v) for v in init_words)).digest()
    for v in pad([], N_STACK):
        buf += struct.pack('<Q', v)
    for v in pad([0] * max(len(prog.get('locals', [])), 1), N_LOCALS):
        buf += struct.pack('<Q', v)
    for v in pad(init_globals, N_GLOBALS):
        buf += struct.pack('<Q', v)
    for w in range(MEM_WORDS):
        buf += struct.pack('<Q', 0)
    for s in st.steps:
        buf += struct.pack('<IIQQQQ', s['pc'], s['tag'], s['a'], s['b'], s['out'], s['c'])
        buf += struct.pack('<I', len(s['stack']))
        buf += struct.pack('<II', s['code_off'], 0)
        buf += struct.pack('<QQQ', s.get('br_taken', 0), s.get('br_h', 0), s.get('br_ar', 0))
        buf += struct.pack('<QQ', s.get('mem_addr', 0), s.get('mem_word', 0))
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
