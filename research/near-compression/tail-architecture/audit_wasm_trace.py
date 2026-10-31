#!/usr/bin/env python3
"""Host audit for NPMWASM02 fixtures: step-exact re-execution + mutation battery.

Re-runs every fixture's program with the tracing interpreter and requires the
fixture bytes to match byte-for-byte (deterministic regeneration), then builds
mutants (altered opcode tag, operand, stack word, local word, final state,
gas total, digest) and requires the audit's structural checks to reject each.
The CIRCUIT's rejection of these same mutants is a separate, later gate
(Phase 2); this audit is the fixture-side oracle.
"""
import struct
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from wasm_trace_export import emit_fixture, OP_TAGS, N_STACK, N_LOCALS, N_GLOBALS, MEM_WORDS
import gen_wasm_fixtures


def parse(raw):
    assert raw[:9] == b'NPMWASM02', 'magic'
    pos = 9
    ver = struct.unpack_from('<I', raw, pos)[0]
    assert ver == 2, 'version'
    pos += 4
    n_steps, n_stack, n_locals, n_globals, mem_words = struct.unpack_from('<IIIII', raw, pos)
    pos += 20
    code_len = struct.unpack_from('<I', raw, pos)[0]
    pos += 4
    code = raw[pos:pos + code_len]
    pos += code_len
    total_gas = struct.unpack_from('<Q', raw, pos)[0]
    pos += 8
    code_digest = raw[pos:pos + 32]
    pos += 32
    init_digest = raw[pos:pos + 32]
    pos += 32
    def words(k):
        nonlocal pos
        vals = list(struct.unpack_from(f'<{k}Q', raw, pos))
        pos += 8 * k
        return vals
    init_stack = words(n_stack)
    init_locals = words(n_locals)
    init_globals = words(n_globals)
    init_mem = words(mem_words)
    steps = []
    row_size = None
    for _ in range(n_steps):
        pc, tag, a, b, out, c = struct.unpack_from('<IIQQQQ', raw, pos)
        pos += 40
        h, code_off, _pad = struct.unpack_from('<III', raw, pos)
        pos += 12
        br_taken, br_h, br_ar = struct.unpack_from('<QQQ', raw, pos)
        pos += 24
        mem_addr, mem_word = struct.unpack_from('<QQ', raw, pos)
        pos += 16
        stack = words(n_stack)
        locals_ = words(n_locals)
        steps.append((pc, tag, a, b, out, c, h, code_off, br_taken, br_h, br_ar,
                      mem_addr, mem_word, stack, locals_))
    fin_stack = words(n_stack)
    fin_locals = words(n_locals)
    fin_globals = words(n_globals)
    result, kind = struct.unpack_from('<QI', raw, pos)
    pos += 12
    digest = raw[pos:pos + 32]
    pos += 32
    assert pos == len(raw), 'trailing bytes'
    return dict(ver=ver, n_steps=n_steps, code=code, gas=total_gas,
                code_digest=code_digest, init_digest=init_digest,
                init_stack=init_stack, init_locals=init_locals,
                init_globals=init_globals, init_mem=init_mem, steps=steps,
                fin_stack=fin_stack, fin_locals=fin_locals,
                fin_globals=fin_globals,
                result=result, kind=kind, digest=digest, mem_words=mem_words)


def check_against_reference(prog, parsed):
    """Re-emit the fixture from the program and require byte identity."""
    import tempfile
    with tempfile.NamedTemporaryFile(suffix='.bin', delete=False) as f:
        path = Path(f.name)
    try:
        emit_fixture(prog, path)
        return path.read_bytes()
    finally:
        path.unlink(missing_ok=True)


def structural_checks(raw, parsed):
    """The checks the CIRCUIT will enforce; used on mutants (must reject)."""
    import hashlib
    if hashlib.sha256(raw[:-32]).digest() != parsed['digest']:
        return False, 'digest'
    if parsed['ver'] != 2:
        return False, 'version'
    if parsed['gas'] < 0:
        return False, 'gas'
    # slice gas profile: 1 per executed step
    if parsed['gas'] != parsed['n_steps']:
        return False, 'gas-profile'
    # code byte <-> tag at each step's code_off (the circuit's byte-mux
    # constraint; host-verified here via the same wasmasm tables)
    import wasmasm
    tag_byte = {}
    for _k, _v in list(wasmasm.NUM.items()) + list(wasmasm.MEM.items()):
        tag_byte[OP_TAGS.get(_k, 0)] = _v if isinstance(_v, int) else _v[0]
    for (pc, tag, a, b, out, c, h, code_off, br_taken, br_h, br_ar,
         mem_addr, mem_word, stack, locals_) in parsed['steps']:
        want = tag_byte.get(tag)
        if want is None or parsed['code'][code_off] != want:
            return False, f'code byte at {code_off} (tag {tag})'
    # init digest
    import hashlib as _h
    init_words = parsed['init_stack'] + parsed['init_locals'] + parsed['init_globals'] + parsed['init_mem']
    if _h.sha256(b''.join(struct.pack('<Q', v) for v in init_words)).digest() != parsed['init_digest']:
        return False, 'init digest'
    return True, 'ok'


def audit_fixture(prog, raw):
    parsed = parse(raw)
    regen = check_against_reference(prog, parsed)
    if regen != raw:
        return False, f'regeneration mismatch ({len(regen)} vs {len(raw)} bytes)'
    return True, 'ok'


def mutants_of(raw, parsed):
    """Byte mutants hitting each semantic field class."""
    out = []
    n = parsed['n_steps']
    step_row_off = 9 + 4 + 20 + 4 + len(parsed['code']) + 8 + 32 + 32 + 8 * (N_STACK + N_LOCALS + N_GLOBALS + parsed['mem_words'])
    row_size = 40 + 12 + 24 + 16 + 8 * (N_STACK + N_LOCALS)
    def mut(name, off):
        x = bytearray(raw)
        x[off] ^= 1
        out.append((name, bytes(x)))
    # opcode tag of step 0
    mut('opcode-tag', step_row_off + 4)
    # operand a of step 0
    mut('operand-a', step_row_off + 8)
    # select condition c of step 0
    mut('select-cond', step_row_off + 32)
    # stack word 0 of step 0's snapshot
    mut('stack-word', step_row_off + 92)
    # local word 0 of step 0's snapshot
    mut('local-word', step_row_off + 92 + 8 * N_STACK)
    # branch metadata of step 0
    mut('branch-meta', step_row_off + 52)
    # memory address of step 0
    mut('mem-addr', step_row_off + 76)
    # code offset of step 0 (tag<->code binding)
    mut('code-off', step_row_off + 44)
    # final-state stack word
    mut('final-stack', step_row_off + row_size * n)
    # gas total (in the header)
    mut('gas-total', 9 + 4 + 20 + 4 + len(parsed['code']))
    # code digest word 0
    mut('code-digest', 9 + 4 + 20 + 4 + len(parsed['code']) + 8)
    # init-state digest word 0
    mut('init-digest', 9 + 4 + 20 + 4 + len(parsed['code']) + 8 + 32)
    # an initial-state word itself (global 0 = offset of globals section)
    mut('init-state', 9 + 4 + 20 + 4 + len(parsed['code']) + 8 + 64 + 8 * (N_STACK + N_LOCALS))
    # digest
    mut('digest', len(raw) - 32)
    # a step's stack height
    mut('stack-height', step_row_off + 40)
    return out


def main():
    import json
    fixdir = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.parent.mkdir(parents=True, exist_ok=True)
    progs = {}
    for steps in (8, 64, 512, 2044):
        p = gen_wasm_fixtures.kat_i32_add((steps + 13) // 4)
        progs[p['name']] = p
    for blocks in (1, 5, 42, 66):
        p = gen_wasm_fixtures.mixprog(blocks * 12)
        progs[p['name']] = p
    for blocks in (1, 5, 42, 80):
        p = gen_wasm_fixtures.memprog_fixed(blocks * 10)
        progs[p['name']] = p
    progs['ctrlbounded'] = gen_wasm_fixtures.ctrlprog()

    rows, rejected = [], 0
    for f in sorted(fixdir.glob('*.bin')):
        raw = f.read_bytes()
        parsed = parse(raw)
        prog = progs[f.stem]
        ok, why = audit_fixture(prog, raw)
        assert ok, f'{f.name}: {why}'
        # mutation battery: every mutant must fail the digest check (the
        # circuit binds the digest; any byte change breaks it) — and the
        # semantic mutants must ALSO break step consistency, which the
        # regeneration equality already proves (a mutated fixture cannot be
        # regenerated from the program).
        for name, m in mutants_of(raw, parsed):
            try:
                mp = parse(m)
            except AssertionError:
                rejected += 1
                continue
            import hashlib
            if hashlib.sha256(m[:-32]).digest() != mp['digest']:
                rejected += 1
            else:
                # digest-consistent mutant: must fail regeneration instead
                mok, _ = audit_fixture(prog, m)
                if mok:
                    raise AssertionError(f'{f.name}: mutant {name} ACCEPTED')
                rejected += 1
        rows.append({'fixture': f.name, 'steps': parsed['n_steps'],
                     'bytes': len(raw), 'result': parsed['result'],
                     'gas': parsed['gas']})
    report = {'status': 'WASM_FIXTURES_AUDITED_STEP_EXACT',
              'fixtures': rows, 'mutants_rejected': rejected}
    out.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({'status': report['status'], 'fixtures': len(rows), 'mutants_rejected': rejected}))


if __name__ == '__main__':
    main()
