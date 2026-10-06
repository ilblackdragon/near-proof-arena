"""D15 probe: what `call_indirect` pops in the operand-stack maximum (random seed 94 case #433).
`main` = push the callee's params + table index, call_indirect (never reached: the recursion
comes first), then push 8 more bytes to expose the height left behind. Recursion depth = stack budget
/ (op_stack_max + frame), so the burnt gas measures op_stack_max."""
from probe import *
I32, I64 = 0x7F, 0x7E
def mod(params, results, extra):
    m = base_module()
    m.tables = [(0x70, 1, None)]
    t = m.type(params, results)
    push = b"".join((b"\x41\x00" if p == I32 else b"\x42\x00") for p in params)
    body = b"\x10\x01" + push + b"\x41\x00" + b"\x11" + uleb(t) + b"\x00" + extra
    m.func([], [], [], body)
    m.exports.append(("main", 0, 1))
    return m.encode().hex()
E = b"\x42\x00\x42\x00\x1a\x1a"   # push 16 bytes on top, then drop
c = []
for params in ([], [I32], [I64], [I32, I32], [I64, I32], [I32, I64], [I64, I64], [I64, I64, I64], [I32] * 4):
    for results in ([], [I32], [I64]):
        drops = b"\x1a" * len(results)
        E2 = drops + E
        c.append((f"{''.join('l' if p == I64 else 'i' for p in params) or '-'}->{''.join('l' if r == I64 else 'i' for r in results) or '-'}",
                  f"300000000000000 {mod(params, results, E2)}"))
# results on top of the leftover, and the leftover vs a later peak
for params, results in (([I64, I32], [I64]), ([I64, I32], [I32]), ([I64], [I64]), ([I32, I64, I64], [I32])):
    c.append((f"keep result {params}->{results}", f"300000000000000 {mod(params, results, b'\x42\x00\x1a' + b'\x1a' * len(results))}"))
cmp(c)
