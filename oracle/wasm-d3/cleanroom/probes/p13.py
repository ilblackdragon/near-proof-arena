"""D15 probe: operand-stack maximum around live `if` (random seed 94 case #433).
Each module's `main` recurses into itself after a prefix, so the stack budget (and so the gas burnt)
measures main's op_stack_max."""
from probe import *
I32c = lambda v: b"\x41" + sleb(v)
I64c = lambda v: b"\x42" + sleb(v)
DROP = b"\x1a"; END = b"\x0b"; ELSE = b"\x05"
IF = b"\x04\x40"; IFI32 = b"\x04\x7f"; IFI64 = b"\x04\x7e"
def mod(prefix):
    m = base_module()
    m.func([], [], [], prefix + b"\x10\x01")
    m.exports.append(("main", 0, 1))
    return m.encode().hex()
P = {
  "baseline i64 drop":            I64c(0) + DROP,
  "if: i64 inside then":          I32c(1) + IF + I64c(0) + DROP + END,
  "if: i64 inside else":          I32c(1) + IF + ELSE + I64c(0) + DROP + END,
  "if0: i64 inside else (taken)": I32c(0) + IF + ELSE + I64c(0) + DROP + END,
  "if(result i64) then/else":     I32c(1) + IFI64 + I64c(0) + ELSE + I64c(0) + END + DROP,
  "if(result i64) after end":     I32c(1) + IFI64 + I64c(0) + ELSE + I64c(0) + END + I64c(0) + DROP + DROP,
  "if(result i32), i32 inside then": I32c(1) + IFI32 + I32c(0) + I32c(0) + DROP + ELSE + I32c(0) + END + DROP,
  "nested if in else":            I32c(1) + IFI64 + I64c(0) + ELSE + I32c(1) + IFI32 + I32c(5) + I32c(6) + DROP + ELSE + I32c(7) + END + DROP + I64c(0) + END + DROP,
  "nested if in then":            I32c(1) + IF + I32c(1) + IF + I64c(0) + DROP + END + END,
  "block with i64":               b"\x02\x40" + I64c(0) + DROP + END,
  "i64 under if":                 I64c(0) + I32c(1) + IF + I64c(0) + DROP + END + DROP,
}
cmp([(k, f"300000000000000 {mod(v)}") for k, v in P.items()])
