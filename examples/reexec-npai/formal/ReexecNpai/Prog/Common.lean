import NpaiIR.Asm
import ReexecNpai.Layout

/-!
# Shared macros of the verifier program

Register conventions for the whole program: `r15 = 1`, `r14 = 8` (set once),
`r11 r12 r13` are macro temporaries (clobbered by `ld32`, `st32`, `need`, …);
phases use `r0 … r10`.
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

/-- `d := u32 LE at regs a` (clobbers `d r12 r13`). -/
def ld32 (d a : Nat) : Stmt := ldLE d a 12 13 4
def ld16 (d a : Nat) : Stmt := ldLE d a 12 13 2
def ld64 (d a : Nat) : Stmt := ldLE d a 12 13 8
/-- `mem[regs a, +4) := u32 LE of regs v` (clobbers `r11 r12 r13`). -/
def st32 (a v : Nat) : Stmt := stLE a v 4 11 12 13

/-- Continue iff `regs p + k ≤ regs e` (clobbers `r12 r13`). -/
def need (p k e : Nat) : Stmt := .seq (ADDI 12 p k) (chkLe 12 e 13)

/-- Continue iff `regs a ≤ regs b` / `<` / `=` (clobbers `r13`). -/
def le (a b : Nat) : Stmt := chkLe a b 13
def lt (a b : Nat) : Stmt := chkLt a b 13
def eqc (a b : Nat) : Stmt := chkEq a b 13

/-- Load a constant ≥ 2^32 from the data segment (8 bytes LE at `addr`;
clobbers `d r11 r12 r13`). -/
def ldConst64 (d addr : Nat) : Stmt := .seq (CST 11 addr) (ld64 d 11)

/-- `r := (regs c - lo) < width` (unsigned range test; clobbers `r` and `tmp`). -/
def inRange (r c lo width tmp : Nat) : Stmt :=
  seqs [CST r lo, SUB r c r, CST tmp width, LTU r r tmp]

/-- `r := isHex(regs c)` (`0-9a-f`; clobbers `r tmp tmp2`). -/
def isHex (r c tmp tmp2 : Nat) : Stmt :=
  seqs [inRange r c 97 6 tmp, inRange tmp c 48 10 tmp2, OR r r tmp]

/-- Arena entry field write: `AR[e = r8].off := regs v` (clobbers `r4 r11 r12 r13`). -/
def wField (off v : Nat) : Stmt := seqs [CST 4 24, MUL 4 8 4, ADDI 4 4 (AR + off), st32 4 v]

/-- `d := cell C` (clobbers `d r11 r12 r13`). -/
def ldCell (d c : Nat) : Stmt := .seq (CST 11 c) (ld32 d 11)
/-- `cell C := regs v` (clobbers `r4 r11 r12 r13`). -/
def stCell (c v : Nat) : Stmt := .seq (CST 4 c) (st32 4 v)

/-- "No entry" marker of the resolved-child field (`≥ NCAP`). -/
def NONE : Nat := 4294967295

end ReexecNpai
