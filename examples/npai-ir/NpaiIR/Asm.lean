import NpaiIR.Basic

/-!
# NpaiIR.Asm — terse notation for writing `Stmt` programs

Every form expands to the plain `Stmt.op (Instr.…)` term, so proofs see
ordinary syntax trees.
-/

namespace NpaiIR

open ArenaCore Interp

syntax "CST " term:max term:max : term
syntax "MOV " term:max term:max : term
syntax "ADD " term:max term:max term:max : term
syntax "SUB " term:max term:max term:max : term
syntax "MUL " term:max term:max term:max : term
syntax "AND " term:max term:max term:max : term
syntax "OR " term:max term:max term:max : term
syntax "XOR " term:max term:max term:max : term
syntax "SHL " term:max term:max term:max : term
syntax "SHR " term:max term:max term:max : term
syntax "EQ " term:max term:max term:max : term
syntax "LTU " term:max term:max term:max : term
syntax "ADDI " term:max term:max term:max : term
syntax "LD8 " term:max term:max : term
syntax "ST8 " term:max term:max : term
syntax "SHA " term:max term:max term:max : term
syntax "MEMEQ " term:max term:max term:max term:max : term
syntax "TLEN " term:max term:max : term
syntax "TCOPY " term:max term:max term:max term:max : term

macro_rules
  | `(CST $a $v) => `(Stmt.op (Instr.const $a $v))
  | `(MOV $a $b) => `(Stmt.op (Instr.mov $a $b))
  | `(ADD $a $b $c) => `(Stmt.op (Instr.bin BinOp.add $a $b $c))
  | `(SUB $a $b $c) => `(Stmt.op (Instr.bin BinOp.sub $a $b $c))
  | `(MUL $a $b $c) => `(Stmt.op (Instr.bin BinOp.mul $a $b $c))
  | `(AND $a $b $c) => `(Stmt.op (Instr.bin BinOp.and $a $b $c))
  | `(OR $a $b $c) => `(Stmt.op (Instr.bin BinOp.or $a $b $c))
  | `(XOR $a $b $c) => `(Stmt.op (Instr.bin BinOp.xor $a $b $c))
  | `(SHL $a $b $c) => `(Stmt.op (Instr.bin BinOp.shl $a $b $c))
  | `(SHR $a $b $c) => `(Stmt.op (Instr.bin BinOp.shr $a $b $c))
  | `(EQ $a $b $c) => `(Stmt.op (Instr.bin BinOp.eq $a $b $c))
  | `(LTU $a $b $c) => `(Stmt.op (Instr.bin BinOp.ltu $a $b $c))
  | `(ADDI $a $b $v) => `(Stmt.op (Instr.addi $a $b $v))
  | `(LD8 $a $b) => `(Stmt.op (Instr.ld8 $a $b))
  | `(ST8 $a $b) => `(Stmt.op (Instr.st8 $a $b))
  | `(SHA $a $b $c) => `(Stmt.op (Instr.sha256 $a $b $c))
  | `(MEMEQ $a $b $c $d) => `(Stmt.op (Instr.memeq $a $b $c $d))
  | `(TLEN $a $t) => `(Stmt.op (Instr.tlen $a $t))
  | `(TCOPY $a $b $c $t) => `(Stmt.op (Instr.tcopy $a $b $c $t))

end NpaiIR
