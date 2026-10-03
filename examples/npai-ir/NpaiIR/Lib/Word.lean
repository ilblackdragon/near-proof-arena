import NpaiIR.Exe
import NpaiIR.Lib.Num

/-!
# NpaiIR.Lib.Word — straight-line little-endian loads and stores

`ld32 d a` / `ld16` / `ld64` and `st32 a v` are loop-free, so code using them
can be evaluated symbolically with `exe` (`ld32_exe`, `st32_exe`, …).
Temporaries: `r12` (loads), `r12 r13` (stores).
-/

set_option maxRecDepth 8000

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-- Load bytes `n-1, …, 0` (high to low) into `d`: `d := leToNat mem[a, a+n)`. -/
def ldwI (d a : Nat) : Nat → List Instr
  | 0 => [.const d 0]
  | n + 1 => [.addi 12 a n, .ld8 d 12] ++
      ((List.range n).reverse.flatMap fun i => [.bin .shl d d K8, .addi 12 a i, .ld8 12 12, .bin .add d d 12])

def ld32 (d a : Nat) : Stmt := block (ldwI d a 4)
def ld16 (d a : Nat) : Stmt := block (ldwI d a 2)
def ld64 (d a : Nat) : Stmt := block (ldwI d a 8)

/-- Store the low 4 bytes of `regs v` at `regs a` (temps `r12 r13`). -/
def st32 (a v : Nat) : Stmt := block [.mov 12 v, .st8 a 12,
  .bin .shr 12 12 K8, .addi 13 a 1, .st8 13 12,
  .bin .shr 12 12 K8, .addi 13 a 2, .st8 13 12,
  .bin .shr 12 12 K8, .addi 13 a 3, .st8 13 12]

theorem block_loopFree (is : List Instr) : (block is).loopFree := by
  induction is with
  | nil => trivial
  | cons i is ih => cases is with
    | nil => trivial
    | cons j js => exact ⟨trivial, ih⟩

theorem exe_block {is : List Instr} (h : allOk is) (m : M) : exe p inp (block is) m = runSL p inp is m := by
  cases hr : runSL p inp is m with
  | none =>
    cases he : exe p inp (block is) m with
    | none => rfl
    | some r =>
      obtain ⟨m', c⟩ := r
      have := (ev_block h).1 (exe_sound he)
      rw [hr] at this; cases this
  | some r =>
    obtain ⟨m', c⟩ := r
    exact exe_complete (block_loopFree is) ((ev_block h).2 hr)

theorem readMem_four (M0 : Nat → UInt8) (A : Nat) :
    readMem M0 A 4 = [M0 A, M0 (A + 1), M0 (A + 2), M0 (A + 3)] := by
  simp [readMem_succ, readMem_zero, Nat.add_assoc]

theorem readMem_two (M0 : Nat → UInt8) (A : Nat) : readMem M0 A 2 = [M0 A, M0 (A + 1)] := by
  simp [readMem_succ, readMem_zero]

theorem readMem_eight (M0 : Nat → UInt8) (A : Nat) :
    readMem M0 A 8 = [M0 A, M0 (A + 1), M0 (A + 2), M0 (A + 3), M0 (A + 4), M0 (A + 5), M0 (A + 6),
      M0 (A + 7)] := by
  simp [readMem_succ, readMem_zero, Nat.add_assoc]

theorem ld32_exe {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M} (hk : m.regs 14 = 8)
    (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296) :
    exe p inp (ld32 d a) m = some (⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 4)), m.mem⟩, 14) := by
  have h0 := byte_lt (m.mem (m.regs a))
  have h1 := byte_lt (m.mem (m.regs a + 1))
  have h2 := byte_lt (m.mem (m.regs a + 2))
  have h3 := byte_lt (m.mem (m.regs a + 3))
  rw [ld32]
  simp only [ldwI, List.range_succ, List.range_zero, List.reverse_cons, List.reverse_nil,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
  rw [exe_block (by simp [allOk, okInstr])]
  npai_sym [hk, Ne.symm hda, Ne.symm hd, Ne.symm ha, hda, hd, ha, hd14, Ne.symm hd14]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  funext j
  simp only [setReg_apply, readMem_four, Bytes.leToNat]
  by_cases hj : j = d
  · subst hj; simp; omega
  · by_cases hj2 : j = 12
    · simp [hj2, Ne.symm hd]
    · simp [hj, hj2]

theorem ld16_exe {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M} (hk : m.regs 14 = 8)
    (hb : m.regs a + 2 ≤ p.memSize) (hw : p.memSize < 4294967296) :
    exe p inp (ld16 d a) m = some (⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 2)), m.mem⟩, 6) := by
  have h0 := byte_lt (m.mem (m.regs a))
  have h1 := byte_lt (m.mem (m.regs a + 1))
  rw [ld16]
  simp only [ldwI, List.range_succ, List.range_zero, List.reverse_cons, List.reverse_nil,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
  rw [exe_block (by simp [allOk, okInstr])]
  npai_sym [hk, Ne.symm hda, Ne.symm hd, Ne.symm ha, hda, hd, ha, hd14, Ne.symm hd14]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  funext j
  simp only [setReg_apply, readMem_two, Bytes.leToNat]
  by_cases hj : j = d
  · subst hj; simp; omega
  · by_cases hj2 : j = 12
    · simp [hj2, Ne.symm hd]
    · simp [hj, hj2]

theorem ld64_exe {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 8 ≤ p.memSize) (hw : p.memSize < 4294967296) :
    exe p inp (ld64 d a) m = some (⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 8)), m.mem⟩, 30) := by
  have h0 := byte_lt (m.mem (m.regs a))
  have h1 := byte_lt (m.mem (m.regs a + 1))
  have h2 := byte_lt (m.mem (m.regs a + 2))
  have h3 := byte_lt (m.mem (m.regs a + 3))
  have h4 := byte_lt (m.mem (m.regs a + 4))
  have h5 := byte_lt (m.mem (m.regs a + 5))
  have h6 := byte_lt (m.mem (m.regs a + 6))
  have h7 := byte_lt (m.mem (m.regs a + 7))
  rw [ld64]
  simp only [ldwI, List.range_succ, List.range_zero, List.reverse_cons, List.reverse_nil,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
  rw [exe_block (by simp [allOk, okInstr])]
  npai_sym [hk, Ne.symm hda, Ne.symm hd, Ne.symm ha, hda, hd, ha, hd14, Ne.symm hd14]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  funext j
  simp only [setReg_apply, readMem_eight, Bytes.leToNat]
  by_cases hj : j = d
  · subst hj; simp; omega
  · by_cases hj2 : j = 12
    · simp [hj2, Ne.symm hd]
    · simp [hj, hj2]

theorem leN_four (V : Nat) : Bytes.leN 4 V = [UInt8.ofNat (V % 256), UInt8.ofNat (V / 256 % 256),
    UInt8.ofNat (V / 256 / 256 % 256), UInt8.ofNat (V / 256 / 256 / 256 % 256)] := rfl

theorem writeMem_four (M0 : Nat → UInt8) (A : Nat) (b0 b1 b2 b3 : UInt8) :
    writeMem (writeMem (writeMem (writeMem M0 A 1 [b0]) (A + 1) 1 [b1]) (A + 2) 1 [b2]) (A + 3) 1 [b3] =
      writeMem M0 A 4 [b0, b1, b2, b3] := by
  have e1 := writeMem_snoc M0 A 1 [b0] rfl b1
  have e2 := writeMem_snoc M0 A 2 [b0, b1] rfl b2
  have e3 := writeMem_snoc M0 A 3 [b0, b1, b2] rfl b3
  simp only [List.cons_append, List.nil_append] at e1 e2 e3
  rw [e1, e2, e3]

theorem st32_exe {a v : Nat} (ha : a ≠ 12) (ha13 : a ≠ 13) {m : M} (hk : m.regs 14 = 8)
    (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296)
    (hv : m.regs v < 18446744073709551616) :
    exe p inp (st32 a v) m = some (⟨setReg (setReg m.regs 12 (m.regs v / 256 / 256 / 256)) 13
      (m.regs a + 3), writeMem m.mem (m.regs a) 4 (Bytes.leN 4 (m.regs v))⟩, 11) := by
  rw [st32, exe_block (by simp [allOk, okInstr])]
  npai_sym [hk, ha, ha13, Ne.symm ha, Ne.symm ha13]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true, M.mk.injEq]
  constructor
  · funext j
    simp only [setReg_apply]
    by_cases hj : j = 13
    · simp [hj]
    · by_cases hj2 : j = 12
      · simp [hj2]
      · simp [hj, hj2]
  · rw [writeMem_four, leN_four]

end NpaiIR
