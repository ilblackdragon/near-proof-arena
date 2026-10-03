import ReexecNpai.Spec.RecAux19
import NpaiIR.Lib.NumSpec

/-!
# Record parse: branch records, bytecode chunks before the slot loop
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

def brL1 : List Stmt := [CST 1 0, CST 2 0, CST 3 5, EQ 3 0 3,
  .ite 3 (seqs [need 10 4 9, ld32 2 10, ADDI 10 10 4, MOV 1 10, ADD 10 10 2, le 10 9]) nop,
  ADD 5 5 2, wField 20 1]
def brL2 : List Stmt := [need 10 2 9, ld16 3 10, ADDI 10 10 2, wField 0 10, ldCell 2 C_KC, wField 12 2,
  CST 6 4, EQ 6 0 6, need 10 1 9, LD8 2 10,
  .ite 6 (seqs [CST 11 1, eqc 2 11, CST 0 1]) (seqs [CST 11 2, eqc 2 11, CST 0 37])]
def brL3 : Stmt := .ite 1 (seqs [ADDI 2 10 1, CST 11 4, SUB 11 1 11, CST 12 4, MEMEQ 13 2 11 12, assert 13,
    ADDI 2 10 5, CST 11 D_ZERO, CST 12 32, MEMEQ 13 2 11 12, assert 13]) nop
def brL4a : List Stmt := [ADD 2 10 0, need 2 2 9, ld16 1 2, AND 6 3 1, eqc 6 3]
def brL4b : List Stmt := [CST 11 5, SHL 11 6 11, ADD 0 0 11, ADDI 0 0 10,
  wField 4 0, ADD 5 5 0,
  ADD 11 10 0, le 11 9,
  CST 11 5, SHL 11 6 11, ADD 2 2 11, ADDI 2 2 2,
  ADD 10 10 0,
  CST 11 16, SHL 11 3 11, ADD 1 1 11,
  ldCell 3 C_KC,
  CST 6 16]
def brBody : Stmt := seqs [
    SUB 6 6 15,
    SHR 11 1 6, AND 11 11 15,
    .ite 11 (seqs [
      CST 11 32, SUB 2 2 11,
      ADDI 11 6 16, SHR 11 1 11, AND 11 11 15,
      .ite 11 (seqs [
        CST 11 D_ZERO, CST 12 32, MEMEQ 13 2 11 12, assert 13,
        CST 11 1, le 11 7, SUB 7 7 15,
        CST 4 4, MUL 4 7 4, ADDI 4 4 STK, ld32 0 4,
        CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 8), st32 4 2,
        CST 4 4, MUL 4 3 4, ADDI 4 4 KL, st32 4 0, ADDI 3 3 1]) nop]) nop]
def brL5 : List Stmt := [stCell C_KC 3, MOV 0 8, wField 16 0]

theorem pBranch_split : pBranch = seqs (brL1 ++ brL2 ++ [brL3] ++ brL4a ++ [popc16 6 1 4 11 12] ++ brL4b ++
    [.loop 6 brBody] ++ brL5) := rfl

theorem evAndLt (x y : Nat) (h : x < 65536) : BinOp.and.eval x y = x &&& y := by
  simp only [BinOp.eval]
  apply Nat.mod_eq_of_lt
  have := Nat.and_le_left (n := x) (m := y)
  unfold wordMod; omega

theorem popcN_eq : ∀ n x, popcN n x = popc n x
  | 0, _ => rfl
  | n + 1, x => by simp only [popcN, popc, popcN_eq n]

section
variable {pub cb pb : Bytes}

set_option maxHeartbeats 4000000 in
theorem brL1_val_wp {m : M} {q E e rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = 5) (h10 : m.regs 10 = q) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E) (hq : q ≤ E)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h5 : m.regs 5 = rv) (hrv : rv < 4294967296) :
    wp P (Inp pub cb pb) (seqs brL1) m (fun m' => q + 4 ≤ E ∧ q + 4 + rd32 m q ≤ E ∧
      m'.mem = wr4 m.mem (AR + 24 * e + 20) (q + 4) ∧ m'.regs 1 = q + 4 ∧ m'.regs 2 = rd32 m q ∧
      m'.regs 10 = q + 4 + rd32 m q ∧ m'.regs 5 = rv + rd32 m q ∧ m'.regs 0 = 5 ∧ m'.regs 7 = m.regs 7 ∧
      m'.regs 8 = e ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [NCAP] at he
  simp only [brL1, wField, rd32]
  rec_auto [hk1, hk8, h0, h10, h9, h8, h5]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 20) = e * 24 + 117020 by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL1_val_twp {m : M} {q E e rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = 5) (h10 : m.regs 10 = q) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h5 : m.regs 5 = rv) (hrv : rv < 4294967296)
    (hq1 : q + 4 ≤ E) (hq2 : q + 4 + rd32 m q ≤ E) :
    twp P (Inp pub cb pb) (seqs brL1) m (fun m' c =>
      m'.mem = wr4 m.mem (AR + 24 * e + 20) (q + 4) ∧ m'.regs 1 = q + 4 ∧ m'.regs 2 = rd32 m q ∧
      m'.regs 10 = q + 4 + rd32 m q ∧ m'.regs 5 = rv + rd32 m q ∧ m'.regs 0 = 5 ∧ m'.regs 7 = m.regs 7 ∧
      m'.regs 8 = e ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 80) := by
  simp only [NCAP] at he
  simp only [brL1, wField, rd32, Nat.add_assoc] at hq2 ⊢
  rec_auto [hk1, hk8, h0, h10, h9, h8, h5, hq2]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 20) = e * 24 + 117020 by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL1_nov_twp {m : M} {k q e rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = k) (hk : k ≠ 5) (h10 : m.regs 10 = q)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h5 : m.regs 5 = rv) (hrv : rv < 4294967296) :
    twp P (Inp pub cb pb) (seqs brL1) m (fun m' c =>
      m'.mem = wr4 m.mem (AR + 24 * e + 20) 0 ∧ m'.regs 1 = 0 ∧ m'.regs 2 = 0 ∧
      m'.regs 10 = q ∧ m'.regs 5 = rv ∧ m'.regs 0 = k ∧ m'.regs 7 = m.regs 7 ∧
      m'.regs 8 = e ∧ m'.regs 9 = m.regs 9 ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 80) := by
  simp only [NCAP] at he
  simp only [brL1, wField]
  rec_auto [hk1, hk8, h0, h10, h8, h5, hk]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 20) = e * 24 + 117020 by omega]; done)

set_option maxHeartbeats 4000000 in
/-- After the tag: `r0` is the header length. -/
theorem brL2_wp {m : M} {k q E e : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = k) (h10 : m.regs 10 = q) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E) (hq : q ≤ E)
    (h8 : m.regs 8 = e) (he : e < NCAP) (hqa : AR + 24 * NCAP ≤ q) :
    wp P (Inp pub cb pb) (seqs brL2) m (fun m' => q + 3 ≤ E ∧
      (m.mem (q + 2)).toNat = (if k = 4 then 1 else 2) ∧
      m'.mem = wr4 (wr4 m.mem (AR + 24 * e) (q + 2)) (AR + 24 * e + 12) (rd32 m C_KC) ∧
      m'.regs 3 = (readMem m.mem q 2).leToNat ∧ m'.regs 10 = q + 2 ∧ m'.regs 0 = (if k = 4 then 1 else 37) ∧
      m'.regs 1 = m.regs 1 ∧ m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧ m'.regs 9 = E ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [NCAP, AR] at he hqa
  simp only [brL2, wField, ldCell, rd32]
  rec_auto [hk1, hk8, h0, h10, h9, h8, readMem_writeMem_disjoint, writeMem_apply_out]
  refine ⟨fun hk4 ht => ?_, fun hk4 ht => ?_⟩ <;>
    simp only [hk4, ↓reduceIte, ht, Nat.reduceEqDiff, eq_self_iff_true] <;>
    (repeat' apply And.intro) <;>
    first | assumption | omega | rfl |
      (simp only [wr4, show 117000 + 24 * e = e * 24 + 117000 by omega,
        show 117000 + (24 * e + 12) = e * 24 + 117012 by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL2_twp {m : M} {k q E e : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = k) (h10 : m.regs 10 = q) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E)
    (h8 : m.regs 8 = e) (he : e < NCAP) (hqa : AR + 24 * NCAP ≤ q) (hq : q + 3 ≤ E)
    (ht : (m.mem (q + 2)).toNat = (if k = 4 then 1 else 2)) :
    twp P (Inp pub cb pb) (seqs brL2) m (fun m' c =>
      m'.mem = wr4 (wr4 m.mem (AR + 24 * e) (q + 2)) (AR + 24 * e + 12) (rd32 m C_KC) ∧
      m'.regs 3 = (readMem m.mem q 2).leToNat ∧ m'.regs 10 = q + 2 ∧ m'.regs 0 = (if k = 4 then 1 else 37) ∧
      m'.regs 1 = m.regs 1 ∧ m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧ m'.regs 9 = E ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 100) := by
  simp only [NCAP, AR] at he hqa
  simp only [brL2, wField, ldCell, rd32]
  by_cases hk4 : k = 4
  · subst hk4
    simp only [↓reduceIte] at ht ⊢
    rec_auto [hk1, hk8, h0, h10, h9, h8, readMem_writeMem_disjoint, writeMem_apply_out, ht]
    repeat' apply And.intro
    all_goals first | assumption | omega | rfl |
      (simp only [wr4, show 117000 + 24 * e = e * 24 + 117000 by omega,
        show 117000 + (24 * e + 12) = e * 24 + 117012 by omega]; done)
  · simp only [hk4, ↓reduceIte] at ht ⊢
    rec_auto [hk1, hk8, h0, h10, h9, h8, readMem_writeMem_disjoint, writeMem_apply_out, ht, hk4]
    repeat' apply And.intro
    all_goals first | assumption | omega | rfl |
      (simp only [wr4, show 117000 + 24 * e = e * 24 + 117000 by omega,
        show 117000 + (24 * e + 12) = e * 24 + 117012 by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL3_wp {m : M} {a pr : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h1 : m.regs 1 = a) (h10 : m.regs 10 = pr) (hpr : pr ≤ 13844304) (ha : a = 0 ∨ (4 ≤ a ∧ a ≤ 13844304)) :
    wp P (Inp pub cb pb) brL3 m (fun m' => (a ≠ 0 → readMem m.mem (pr + 1) 4 = readMem m.mem (a - 4) 4 ∧
      readMem m.mem (pr + 5) 32 = readMem m.mem 136 32) ∧ m'.mem = m.mem ∧
      (∀ j, j ≠ 2 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j)) := by
  simp only [brL3]
  rec_auto [hk1, hk8, h1, h10]
  refine ⟨fun h0 h1 => absurd h0 h1, fun ha0 _ _ c1 _ c2 => ⟨fun _ => ⟨?_, c2⟩,
    fun j h2 h11 h12 h13 => by simp [h2, h11, h12, h13]⟩⟩
  have hsub : BinOp.sub.eval a 4 = a - 4 := by simp only [BinOp.eval, wordMod]; omega
  rw [c1, hsub]

set_option maxHeartbeats 4000000 in
theorem brL3_twp {m : M} {a pr : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h1 : m.regs 1 = a) (h10 : m.regs 10 = pr) (hpr : a ≠ 0 → pr + 37 ≤ 13844304)
    (ha : a = 0 ∨ (4 ≤ a ∧ a ≤ 13844304)) (hc : a ≠ 0 → readMem m.mem (pr + 1) 4 = readMem m.mem (a - 4) 4 ∧
      readMem m.mem (pr + 5) 32 = readMem m.mem 136 32) :
    twp P (Inp pub cb pb) brL3 m (fun m' c => m'.mem = m.mem ∧
      (∀ j, j ≠ 2 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 40) := by
  simp only [brL3]
  by_cases ha0 : a = 0
  · subst ha0
    rec_auto [hk1, hk8, h1, h10]
    all_goals first | omega | (intro j h2 h11 h12 h13; simp [h2, h11, h12, h13])
  · obtain ⟨c1, c2⟩ := hc ha0
    have hpr := hpr ha0
    have hsub : BinOp.sub.eval a 4 = a - 4 := by simp only [BinOp.eval, wordMod]; omega
    rec_auto [hk1, hk8, h1, h10, ha0, hsub, c1, c2]
    repeat' apply And.intro
    all_goals first | omega | (intro j h2 h11 h12 h13; simp [h2, h11, h12, h13])

set_option maxHeartbeats 4000000 in
theorem brL4a_wp {m : M} {R E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 10 + m.regs 0 = R) (hR : R < 4294967296) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E)
    (h3 : m.regs 3 < 65536) :
    wp P (Inp pub cb pb) (seqs brL4a) m (fun m' => R + 2 ≤ E ∧
      (m.regs 3 &&& (readMem m.mem R 2).leToNat) = m.regs 3 ∧ m'.mem = m.mem ∧
      m'.regs 1 = (readMem m.mem R 2).leToNat ∧ m'.regs 2 = R ∧
      (∀ j, j ≠ 1 → j ≠ 2 → j ≠ 6 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j)) := by
  simp only [brL4a]
  rec_auto [hk1, hk8, h0, h9, evAndLt _ _ h3]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (intro j h1 h2 h6 h11 h12 h13; simp [h1, h2, h6, h11, h12, h13])

end

end ReexecNpai
