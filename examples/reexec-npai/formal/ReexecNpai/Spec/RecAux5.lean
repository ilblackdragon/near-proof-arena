import ReexecNpai.Spec.RecAux4

/-!
# Record parse: leaf records, bytecode
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

macro "close_conj" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl | (simp only [Nat.add_sub_cancel] at *; assumption)))

def leafChkL : List Stmt := [CST 1 0, CST 2 0,
  CST 3 1, EQ 3 0 3,
  .ite 3 (seqs [need 10 4 9, ld32 2 10, ADDI 10 10 4, MOV 1 10, ADD 10 10 2, le 10 9]) nop,
  need 10 5 9, LD8 3 10, assertZ 3,
  ADDI 3 10 1, ld32 0 3,
  CST 3 1, le 3 0,
  ADDI 3 0 49, ADD 4 3 10, le 4 9,
  ADDI 4 10 5, LD8 4 4, CST 11 32, EQ 11 4 11, inRange 12 4 48 16 13, OR 11 11 12, assert 11,
  .ite 1 (seqs [ADDI 4 10 5, ADD 4 4 0, CST 11 4, SUB 11 1 11, CST 12 4, MEMEQ 13 4 11 12,
    assert 13, ADDI 4 10 9, ADD 4 4 0, CST 11 D_ZERO, CST 12 32, MEMEQ 13 4 11 12, assert 13]) nop]

def leafWrL : List Stmt := [wField 0 10, wField 4 3, ldCell 0 C_KC, wField 12 0, MOV 0 8, wField 16 0,
  wField 20 1, ADD 5 5 3, ADD 5 5 2, ADD 10 10 3]

theorem pLeaf_split : pLeaf = seqs (leafChkL ++ leafWrL) := rfl

/-- Leaf checks, revealed value (kind 1). -/
def LeafChk1 (m : M) (q E : Nat) : Prop :=
  q + 4 ≤ E ∧ q + 4 + rd32 m q + 5 ≤ E ∧ (m.mem (q + 4 + rd32 m q)).toNat = 0 ∧
  1 ≤ rd32 m (q + 4 + rd32 m q + 1) ∧ q + 4 + rd32 m q + rd32 m (q + 4 + rd32 m q + 1) + 49 ≤ E ∧
  ((m.mem (q + 4 + rd32 m q + 5)).toNat = 32 ∨
    (48 ≤ (m.mem (q + 4 + rd32 m q + 5)).toNat ∧ (m.mem (q + 4 + rd32 m q + 5)).toNat < 64)) ∧
  readMem m.mem (q + 4 + rd32 m q + 5 + rd32 m (q + 4 + rd32 m q + 1)) 4 = readMem m.mem q 4 ∧
  readMem m.mem (q + 4 + rd32 m q + 9 + rd32 m (q + 4 + rd32 m q + 1)) 32 = readMem m.mem 136 32

/-- Leaf checks, value by reference (kind 2). -/
def LeafChk2 (m : M) (q E : Nat) : Prop :=
  q + 5 ≤ E ∧ (m.mem q).toNat = 0 ∧ 1 ≤ rd32 m (q + 1) ∧ q + rd32 m (q + 1) + 49 ≤ E ∧
  ((m.mem (q + 5)).toNat = 32 ∨ (48 ≤ (m.mem (q + 5)).toNat ∧ (m.mem (q + 5)).toNat < 64))

/-- Registers after the leaf checks. -/
def LeafRegs (m m' : M) (hl vl val p : Nat) : Prop :=
  m'.mem = m.mem ∧ m'.regs 0 = hl ∧ m'.regs 1 = val ∧ m'.regs 2 = vl ∧ m'.regs 3 = hl + 49 ∧ m'.regs 10 = p ∧
  m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = m.regs 8 ∧ m'.regs 9 = m.regs 9 ∧
  m'.regs 14 = 8 ∧ m'.regs 15 = 1

section
variable {pub cb pb : Bytes}

set_option maxHeartbeats 4000000 in
theorem leafChk1_wp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (h0 : m.regs 0 = 1) (hq : q ≤ E) :
    wp P (Inp pub cb pb) (seqs leafChkL) m (fun m' => LeafChk1 m q E ∧
      LeafRegs m m' (rd32 m (q + 4 + rd32 m q + 1)) (rd32 m q) (q + 4) (q + 4 + rd32 m q)) := by
  simp only [leafChkL, LeafChk1, LeafRegs, rd32]
  rec_auto [hk1, hk8, hP, h0, hE]
  close_conj

set_option maxHeartbeats 4000000 in
theorem leafChk2_wp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (h0 : m.regs 0 = 2) (hq : q ≤ E) :
    wp P (Inp pub cb pb) (seqs leafChkL) m (fun m' => LeafChk2 m q E ∧
      LeafRegs m m' (rd32 m (q + 1)) 0 0 q) := by
  simp only [leafChkL, LeafChk2, LeafRegs, rd32]
  rec_auto [hk1, hk8, hP, h0, hE]
  close_conj

set_option maxHeartbeats 4000000 in
theorem leafChk1_twp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (h0 : m.regs 0 = 1) (hq : q ≤ E)
    (hc : LeafChk1 m q E) :
    twp P (Inp pub cb pb) (seqs leafChkL) m (fun m' c =>
      LeafRegs m m' (rd32 m (q + 4 + rd32 m q + 1)) (rd32 m q) (q + 4) (q + 4 + rd32 m q) ∧ c ≤ 150) := by
  simp only [leafChkL, LeafChk1, LeafRegs, rd32, Nat.add_assoc] at hc ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc
  rec_auto [hk1, hk8, hP, h0, hE, c3, c7, c8]
  close_conj

set_option maxHeartbeats 4000000 in
theorem leafChk2_twp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (h0 : m.regs 0 = 2) (hq : q ≤ E)
    (hc : LeafChk2 m q E) :
    twp P (Inp pub cb pb) (seqs leafChkL) m (fun m' c => LeafRegs m m' (rd32 m (q + 1)) 0 0 q ∧ c ≤ 150) := by
  simp only [leafChkL, LeafChk2, LeafRegs, rd32, Nat.add_assoc] at hc ⊢
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  rec_auto [hk1, hk8, hP, h0, hE, c2]
  close_conj

set_option maxHeartbeats 4000000 in
theorem leafWr_twp {m : M} {e pre pl val vl rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h10 : m.regs 10 = pre) (h3 : m.regs 3 = pl) (h1 : m.regs 1 = val)
    (h2 : m.regs 2 = vl) (h5 : m.regs 5 = rv) (hpre : pre < 4294967296) (hpl : pl < 4294967296)
    (hval : val < 4294967296) (hvl : vl < 4294967296) (hrv : rv < 4294967296) :
    twp P (Inp pub cb pb) (seqs leafWrL) m (fun m' c =>
      m'.mem = wr4 (wr4 (wr4 (wr4 (wr4 m.mem (AR + 24 * e) pre) (AR + 24 * e + 4) pl)
        (AR + 24 * e + 12) (rd32 m C_KC)) (AR + 24 * e + 16) e) (AR + 24 * e + 20) val ∧
      m'.regs 10 = pre + pl ∧ m'.regs 5 = rv + pl + vl ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧
      m'.regs 9 = m.regs 9 ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 120) := by
  simp only [NCAP] at he
  simp only [leafWrL, wField, ldCell, rd32]
  rec_auto [hk1, hk8, h8, h10, h3, h1, h2, h5, readMem_writeMem_disjoint]
  simp only [wr4, show 117000 + 24 * e = e * 24 + 117000 by omega,
    show 117000 + (24 * e + 4) = e * 24 + 117004 by omega, show 117000 + (24 * e + 12) = e * 24 + 117012 by omega,
    show 117000 + (24 * e + 16) = e * 24 + 117016 by omega, show 117000 + (24 * e + 20) = e * 24 + 117020 by omega]

end

end ReexecNpai
