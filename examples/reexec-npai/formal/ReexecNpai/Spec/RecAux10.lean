import ReexecNpai.Spec.RecAux5

/-!
# Record parse: extension records, bytecode chunks
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

def extL1 : List Stmt := [need 10 1 9, LD8 1 10, CST 3 1, le 1 3, ADDI 10 10 1,
  need 10 5 9, LD8 3 10, CST 2 3, eqc 3 2]
def extL2 : List Stmt := [wField 0 10, ldCell 6 C_KC, wField 12 6, CST 2 0, wField 20 2]
def extL3 : List Stmt := [ADDI 3 10 1, ld32 0 3,
  CST 3 1, le 3 0,
  ADDI 2 0 45, wField 4 2, ADD 5 5 2,
  ADD 3 2 10, le 3 9,
  ADDI 3 10 5, LD8 3 3, CST 11 0, EQ 11 3 11, inRange 12 3 16 16 13, OR 11 11 12, assert 11,
  CST 11 1, EQ 11 0 11, CST 12 0, EQ 12 3 12, AND 3 11 12,
  ADDI 0 0 5, ADD 0 0 10,
  ADD 10 10 2,
  MOV 2 8]
def extA1 : List Stmt := [CST 11 D_ZERO, CST 12 32, MEMEQ 13 0 11 12, assert 13, CST 11 1, le 11 7]
def extA2 : List Stmt := [SUB 7 7 15, CST 4 4, MUL 4 7 4, ADDI 4 4 STK, ld32 1 4,
      CST 4 24, MUL 4 1 4, ADDI 4 4 (AR + 8), st32 4 0,
      CST 4 4, MUL 4 6 4, ADDI 4 4 KL, st32 4 1, ADDI 6 6 1, stCell C_KC 6,
      .ite 3 (seqs [CST 4 24, MUL 4 1 4, ADDI 4 4 (AR + 16), ld32 2 4]) nop]

theorem pExt_split : pExt = seqs (extL1 ++ extL2 ++ extL3 ++
    [.ite 1 (seqs (extA1 ++ extA2)) (.ite 3 (CST 2 NONE) nop), wField 16 2]) := rfl

section
variable {pub cb pb : Bytes}

/-- Checks of the first chunk. -/
def ExtChk1 (m : M) (q E : Nat) : Prop :=
  q + 1 ≤ E ∧ (m.mem q).toNat ≤ 1 ∧ q + 6 ≤ E ∧ (m.mem (q + 1)).toNat = 3

theorem ext1_wp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (hq : q ≤ E) :
    wp P (Inp pub cb pb) (seqs extL1) m (fun m' => ExtChk1 m q E ∧ m'.mem = m.mem ∧
      m'.regs 1 = (m.mem q).toNat ∧ m'.regs 10 = q + 1 ∧
      m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = m.regs 8 ∧ m'.regs 9 = m.regs 9 ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [extL1, ExtChk1]
  rec_auto [hk1, hk8, hP, hE]
  close_conj

theorem ext1_twp {m : M} {q E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = q) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (hc : ExtChk1 m q E) :
    twp P (Inp pub cb pb) (seqs extL1) m (fun m' c => m'.mem = m.mem ∧
      m'.regs 1 = (m.mem q).toNat ∧ m'.regs 10 = q + 1 ∧
      m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = m.regs 8 ∧ m'.regs 9 = m.regs 9 ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 40) := by
  simp only [extL1, ExtChk1] at hc ⊢
  obtain ⟨c1, c2, c3, c4⟩ := hc
  rec_auto [hk1, hk8, hP, hE, c4]
  close_conj

set_option maxHeartbeats 4000000 in
theorem ext2_twp {m : M} {e p : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h10 : m.regs 10 = p) (hp : p < 4294967296) :
    twp P (Inp pub cb pb) (seqs extL2) m (fun m' c =>
      m'.mem = wr4 (wr4 (wr4 m.mem (AR + 24 * e) p) (AR + 24 * e + 12) (rd32 m C_KC)) (AR + 24 * e + 20) 0 ∧
      m'.regs 6 = rd32 m C_KC ∧ m'.regs 2 = 0 ∧ m'.regs 10 = p ∧ m'.regs 1 = m.regs 1 ∧
      m'.regs 5 = m.regs 5 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧ m'.regs 9 = m.regs 9 ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 80) := by
  simp only [NCAP] at he
  simp only [extL2, wField, ldCell, rd32]
  rec_auto [hk1, hk8, h8, h10, readMem_writeMem_disjoint]
  simp only [wr4, show 117000 + 24 * e = e * 24 + 117000 by omega,
    show 117000 + (24 * e + 12) = e * 24 + 117012 by omega, show 117000 + (24 * e + 20) = e * 24 + 117020 by omega]

/-- Checks of the third chunk (on its input memory). -/
def ExtChk3 (m : M) (p E : Nat) : Prop :=
  1 ≤ rd32 m (p + 1) ∧ p + rd32 m (p + 1) + 45 ≤ E ∧
  ((m.mem (p + 5)).toNat = 0 ∨ (16 ≤ (m.mem (p + 5)).toNat ∧ (m.mem (p + 5)).toNat < 32))

/-- Registers and memory after the third chunk. -/
def ExtRegs3 (m m' : M) (p e rv : Nat) : Prop :=
  m'.mem = wr4 m.mem (AR + 24 * e + 4) (rd32 m (p + 1) + 45) ∧
  m'.regs 0 = rd32 m (p + 1) + 5 + p ∧ m'.regs 2 = e ∧
  m'.regs 3 = (if rd32 m (p + 1) = 1 ∧ (m.mem (p + 5)).toNat = 0 then 1 else 0) ∧
  m'.regs 5 = rv + (rd32 m (p + 1) + 45) ∧ m'.regs 10 = p + (rd32 m (p + 1) + 45) ∧
  m'.regs 1 = m.regs 1 ∧ m'.regs 6 = m.regs 6 ∧ m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧
  m'.regs 9 = m.regs 9 ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1

set_option maxHeartbeats 4000000 in
theorem ext3_wp {m : M} {p E e rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = p) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (hq : p + 6 ≤ E) (h8 : m.regs 8 = e)
    (he : e < NCAP) (h5 : m.regs 5 = rv) (hrv : rv < 4294967296) (hpA : AR + 24 * NCAP ≤ p) :
    wp P (Inp pub cb pb) (seqs extL3) m (fun m' => ExtChk3 m p E ∧ ExtRegs3 m m' p e rv) := by
  simp only [NCAP, AR] at he hpA
  simp only [extL3, ExtChk3, ExtRegs3, wField, rd32]
  rec_auto [hk1, hk8, hP, hE, h8, h5, writeMem_apply_out]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 4) = e * 24 + 117004 by omega])

set_option maxHeartbeats 4000000 in
theorem ext3_twp {m : M} {p E e rv : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hP : m.regs 10 = p) (hEE : E ≤ 13844304) (hE : m.regs 9 = E) (hq : p + 6 ≤ E) (h8 : m.regs 8 = e)
    (he : e < NCAP) (h5 : m.regs 5 = rv) (hrv : rv < 4294967296) (hpA : AR + 24 * NCAP ≤ p)
    (hc : ExtChk3 m p E) :
    twp P (Inp pub cb pb) (seqs extL3) m (fun m' c => ExtRegs3 m m' p e rv ∧ c ≤ 100) := by
  simp only [NCAP, AR] at he hpA
  simp only [extL3, ExtChk3, ExtRegs3, wField, rd32, Nat.add_assoc] at hc ⊢
  obtain ⟨c1, c2, c3⟩ := hc
  rec_auto [hk1, hk8, hP, hE, h8, h5, writeMem_apply_out]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 4) = e * 24 + 117004 by omega])

theorem extA1_wp {m : M} {s sp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = s) (hs : s + 32 ≤ 13844304) (h7 : m.regs 7 = sp) :
    wp P (Inp pub cb pb) (seqs extA1) m (fun m' => readMem m.mem s 32 = readMem m.mem 136 32 ∧ 1 ≤ sp ∧
      m'.mem = m.mem ∧ (∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j)) := by
  simp only [extA1]
  rec_auto [hk1, hk8, h0, h7]
  repeat' apply And.intro
  all_goals first | assumption | omega | (intro j h1 h2 h3; simp [h1, h2, h3])

theorem extA1_twp {m : M} {s sp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = s) (hs : s + 32 ≤ 13844304) (h7 : m.regs 7 = sp)
    (hz : readMem m.mem s 32 = readMem m.mem 136 32) (hsp : 1 ≤ sp) :
    twp P (Inp pub cb pb) (seqs extA1) m (fun m' c =>
      m'.mem = m.mem ∧ (∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 20) := by
  simp only [extA1]
  rec_auto [hk1, hk8, h0, h7, hz]
  repeat' apply And.intro
  all_goals first | assumption | omega | (intro j h1 h2 h3; simp [h1, h2, h3])

/-- Registers preserved by `extA2`. -/
def ExtA2Frame (m m' : M) : Prop :=
  m'.regs 0 = m.regs 0 ∧ m'.regs 3 = m.regs 3 ∧ m'.regs 5 = m.regs 5 ∧ m'.regs 8 = m.regs 8 ∧
  m'.regs 9 = m.regs 9 ∧ m'.regs 10 = m.regs 10 ∧ m'.regs 14 = m.regs 14 ∧ m'.regs 15 = m.regs 15

set_option maxHeartbeats 4000000 in
theorem extA2_twp {m : M} {s sp kc c : Nat} {emp : Bool} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = s) (hs : s < 4294967296) (h7 : m.regs 7 = sp) (hsp : 1 ≤ sp) (hspN : sp ≤ NCAP)
    (hc : rd32 m (STK + 4 * (sp - 1)) = c) (hcN : c < NCAP) (h6 : m.regs 6 = kc) (hkc : kc < NCAP)
    (h3 : m.regs 3 = if emp then 1 else 0) :
    twp P (Inp pub cb pb) (seqs extA2) m (fun m' cost =>
      m'.mem = wr4 (wr4 (wr4 m.mem (AR + 24 * c + 8) s) (KL + 4 * kc) c) C_KC (kc + 1) ∧
      m'.regs 7 = sp - 1 ∧ m'.regs 6 = kc + 1 ∧
      m'.regs 2 = (if emp then rd32 m (AR + 24 * c + 16) else m.regs 2) ∧ ExtA2Frame m m' ∧
      cost ≤ 120) := by
  simp only [NCAP] at hspN hcN hkc
  simp only [STK, rd32] at hc
  rw [show 7753384 + 4 * (sp - 1) = (sp - 1) * 4 + 7753384 by omega] at hc
  have e1 : 117000 + (24 * c + 8) = c * 24 + 117008 := by omega
  have e2 : 6662472 + 4 * kc = kc * 4 + 6662472 := by omega
  have e3 : 117000 + (24 * c + 16) = c * 24 + 117016 := by omega
  cases emp
  · simp only [Bool.false_eq_true, ↓reduceIte] at h3 ⊢
    simp only [extA2, stCell, rd32, ExtA2Frame]
    rec_auto [hk1, hk8, h0, h7, h6, h3, hc]
    repeat' apply And.intro
    all_goals first | assumption | omega | rfl | (simp only [wr4, e1, e2]; done)
  · simp only [↓reduceIte] at h3 ⊢
    simp only [extA2, stCell, rd32, ExtA2Frame]
    rec_auto [hk1, hk8, h0, h7, h6, h3, hc, readMem_writeMem_disjoint]
    repeat' apply And.intro
    all_goals first | assumption | omega | rfl | (simp only [wr4, e1, e2]; done) | (simp only [e3]; done)

theorem extRes_twp {m : M} {e r : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h8 : m.regs 8 = e) (he : e < NCAP) (h2 : m.regs 2 = r) (hr : r < 18446744073709551616) :
    twp P (Inp pub cb pb) (wField 16 2) m (fun m' c => m'.mem = wr4 m.mem (AR + 24 * e + 16) r ∧
      (∀ j, j ≠ 4 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 20) := by
  simp only [NCAP] at he
  simp only [wField]
  rec_auto [hk1, hk8, h8, h2]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (simp only [wr4, show 117000 + (24 * e + 16) = e * 24 + 117016 by omega]; done) |
    (intro j h1 h2 h3 h4; simp [h1, h2, h3, h4])

end

end ReexecNpai
