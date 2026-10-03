import ReexecNpai.Spec.RecAux29

/-!
# Record parse: the kind dispatch of `pRecord`
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

def recPre : List Stmt := [CST 0 NCAP, lt 8 0, LD8 0 10, ADDI 10 10 1, CST 1 1, EQ 1 0 1, CST 2 2, EQ 2 0 2,
  OR 1 1 2]
def recExtL : List Stmt := [CST 1 3, EQ 1 0 1]
def recBrL : List Stmt := [CST 1 4, SUB 1 0 1, CST 2 3, LTU 1 1 2, assert 1]

theorem pRecord_split : pRecord = seqs (recPre ++ [.ite 1 pLeaf (seqs (recExtL ++
    [.ite 1 pExt (seqs (recBrL ++ [pBranch]))])), pPush]) := rfl

section
variable {pub cb pb : Bytes}

set_option maxHeartbeats 4000000 in
theorem recPre_wp {m : M} {q : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h10 : m.regs 10 = q) (hq : q < 13844304) :
    wp P (Inp pub cb pb) (seqs recPre) m (fun m' => m.regs 8 < NCAP ∧ m'.mem = m.mem ∧ m'.regs 10 = q + 1 ∧
      m'.regs 0 = (m.mem q).toNat ∧
      m'.regs 1 = (if (m.mem q).toNat = 1 ∨ (m.mem q).toNat = 2 then 1 else 0) ∧
      (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → j ≠ 13 → m'.regs j = m.regs j)) := by
  simp only [recPre]
  rec_auto [hk1, hk8, h10]
  repeat' apply And.intro
  all_goals first | omega | (intro j h0 h1 h2 h10 h13; simp [h0, h1, h2, h10, h13])

set_option maxHeartbeats 4000000 in
theorem recPre_twp {m : M} {q : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h10 : m.regs 10 = q) (hq : q < 13844304) (he : m.regs 8 < NCAP) :
    twp P (Inp pub cb pb) (seqs recPre) m (fun m' c => m'.mem = m.mem ∧ m'.regs 10 = q + 1 ∧
      m'.regs 0 = (m.mem q).toNat ∧
      m'.regs 1 = (if (m.mem q).toNat = 1 ∨ (m.mem q).toNat = 2 then 1 else 0) ∧
      (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 20) := by
  simp only [NCAP] at he
  simp only [recPre]
  have he' : ¬ 272728 ≤ m.regs 8 := by omega
  rec_auto [hk1, hk8, h10, he']
  repeat' apply And.intro
  all_goals first | omega | (intro j h0 h1 h2 h10 h13; simp [h0, h1, h2, h10, h13])

set_option maxHeartbeats 4000000 in
theorem recExt_twp {m : M} {k : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = k) :
    twp P (Inp pub cb pb) (seqs recExtL) m (fun m' c => m'.mem = m.mem ∧
      m'.regs 1 = (if k = 3 then 1 else 0) ∧ (∀ j, j ≠ 1 → m'.regs j = m.regs j) ∧ c ≤ 5) := by
  simp only [recExtL]
  rec_auto [hk1, hk8, h0]
  repeat' apply And.intro
  all_goals first | omega | (intro j h1; simp [h1])

set_option maxHeartbeats 4000000 in
theorem recBr_wp {m : M} {k : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = k)
    (hk : k < 256) :
    wp P (Inp pub cb pb) (seqs recBrL) m (fun m' => (k = 4 ∨ k = 5 ∨ k = 6) ∧ m'.mem = m.mem ∧
      (∀ j, j ≠ 1 → j ≠ 2 → m'.regs j = m.regs j)) := by
  simp only [recBrL]
  rec_auto [hk1, hk8, h0]
  rename_i hs
  simp only [BinOp.eval, wordMod] at hs
  exact ⟨by omega, fun j h1 h2 => by simp [h1, h2]⟩

set_option maxHeartbeats 4000000 in
theorem recBr_twp {m : M} {k : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = k)
    (hk : k = 4 ∨ k = 5 ∨ k = 6) :
    twp P (Inp pub cb pb) (seqs recBrL) m (fun m' c => m'.mem = m.mem ∧
      (∀ j, j ≠ 1 → j ≠ 2 → m'.regs j = m.regs j) ∧ c ≤ 10) := by
  simp only [recBrL]
  have hs : BinOp.sub.eval k 4 = k - 4 := by simp only [BinOp.eval, wordMod]; omega
  rec_auto [hk1, hk8, h0, hs]
  repeat' apply And.intro
  all_goals first | omega | (intro j h1 h2; simp [h1, h2])

end

end ReexecNpai
