import ReexecNpai.Spec.RcptAux4

/-!
# Receipts phase, part 5: the receipts commitment
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

def LC1 : List Stmt := [CST 4 C_REND, st32 4 10, CST 1 SH8, CST 2 (CLM + 77), CST 3 8]
def LC3 : List Stmt := [CST 1 S_H, CST 2 SH8, SUB 3 10 2, SHA 1 2 3, CST 2 (CLM + 153), CST 3 32,
  MEMEQ 4 1 2 3, assert 4, CST 8 0]

section
variable {pub cb pb : NearSpec.Bytes}

theorem c1_wp {x : M} {R : Nat} (hk8 : x.regs 14 = 8) (h10 : x.regs 10 = PF + R) (hR : R ≤ PMAX) :
    wp P (Inp pub cb pb) (seqs LC1) x (fun y => y.mem = writeMem x.mem 3080 4 (Bytes.leN 4 (PF + R)) ∧
      y.regs 1 = SH8 ∧ y.regs 2 = 2637 ∧ y.regs 3 = 8 ∧ Frame [1, 2, 3, 4, 12, 13] x y) := by
  simp only [PF, PMAX] at h10 hR
  simp only [LC1]
  rcpt_auto [hk8, h10]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hj
  simp [a1, a2, a3, a4, a5, a6]

theorem c1_twp {x : M} {R : Nat} (hk8 : x.regs 14 = 8) (h10 : x.regs 10 = PF + R) (hR : R ≤ PMAX) :
    twp P (Inp pub cb pb) (seqs LC1) x (fun y c => y.mem = writeMem x.mem 3080 4 (Bytes.leN 4 (PF + R)) ∧
      y.regs 1 = SH8 ∧ y.regs 2 = 2637 ∧ y.regs 3 = 8 ∧ Frame [1, 2, 3, 4, 12, 13] x y ∧ c ≤ 20) := by
  simp only [PF, PMAX] at h10 hR
  simp only [LC1]
  rcpt_auto [hk8, h10]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hj
  simp [a1, a2, a3, a4, a5, a6]

theorem cp_spec {y : M} (hk1 : y.regs 15 = 1) (h1 : y.regs 1 = SH8) (h2 : y.regs 2 = 2637) (h3 : y.regs 3 = 8) :
    ∃ m' c, Ev P (Inp pub cb pb) (memcpy 1 2 3 4) y (.ok m') c ∧
      m'.mem = writeMem y.mem SH8 8 (readMem y.mem 2637 8) ∧ Frame [1, 2, 3, 4] y m' ∧ c ≤ 57 := by
  obtain ⟨m', c, e, hm, -, -, -, hF, hc⟩ := memcpy_spec (p := P) (inp := Inp pub cb pb) (d := 1) (s := 2) (k := 3)
    (t := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hk1 h3
    (by rw [h1]; simp [SH8]) (by rw [h2]; simp) (by simp) (by rw [h1, h2]; simp [SH8])
  exact ⟨m', c, e, by rw [hm, h1, h2], hF, by omega⟩

theorem c3_wp {z : M} {R : Nat} (hk8 : z.regs 14 = 8) (hk1 : z.regs 15 = 1) (h10 : z.regs 10 = PF + R)
    (hR : R ≤ PMAX) :
    wp P (Inp pub cb pb) (seqs LC3) z (fun w =>
      ArenaCore.sha256 (readMem z.mem SH8 (R + 8)) = readMem z.mem 2713 32 ∧
      w.mem = writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem SH8 (R + 8))) ∧ w.regs 8 = 0 ∧
      Frame [1, 2, 3, 4, 8, 12, 13] z w) := by
  simp only [PF, PMAX, SH8] at h10 hR ⊢
  have hL : 8844304 + R - 8844296 = R + 8 := by omega
  have hs1 : ∀ L, readMem (writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem 8844296 L))) 1408 32 =
      ArenaCore.sha256 (readMem z.mem 8844296 L) := fun L => by
    rw [readMem_writeMem_self _ _ _ _ (by simp [ArenaCore.sha256_length]), List.take_of_length_le (by simp [ArenaCore.sha256_length])]
  have hs2 : ∀ L, readMem (writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem 8844296 L))) 2713 32 =
      readMem z.mem 2713 32 := fun L => readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)
  simp only [LC3]
  rcpt_auto [hk8, hk1, h10, hL, hs1, hs2]
  exact ⟨by assumption, by rcpt_frame_tac⟩

theorem c3_twp {z : M} {R : Nat} (hk8 : z.regs 14 = 8) (hk1 : z.regs 15 = 1) (h10 : z.regs 10 = PF + R)
    (hR : R ≤ PMAX) (hcom : ArenaCore.sha256 (readMem z.mem SH8 (R + 8)) = readMem z.mem 2713 32) :
    twp P (Inp pub cb pb) (seqs LC3) z (fun w c =>
      w.mem = writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem SH8 (R + 8))) ∧ w.regs 8 = 0 ∧
      Frame [1, 2, 3, 4, 8, 12, 13] z w ∧ c ≤ 80000) := by
  simp only [PF, PMAX, SH8] at h10 hR hcom ⊢
  have hL : 8844304 + R - 8844296 = R + 8 := by omega
  have hs1 : ∀ L, readMem (writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem 8844296 L))) 1408 32 =
      ArenaCore.sha256 (readMem z.mem 8844296 L) := fun L => by
    rw [readMem_writeMem_self _ _ _ _ (by simp [ArenaCore.sha256_length]),
      List.take_of_length_le (by simp [ArenaCore.sha256_length])]
  have hs2 : ∀ L, readMem (writeMem z.mem 1408 32 (ArenaCore.sha256 (readMem z.mem 8844296 L))) 2713 32 =
      readMem z.mem 2713 32 := fun L => readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)
  simp only [LC3]
  rcpt_auto [hk8, hk1, h10, hL, hs1, hs2]
  exact ⟨by omega, hcom, by rcpt_frame_tac, by omega⟩

end

end RcptProof

end ReexecNpai
