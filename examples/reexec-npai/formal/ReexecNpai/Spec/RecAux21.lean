import ReexecNpai.Spec.RecAux20

/-!
# Record parse: branch records, remaining straight-line chunks
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem evShl (x k : Nat) (hk : k < 64) (h : x * 2 ^ k < 18446744073709551616) :
    BinOp.shl.eval x k = x * 2 ^ k := by
  simp only [BinOp.eval, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt (by unfold wordMod; omega)

section
variable {pub cb pb : Bytes}

set_option maxHeartbeats 4000000 in
theorem brL4a_twp {m : M} {R E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 10 + m.regs 0 = R) (hR : R ≤ 13844304) (hEE : E ≤ 13844304) (h9 : m.regs 9 = E)
    (h3 : m.regs 3 < 65536) (hc1 : R + 2 ≤ E) (hc2 : (m.regs 3 &&& (readMem m.mem R 2).leToNat) = m.regs 3) :
    twp P (Inp pub cb pb) (seqs brL4a) m (fun m' c => m'.mem = m.mem ∧
      m'.regs 1 = (readMem m.mem R 2).leToNat ∧ m'.regs 2 = R ∧
      (∀ j, j ≠ 1 → j ≠ 2 → j ≠ 6 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 40) := by
  simp only [brL4a]
  rec_auto [hk1, hk8, h0, h9, evAndLt _ _ h3, hc2]
  repeat' apply And.intro
  all_goals first | assumption | omega | rfl |
    (intro j h1 h2 h6 h11 h12 h13; simp [h1, h2, h6, h11, h12, h13])

/-- Registers and memory after `brL4b`. -/
def BrRegs4 (m m' : M) (e hdr np pre R ex bm rv : Nat) : Prop :=
  m'.mem = wr4 m.mem (AR + 24 * e + 4) (hdr + 32 * np + 10) ∧
  m'.regs 0 = hdr + 32 * np + 10 ∧ m'.regs 5 = rv + (hdr + 32 * np + 10) ∧
  m'.regs 2 = R + 32 * np + 2 ∧ m'.regs 10 = pre + (hdr + 32 * np + 10) ∧
  m'.regs 1 = bm + ex * 65536 ∧ m'.regs 3 = rd32 m C_KC ∧ m'.regs 6 = 16 ∧
  m'.regs 7 = m.regs 7 ∧ m'.regs 8 = e ∧ m'.regs 9 = m.regs 9 ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1

set_option maxHeartbeats 4000000 in
theorem brL4b_wp {m : M} {e hdr np pre R ex bm rv E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = hdr) (h6 : m.regs 6 = np) (h10 : m.regs 10 = pre) (h2 : m.regs 2 = R) (h3 : m.regs 3 = ex)
    (h1 : m.regs 1 = bm) (h5 : m.regs 5 = rv) (h8 : m.regs 8 = e) (h9 : m.regs 9 = E)
    (he : e < NCAP) (hhdr : hdr ≤ 37) (hnp : np ≤ 16) (hpre : pre ≤ 13844304) (hR : R ≤ 13844304)
    (hex : ex < 65536) (hbm : bm < 65536) (hrv : rv < 4294967296) :
    wp P (Inp pub cb pb) (seqs brL4b) m (fun m' => pre + (hdr + 32 * np + 10) ≤ E ∧
      BrRegs4 m m' e hdr np pre R ex bm rv) := by
  simp only [NCAP] at he
  simp only [brL4b, wField, ldCell, BrRegs4, rd32]
  have s5 : BinOp.shl.eval np 5 = np * 32 := evShl np 5 (by omega) (by simp; omega)
  have s16 : BinOp.shl.eval ex 16 = ex * 65536 := evShl ex 16 (by omega) (by simp; omega)
  rec_auto [hk1, hk8, h0, h6, h10, h2, h3, h1, h5, h8, h9, s5, s16, readMem_writeMem_disjoint]
  repeat' apply And.intro
  all_goals first | assumption | omega |
    (simp only [wr4, show 117000 + (24 * e + 4) = e * 24 + 117004 by omega,
      show np * 32 = 32 * np by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL4b_twp {m : M} {e hdr np pre R ex bm rv E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h0 : m.regs 0 = hdr) (h6 : m.regs 6 = np) (h10 : m.regs 10 = pre) (h2 : m.regs 2 = R) (h3 : m.regs 3 = ex)
    (h1 : m.regs 1 = bm) (h5 : m.regs 5 = rv) (h8 : m.regs 8 = e) (h9 : m.regs 9 = E)
    (he : e < NCAP) (hhdr : hdr ≤ 37) (hnp : np ≤ 16) (hpre : pre ≤ 13844304) (hR : R ≤ 13844304)
    (hex : ex < 65536) (hbm : bm < 65536) (hrv : rv < 4294967296) (hc : pre + (hdr + 32 * np + 10) ≤ E) :
    twp P (Inp pub cb pb) (seqs brL4b) m (fun m' c => BrRegs4 m m' e hdr np pre R ex bm rv ∧ c ≤ 60) := by
  simp only [NCAP] at he
  simp only [brL4b, wField, ldCell, BrRegs4, rd32]
  have s5 : BinOp.shl.eval np 5 = np * 32 := evShl np 5 (by omega) (by simp; omega)
  have s16 : BinOp.shl.eval ex 16 = ex * 65536 := evShl ex 16 (by omega) (by simp; omega)
  have hc' : ¬ E < pre + (hdr + (np * 32 + 10)) := by omega
  rec_auto [hk1, hk8, h0, h6, h10, h2, h3, h1, h5, h8, h9, s5, s16, readMem_writeMem_disjoint, hc']
  repeat' apply And.intro
  all_goals first | assumption | omega |
    (simp only [wr4, show 117000 + (24 * e + 4) = e * 24 + 117004 by omega,
      show np * 32 = 32 * np by omega]; done)

set_option maxHeartbeats 4000000 in
theorem brL5_twp {m : M} {e kc : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h3 : m.regs 3 = kc) (hkc : kc < 4294967296) (h8 : m.regs 8 = e) (he : e < NCAP) :
    twp P (Inp pub cb pb) (seqs brL5) m (fun m' c =>
      m'.mem = wr4 (wr4 m.mem C_KC kc) (AR + 24 * e + 16) e ∧
      (∀ j, j ≠ 0 → j ≠ 4 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c ≤ 40) := by
  simp only [NCAP] at he
  simp only [brL5, wField, stCell]
  rec_auto [hk1, hk8, h3, h8]
  repeat' apply And.intro
  all_goals first | assumption | omega |
    (simp only [wr4, C_KC, show 117000 + (24 * e + 16) = e * 24 + 117016 by omega]; done) |
    (intro j h0 h4 h11 h12 h13; simp [h0, h4, h11, h12, h13])

end

end ReexecNpai
