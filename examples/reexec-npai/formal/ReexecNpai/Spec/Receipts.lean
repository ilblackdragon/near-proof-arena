import ReexecNpai.Spec.Front
import ReexecNpai.Spec.RcptPos

/-!
# Phase spec: the receipts section
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp

theorem leToNat_eq_leNat : ∀ l : Bytes, Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [Bytes.leToNat, NearSpec.leNat, leToNat_eq_leNat xs]

/-- Reading the proof copy. -/
theorem rdProof {M0 : Nat → UInt8} {pb : Bytes} (h : readMem M0 PF pb.length = pb) {o n : Nat}
    (hn : o + n ≤ pb.length) : readMem M0 (PF + o) n = sl pb o n := by
  apply List.ext_getElem (by simp [sl]; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  rw [readMem_getElem]
  have := mem_of_readMem h (o + i) (by omega)
  rw [Nat.add_assoc, this]
  simp [sl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o + i < pb.length by omega)]

/-- What the receipt loop body needs from the current state. -/
structure RcptPre (cb pb : Bytes) (o e : Nat) (m : M) : Prop extends ClaimIn cb m where
  proof : readMem m.mem PF pb.length = pb
  plen : pb.length ≤ PMAX
  rP : m.regs 10 = PF + o
  rE : m.regs 9 = PF + pb.length
  rT : m.regs 6 = e
  he : RT ≤ e ∧ e + 64 ≤ OL
  ho : o ≤ pb.length

theorem borshField_wp {pub cb pb : Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) (off : Nat)
    (hoff : off + 8 ≤ 64) :
    wp P (Inp pub cb pb) (pBorshField off) m (fun m' => ∃ b o', borshAt pb o = some (b, o') ∧
      m'.regs 10 = PF + o' ∧ m'.regs 1 = PF + o + 4 ∧ m'.regs 2 = b.length ∧
      m'.mem = writeMem (writeMem m.mem (e + off) 4 (Bytes.leN 4 (PF + o + 4))) (e + off + 4) 4
        (Bytes.leN 4 b.length) ∧ Frame [1, 2, 3, 10, 12, 13] m m') := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho⟩ := hp
  simp only [PMAX, RT, OL] at hpl he
  simp only [pBorshField]
  npai_auto [hk1, hk8, hP, hE, hT]
  rename_i h1 h2
  have hL : (readMem m.mem (8844304 + o) 4).leToNat = NearSpec.leNat (sl pb o 4) := by
    rw [show (8844304 : Nat) = PF from rfl, rdProof hpf (by omega), leToNat_eq_leNat]
  rw [hL] at h2 ⊢
  have hlen : (sl pb (o + 4) (NearSpec.leNat (sl pb o 4))).length = NearSpec.leNat (sl pb o 4) :=
    sl_length_of (by omega)
  refine ⟨sl pb (o + 4) (NearSpec.leNat (sl pb o 4)), o + 4 + NearSpec.leNat (sl pb o 4), ?_, by omega,
    hlen.symm, by rw [hlen, Nat.add_assoc, Nat.add_assoc], ?_⟩
  · simp only [borshAt]
    rw [if_pos (by omega), if_pos (by omega)]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [setReg_apply]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
    simp [h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]

end ReexecNpai
