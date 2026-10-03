import ReexecNpai.Spec.Base

/-!
# Phase specs: setup, claim, proof copy
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp

/-- `u32` LE at address `a`. -/
def rd32 (m : M) (a : Nat) : Nat := Bytes.leToNat (readMem m.mem a 4)

/-- The data segment is intact and the constant registers are set. -/
structure Base (m : M) : Prop where
  k1 : m.regs 15 = 1
  k8 : m.regs 14 = 8
  data : readMem m.mem 0 168 = dataSeg

/-- After the claim phase. -/
structure ClaimIn (cb : Bytes) (m : M) : Prop extends Base m where
  claim : readMem m.mem CLM 309 = cb
  shape : claimShape cb

/-- After the proof copy. -/
structure Front (cb pb : Bytes) (m : M) : Prop extends ClaimIn cb m where
  proof : readMem m.mem PF pb.length = pb
  plen : pb.length ≤ PMAX
  pend : rd32 m C_PEND = PF + pb.length

theorem dataSeg_length : dataSeg.length = 168 := by decide

theorem readMem_prefix {M0 : Nat → UInt8} {a n : Nat} {l : Bytes} (h : readMem M0 a n = l) (k : Nat)
    (hk : k ≤ n) : readMem M0 a k = l.take k := by
  subst h
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [readMem]

theorem claimPrefix_eq : dataSeg.take 77 = claimPrefix := by decide

/-! ## Setup -/

theorem setup_wp {pub cb pb : Bytes} {m : M} (hd : readMem m.mem 0 168 = dataSeg) :
    wp P (Inp pub cb pb) pSetup m Base := by
  simp only [pSetup]
  npai_vc
  exact ⟨by simp [setReg_apply], by simp [setReg_apply], hd⟩

theorem setup_twp {pub cb pb : Bytes} {m : M} (hd : readMem m.mem 0 168 = dataSeg) :
    twp P (Inp pub cb pb) pSetup m (fun m' c => Base m' ∧ c = 2) := by
  simp only [pSetup]
  npai_vc
  exact ⟨by simp [setReg_apply], by simp [setReg_apply], hd⟩

end ReexecNpai

namespace ReexecNpai
open NpaiIR ArenaCore Interp

theorem claim_wp {pub cb pb : Bytes} {m : M} (hb : Base m) (hcb : cb.length < 4294967296) :
    wp P (Inp pub cb pb) pClaim m (ClaimIn cb) := by
  obtain ⟨hk1, hk8, hd⟩ := hb
  simp only [pClaim]
  npai_vc [hk1, hk8]
  intro h1 _ h3
  have hdm : readMem (writeMem m.mem 2560 309 cb) 0 168 = dataSeg := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact hd
  rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by omega),
    readMem_prefix hdm 77 (by omega), claimPrefix_eq] at h3
  refine ⟨⟨by simp [setReg_apply, hk1], by simp [setReg_apply, hk8], hdm⟩, ?_, ⟨h1, by simpa using h3⟩⟩
  simp only [CLM]
  rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by omega)]
  simp [← h1]

end ReexecNpai

namespace ReexecNpai
open NpaiIR ArenaCore Interp

theorem claim_twp {pub cb pb : Bytes} {m : M} (hb : Base m) (hs : claimShape cb) :
    twp P (Inp pub cb pb) pClaim m (fun m' c => ClaimIn cb m' ∧ c ≤ 30) := by
  obtain ⟨hk1, hk8, hd⟩ := hb
  obtain ⟨hl, hp⟩ := hs
  simp only [pClaim]
  npai_vc [hk1, hk8, hl]
  have hdm : readMem (writeMem m.mem 2560 309 cb) 0 168 = dataSeg := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact hd
  have h3 : readMem (writeMem m.mem 2560 309 cb) 2560 77 = readMem (writeMem m.mem 2560 309 cb) 0 77 := by
    rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by omega), readMem_prefix hdm 77 (by omega),
      claimPrefix_eq]
    simpa using hp
  simp only [h3, ↓reduceIte, true_and]
  have hcl : readMem (writeMem m.mem 2560 309 cb) 2560 309 = cb := by
    rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by omega)]; simp [← hl]
  exact { toBase := ⟨by simp [setReg_apply, hk1], by simp [setReg_apply, hk8], hdm⟩, claim := hcl,
          shape := ⟨hl, hp⟩ }

end ReexecNpai

namespace ReexecNpai
open NpaiIR ArenaCore Interp

theorem proof_wp {pub cb pb : Bytes} {m : M} (hc : ClaimIn cb m) (hpb : pb.length < 4294967296) :
    wp P (Inp pub cb pb) pProof m (Front cb pb) := by
  obtain ⟨⟨hk1, hk8, hd⟩, hcl, hs⟩ := hc
  simp only [pProof]
  npai_vc [hk1, hk8]
  intro h1 h3
  have hP : readMem (writeMem (writeMem m.mem 8844304 pb.length pb) 3072 4
      (Bytes.leN 4 (8844304 + pb.length))) 8844304 pb.length = pb := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_sub _ _ _ _ _ _ (by omega)
      (by omega) (by omega)]
    simp
  refine { toClaimIn := ⟨⟨by simp [setReg_apply, hk1], by simp [setReg_apply, hk8], ?_⟩, ?_, hs⟩,
           proof := hP, plen := by simp only [PMAX]; omega, pend := ?_ }
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    exact hd
  · simp only [CLM] at hcl ⊢
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    exact hcl
  · simp only [rd32, C_PEND, PF]
    rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by simp [Bytes.leN_length])]
    simp only [Nat.sub_self, List.drop_zero]
    rw [List.take_of_length_le (by simp [Bytes.leN_length]), leToNat_leN _ _ (by omega)]

end ReexecNpai

namespace ReexecNpai
open NpaiIR ArenaCore Interp

theorem proof_twp {pub cb pb : Bytes} {m : M} (hc : ClaimIn cb m) (hpb : pb.length ≤ PMAX) :
    twp P (Inp pub cb pb) pProof m (fun m' c => Front cb pb m' ∧ c ≤ 100000) := by
  obtain ⟨⟨hk1, hk8, hd⟩, hcl, hs⟩ := hc
  simp only [PMAX] at hpb
  simp only [pProof]
  npai_vc [hk1, hk8, show ¬ 5000000 < pb.length by omega, show pb.length ≤ 5000000 from hpb]
  have hP : readMem (writeMem (writeMem m.mem 8844304 pb.length pb) 3072 4
      (Bytes.leN 4 (8844304 + pb.length))) 8844304 pb.length = pb := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_sub _ _ _ _ _ _ (by omega)
      (by omega) (by omega)]
    simp
  refine ⟨by omega, ?_, by omega⟩
  refine { toClaimIn := ⟨⟨by simp [setReg_apply, hk1], by simp [setReg_apply, hk8], ?_⟩, ?_, hs⟩,
           proof := hP, plen := by simp only [PMAX]; omega, pend := ?_ }
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    exact hd
  · simp only [CLM] at hcl ⊢
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    exact hcl
  · simp only [rd32, C_PEND, PF]
    rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by simp [Bytes.leN_length])]
    simp only [Nat.sub_self, List.drop_zero]
    rw [List.take_of_length_le (by simp [Bytes.leN_length]), leToNat_leN _ _ (by omega)]

end ReexecNpai
