import ZkFormal.Stark.Statements

/-!
# ZkFormal.Stark.Laws — `StarkFieldLaws Fp Fp8`, decoding agreement (F1, F2)
-/

namespace ZkFormal.Stark

open ZkFormal.Algebra Lean.Grind

instance lawsInst : StarkFieldLaws Fp Fp8 where
  embed_add a b := Fp8.ofBase_add a b
  embed_mul a b := Fp8.ofBase_mul a b
  embed_one := rfl
  embed_inj _ _ h := Fp8.ofBase_inj h
  limbs_length _ := rfl
  ofLimbs_limbs _ := rfl
  toNat_lt a := Fp.toNat_lt a
  toNat_inj _ _ h := Fp.ext h
  natCast_toNat a := by
    apply Fp.ext
    show (Fp.ofNat a.toNat).toNat = a.toNat
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (Fp.toNat_lt a)]

theorem laws : LawsStmt := ⟨lawsInst⟩

theorem decodeChal_agree (y : ArenaCore.Bytes) :
    decodeChal (F := Fp) y = ZkFormal.Algebra.decodeChal y := rfl

theorem decodeOod_agree (y : ArenaCore.Bytes) :
    decodeOod (F := Fp) y = ZkFormal.Algebra.decodeOod y := by
  have hc := decodeChal_agree y
  unfold decodeOod ZkFormal.Algebra.decodeOod
  generalize hf : (fun i => ofNatF (F := Fp) (be32At y i)) = f
  have hl : (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := rfl
  have hd : ZkFormal.Algebra.decodeChal y = ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩ := by
    rw [← hc, ← hf]; rfl
  simp only [hl, hd]
  by_cases h : (Fp8.IsBase ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩)
  · rw [if_pos h]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    simp only at h1 h2 h3 h4 h5 h6 h7
    simp [h1, h2, h3, h4, h5, h6, h7, StarkField.ofLimbs, Fp8.ofCoeffs]
  · rw [if_neg h]
    have : ¬ ([f 1, f 2, f 3, f 4, f 5, f 6, f 7].all fun a => decide (a = 0)) = true := by
      intro h'; apply h; simp at h'; exact h'
    rw [if_neg (by simpa using this)]
    rfl

theorem decode_agree : DecodeAgreeStmt := fun y => ⟨decodeChal_agree y, decodeOod_agree y⟩

end ZkFormal.Stark
