import ReexecV3D3.NormalForm

/-! Explicit decoded fields needed to connect re-encoding to the logged program. -/
namespace ReexecV3D3.Read
open NearSpec NearSpecV3 NearSpecV3.D2

/-- Refine `encP_good` with the exact state-witness shape and the merged pool
permutation, rather than asserting only the resulting canonical pools. -/
theorem encP_decoded {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2} {X : Pools}
    (C : Ctx cb w sw codes s X) :
    ∃ sw1 codes1 mv, decodeWitnessFile (encP cb sw X) = .ok (sw1, codes1) ∧
      decodeStateWitnessD2 sw1 = .ok (normWV mv X.2 s) ∧
      lenT sw1 ≤ 8388608 ∧ (mv ++ codes1).Perm X.1 := by
  have hQw : ∀ vs ∈ X.2, ValsWf vs := fun vs hv => (C.g2.mem vs hv).wf
  obtain ⟨R, hR⟩ : ∃ R, R = (mainPreRoot cb).getD [] := ⟨_, rfl⟩
  obtain ⟨bc, hbc⟩ : ∃ bc, bc = layout R X.1 := ⟨_, rfl⟩
  have hb : GoodPool bc.1 := C.g1.sub (hbc ▸ layout_sub1 R X.1)
  have hc : GoodPool bc.2 := C.g1.sub (hbc ▸ layout_sub2 R X.1)
  have hbcP : (bc.1 ++ bc.2).Perm X.1 := hbc ▸ layout_perm R X.1
  have hil := concat_implV_sub_le X.2 s.implicit C.iw C.sub.2
  obtain ⟨c1, hr1, hd1, hl1, hst1⟩ := normSWV_spec C.hs hb.wf hQw
  obtain ⟨c2, hr2, hd2, hl2, hst2⟩ := normSWV_spec C.hs (mv := []) ⟨by decide, by simp⟩ hQw
  have hE : encP cb sw X = if lenT c1 ≤ 8388608 then wrapWC c1 bc.2 else wrapWC c2 X.1 := by
    unfold encP
    dsimp only
    rw [← hR, ← hbc, hr1]
    dsimp only
    rw [hr2]
  have hl8 := C.l8
  rw [lenT_eq'] at hl8
  by_cases hle : lenT c1 ≤ 8388608
  · rw [hE, if_pos hle]
    have hle' := hle
    rw [lenT_eq'] at hle'
    have hc1 : c1.length < 4294967296 := by omega
    have hmx : lenT c1 ≤ MAX_WITNESS := by unfold MAX_WITNESS; rw [lenT_eq']; omega
    exact ⟨c1, bc.2, bc.1, decodeWitnessFile_wrapWC c1 bc.2 hc1 hc.wf,
      hd1 hmx, hle, hbcP⟩
  · rw [hE, if_neg hle]
    have h2 : (encTr (trV [] s.main)).length ≤ (encTr s.main).length := by
      rw [encTr_length, encTr_length]
      have e3 : (trV [] s.main).blockHash.length = 32 := zeroHash_length
      have e4 : (trV [] s.main).values = [] := rfl
      have e5 : (trV [] s.main).postStateRoot = s.main.postStateRoot := rfl
      rw [e3, e4, e5, C.mw.1]
      simp only [List.length_nil, List.map_nil, List.foldl_nil]
      omega
    have hle2 : c2.length ≤ sw.length := by omega
    have hc2 : c2.length < 4294967296 := by omega
    have hmx : lenT c2 ≤ MAX_WITNESS := by unfold MAX_WITNESS; rw [lenT_eq']; omega
    refine ⟨c2, X.1, [], decodeWitnessFile_wrapWC c2 X.1 hc2 C.g1.wf,
      hd2 hmx, ?_, List.Perm.refl _⟩
    rw [lenT_eq']
    omega

end ReexecV3D3.Read
