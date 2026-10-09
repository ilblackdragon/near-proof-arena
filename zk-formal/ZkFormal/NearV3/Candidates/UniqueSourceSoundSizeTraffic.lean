import ZkFormal.NearV3.Candidates.UniqueSourceSoundSize
namespace ZkFormal.NearV3.Candidates.UniqueSourceSoundSizeTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates SrcpV3
open UniqueSourceSoundSize
/-- There is exactly one SIZE send, whose payload is the natural prefix sum cast to Fp. -/
theorem size_traffic {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal (UniqueSourceCharge.table 24) tr tt pub) : ∃ K, 0 < K ∧ K ≤ tr.height tt ∧
    (∀ r, r < K → tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) ∧
    (∀ r, K ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0) ∧
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub B_SIZE true) =
      [Msg.toFp [2, prefixSize tr tt K]] ∧
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub B_SIZE false) = [] := by
  have hl:=UniqueSourceSoundShadow.old_local hL
  obtain ⟨K, hK, hKH, ha, hp⟩ := DedupProof.active_end hl
  change K≤tr.height tt at hKH
  have ha0 : ∀r,r<K→tr.cell tt r rt=1 ∨ tr.cell tt r sg=1 := by
    simpa [UniqueSourceSoundShadow.shadow,Trace.height,rt,sg,sz] using ha
  have hp0 : ∀r,K≤r→r<tr.height tt→tr.cell tt r rt=0 ∧ tr.cell tt r sg=0 := by
    simpa [UniqueSourceSoundShadow.shadow,Trace.height,rt,sg,sz] using hp
  refine ⟨K, hK, hKH, ha0, hp0, ?_, ?_⟩
  · have hrow : ∀ r, r < tr.height tt →
        rowTraffic DedupTable.interactions tr tt r pub B_SIZE true =
          if r = K - 1 then [Msg.toFp [2, prefixSize tr tt K]] else [] := by
      intro r hr
      rw [DedupRender.candidate_rowT]
      simp only [B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, Bool.true_eq_false,
        and_false, false_and, ite_false, List.nil_append, true_and]
      have hg : tr.cell tt r gz=1 ↔ r+1=K := by
        simpa [UniqueSourceSoundShadow.shadow,gz,sz] using DedupProof.size_gate hl hK hKH ha hp hr
      simp only [hg]
      by_cases he : r = K - 1
      · have he' : r + 1 = K := by omega
        rw [if_pos he', if_pos he, prefix_field hL hr, he']
        rfl
      · simp [he, show r + 1 ≠ K by omega]
    rw [flatMap_congr' (fun r hr => hrow r (List.mem_range.mp hr))]
    exact Render.SrcpGen.flatMap_at _ _ _ (by omega)
  · apply List.flatMap_eq_nil_iff.mpr
    intro r _
    rw [DedupRender.candidate_rowT]
    simp [B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC]

end ZkFormal.NearV3.Candidates.UniqueSourceSoundSizeTraffic
