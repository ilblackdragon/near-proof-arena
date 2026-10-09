import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRecord
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFullKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecNativeBytes ProcPriorCodecSideFullKind

theorem inside (I : Input) (R : Run) (present : Bool) (vidV p : Nat) (hp:p<4)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn:R.n≤64) (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present p)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present (p+1))[c]!) (if p=0 then 1 else 0) 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.header_boolean_group I R present vidV _ _ p _ _ _ _
  · apply ProcPriorCodecSidePhase.header_phase I R present vidV _ _ p _ _ _ _ rfl
    by_cases hh:p=0
    · exact Or.inr hh
    · exact Or.inl (ite_eq_right hh)
  · exact ProcPriorCodecSideZero.header_zeros I R present vidV _ _ p (by omega) ht _ _ _ _
  · exact ProcPriorCodecSideCarry.same_instance I R present vidV _ _
      (ProcPriorCodecSideCarry.header_instance I R present vidV _ _ p)
      (ProcPriorCodecSideCarry.header_instance I R present vidV _ _ (p+1)) _ _ _
  · exact ProcPriorCodecSideNext.header_inside I R present vidV _ _ p _ _ _
  · exact ProcPriorCodecNativeBytes.header_bytes I R present vidV p _ _ _ _
  · rw [ProcPriorCodecHeaderFlow.header_decomposition]
    simp only [List.forall_mem_append]
    exact ⟨ProcPriorCodecHeaderInitial.native_initial I R present vidV p hparam hn _ _ _ _,
      ProcPriorCodecHeaderFlow.native_inside I R present vidV p hp _ _ _⟩

theorem to_first_record (I : Input) (R : Run) (present : Bool) (vidV : Nat) (gbA : Array Nat)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn:R.n≤64) (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present 4)[c]!)
      (fun c=>Fp.ofNat (ProcPriorCodecPlainStep.row I R present gbA (instanceCells I R present vidV) 0 0 0)[c]!)
      0 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.header_boolean_group I R present vidV _ _ 4 _ _ _ _
  · exact ProcPriorCodecSidePhase.header_phase I R present vidV _ _ 4 _ _ _ _ rfl (Or.inl rfl)
  · exact ProcPriorCodecSideZero.header_zeros I R present vidV _ _ 4 (by decide) ht _ _ _ _
  · exact ProcPriorCodecSideCarry.same_instance I R present vidV _ _
      (ProcPriorCodecSideCarry.header_instance I R present vidV _ _ 4)
      (ProcPriorCodecHeaderRecord.first_instance I R present gbA vidV) _ _ _
  · apply ProcPriorCodecSideNext.encoded_next
    · rw [(ProcPriorCodecSideMultiplicity.header_flags I R present vidV _ _ 4).2.2.2.1]; rfl
    · rw [(ProcPriorCodecSideZero.header_cells I R present vidV _ _ 4).2.2.2.1,
        ProcPriorCodecHeaderRecord.first_position]
      decide +kernel
  · exact ProcPriorCodecNativeBytes.header_bytes I R present vidV 4 _ _ _ _
  · rw [ProcPriorCodecHeaderFlow.header_decomposition]
    simp only [List.forall_mem_append]
    refine ⟨ProcPriorCodecHeaderInitial.native_initial I R present vidV 4 hparam hn _ _ _ _,?_⟩
    obtain ⟨hR,hg,he,hS,hFR,hA,hk,hend⟩ := ProcPriorCodecPlainAdjacent.cells I R present gbA vidV 0 0 0 (by decide)
    apply ProcPriorCodecHeaderFlow.native_end
    · rw [hS]; rfl
    · rw [hk]; rfl
    · rw [hg]; rfl
    · rw [ProcPriorCodecHeaderRecord.first_rs]; rfl

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFullKind
