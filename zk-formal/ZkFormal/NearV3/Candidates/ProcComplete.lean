import ZkFormal.NearV3.Candidates.ProcData
import ZkFormal.NearV3.Candidates.ProcPositionCases
import ZkFormal.NearV3.Candidates.ProcEntryHeaderNative
import ZkFormal.NearV3.Candidates.ProcKeyHeaderNative
import ZkFormal.NearV3.Candidates.ProcHeaderPadding
import ZkFormal.NearV3.Candidates.ProcHeaderNative
import ZkFormal.NearV3.Candidates.ProcNonEntry
import ZkFormal.NearV3.Candidates.ProcKeyComplete
import ZkFormal.Near.Extract.Common
namespace ZkFormal.NearV3.Candidates.ProcComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcData ProcHeightBits ProcNativeRows ProcKindHeight ProcEntryPosition

theorem header_all (R : Run) (hd : RunData R) (hrows : (procVs R).length+1≤2^22)
    (t r : Nat) (pub : List Fp) (hr : r<2^22) :
    ∀ e ∈ Proc.cHdr,e.eval (trace R) t r pub=0 := by
  by_cases ha : r<(procVs R).length
  · rcases ProcPositionCases.active_cases R r ha with hk | ⟨pre,rd,post,he,hpos⟩
    · exact ProcKeyHeaderNative.native_key_header R hd.1 r hk t pub
    · have hmem : rd∈R.rounds := by simp [he]
      have hrd := hd.2.1 rd hmem
      rcases hpos with rfl | ⟨i,hi,rfl⟩
      · exact ProcHeaderNative.native_header R pre post rd he hrd.1 hrd.2.1
          (hrd.2.2.2 0 hrd.2.1).2 hrows t pub
      · apply ProcEntryHeaderNative.native_entry_header R pre post rd he _ hrows i hi t pub
        intro next rest hp
        exact hd.2.2 pre rd next rest (by simpa [hp] using he)
  · exact ProcHeaderPadding.native_padding R r t pub (by omega) hr

theorem entry_all (R : Run) (hd : RunData R) (hrows : (procVs R).length+1≤2^22)
    (t r : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cEnt,e.eval (trace R) t r pub=0 := by
  by_cases ha : r<(procVs R).length
  · rcases ProcPositionCases.active_cases R r ha with hk | ⟨pre,rd,post,he,hpos⟩
    · apply ProcNonEntry.constraints R (keyV R r) (Or.inl ⟨r,rfl⟩) (trace R) t r pub
      exact fun c=>ProcKeyRows.key_cell R t r c hk
    · have hmem : rd∈R.rounds := by simp [he]
      have hrd := hd.2.1 rd hmem
      rcases hpos with rfl | ⟨i,hi,rfl⟩
      · apply ProcNonEntry.constraints R (hdrV R rd) (Or.inr (Or.inl ⟨rd,rfl⟩)) (trace R) t _ pub
        intro c
        rw [cell_cast,header_lookup R pre post rd he]
      · exact ProcEntryNative.native_entry R pre post rd he hrd.2.2.1 hrd.2.2.2 hrows i hi t pub
  · apply ProcNonEntry.constraints R (atRow R r) _ (trace R) t r pub (cell_cast R t r)
    right; right
    rw [atRow,dif_neg ha]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem constraints (R : Run) (hd : RunData R) (htau : R.tau=0)
    (hrows : (procVs R).length+1≤2^22) (t r : Nat) (pub : List Fp) (hr : r<2^22) :
    ∀ e ∈ Proc.constraints,e.eval (trace R) t r pub=0 := by
  simp only [Proc.constraints,List.forall_mem_append]
  exact ⟨⟨⟨kind_constraints R htau hrows t r pub hr,
    ProcKeyComplete.key_constraints R t r pub hrows hr⟩,
    header_all R hd hrows t r pub hr⟩,entry_all R hd hrows t r pub⟩

theorem proc_local (R : Run) (hd : RunData R) (htau : R.tau=0)
    (hrows : (procVs R).length+1≤2^22) (t : Nat) (pub : List Fp) :
    TableLocal Proc.table (trace R) t pub := by
  exact ⟨by change 1≤22; decide,by change 22≤22; decide,
    fun r hr=>constraints R hd htau hrows t r pub hr,
    fun r _=>ProcHeightBits.trace_bits R t r pub⟩
end ZkFormal.NearV3.Candidates.ProcComplete
