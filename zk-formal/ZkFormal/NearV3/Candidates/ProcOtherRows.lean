import ZkFormal.NearV3.Candidates.ProcKeyLast
namespace ZkFormal.NearV3.Candidates.ProcOtherRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows

def NonKey (V : PV) : Prop := V.kK=0 ∧ V.kc=0 ∧ V.kl=0 ∧ V.ikc=Gen.Proc.ikcPad

theorem rounds_nonkey (R : Run) : ∀ V ∈ R.rounds.flatMap (roundVs R),
    NonKey V ∧ (∀ i,V.L i=keyLimb R.seed (i%16)) := by
  intro V hv
  obtain ⟨rd,hrd,hv⟩ := List.mem_flatMap.1 hv
  simp only [roundVs,List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact ⟨⟨rfl,rfl,rfl,rfl⟩,fun _=>rfl⟩
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,fun _=>rfl⟩

theorem active_other (R : Run) (r : Nat) (hr : 16≤r) (ha : r<(procVs R).length) :
    atRow R r ∈ R.rounds.flatMap (roundVs R) := by
  rw [atRow,dif_pos ha]
  unfold procVs at ha ⊢
  rw [List.getElem_append_right (by simpa [keyVs] using hr)]
  apply List.getElem_mem

theorem at_nonkey (R : Run) (r : Nat) (hr : 16≤r) : NonKey (atRow R r) := by
  by_cases ha : r<(procVs R).length
  · exact (rounds_nonkey R _ (active_other R r hr ha)).1
  · rw [atRow,dif_neg ha]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem at_register (R : Run) (r : Nat) (hr : 16≤r) (ha : r≤(procVs R).length) :
    ∀ i,(atRow R r).L i=keyLimb R.seed (i%16) := by
  by_cases hb : r<(procVs R).length
  · exact (rounds_nonkey R _ (active_other R r hr hb)).2
  · have he : r=(procVs R).length := by omega
    rw [atRow,dif_neg hb,if_pos he]
    intro i
    rfl

theorem inactive_kinds (R : Run) (r : Nat) (hr : (procVs R).length≤r) :
    (atRow R r).kH=0 ∧ (atRow R r).kE=0 := by
  rw [atRow,dif_neg (by omega)]
  split <;> exact ⟨rfl,rfl⟩
end ZkFormal.NearV3.Candidates.ProcOtherRows
