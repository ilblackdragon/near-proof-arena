import ZkFormal.NearV3.Candidates.ProcBoundaryGroups
import ZkFormal.NearV3.Candidates.ProcComplete
namespace ZkFormal.NearV3.Candidates.ProcLastRow
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcNativeRows ProcEntryPosition

theorem last_cases (R : Run) (hd : ProcData.RunData R) (i : Nat)
    (hi : i+1=(procVs R).length) :
    (i=15 ∧ atRow R i=keyV R 15) ∨
    ∃ rd j,rd∈R.rounds ∧ j<rd.entries.toArray.size ∧ j+1=rd.entries.toArray.size ∧
      atRow R i=entV R rd rd.entries.toArray j := by
  have hlt : i<(procVs R).length := by omega
  rcases ProcPositionCases.active_cases R i hlt with hk | ⟨pre,rd,post,he,hpos⟩
  · have hlen : 16≤(procVs R).length := by rw [procVs_length]; omega
    have hv : i=15 := by omega
    exact Or.inl ⟨hv,by rw [hv]; exact ProcKeyRows.at_key R 15 (by decide)⟩
  · have hmem : rd∈R.rounds := by simp [he]
    have hrd := hd.2.1 rd hmem
    rcases hpos with hp | ⟨j,hj,hp⟩
    · have hn := ProcEntryNative.entry_index_lt R pre post rd he 0 hrd.2.1
      omega
    · right
      have hl : j+1=rd.entries.toArray.size := by
        by_cases hn : j+1=rd.entries.toArray.size
        · exact hn
        have hj' : j+1<rd.entries.toArray.size := by omega
        have hb := ProcEntryNative.entry_index_lt R pre post rd he (j+1) hj'
        omega
      exact ⟨rd,j,hmem,hj,hl,by rw [hp]; exact entry_lookup R pre post rd he j hj⟩

theorem boundary_groups (R S : Run) (hd : ProcData.RunData R) (ht : S.tau=R.tau+1)
    (i : Nat) (hi : i+1=(procVs R).length)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=Fp.ofNat ((atRow R i).cell c))
    (hn : ∀c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval tr t r pub=0 := by
  rcases last_cases R hd i hi with ⟨_,hv⟩ | ⟨rd,j,hmem,hj,hl,hv⟩
  · apply ProcBoundaryGroups.key_groups R S ht tr t r pub _ hn
    simpa only [hv] using hc
  · have hrd := hd.2.1 rd hmem
    apply ProcBoundaryGroups.entry_groups R S rd rd.entries.toArray j hl ht
      (hrd.2.2.2 j hj).1 hrd.2.2.1 (hrd.2.2.2 j hj).2 tr t r pub _ hn
    simpa only [hv] using hc
end ZkFormal.NearV3.Candidates.ProcLastRow
