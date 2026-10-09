import ZkFormal.NearV3.Candidates.ProcConcatGeometry
import ZkFormal.NearV3.Candidates.ProcLastRow
import ZkFormal.NearV3.Candidates.ProcNativeGroups
import ZkFormal.NearV3.Candidates.ProcRowTransport
namespace ZkFormal.NearV3.Candidates.ProcConcatActive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry

theorem block_length (rs pre post : List Run) (R : Run) (he : rs=pre++R::post) :
    (procVs R).length≤(rows rs).length := by simp [rows,he,List.flatMap_append]; omega

theorem block_cell (rs pre post : List Run) (R : Run) (he : rs=pre++R::post)
    (i : Nat) (hi : i<(procVs R).length) (t c : Nat) :
    (trace rs).cell t (start pre+i) c=Fp.ofNat ((ProcNativeRows.atRow R i).cell c) := by
  change Fp.ofNat ((atRow rs (start pre+i)).cell c)=_
  rw [block_lookup rs pre post R he i hi]

theorem internal_groups (rs pre post : List Run) (R : Run) (he : rs=pre++R::post)
    (hd : ProcData.RunData R) (hcap : (rows rs).length+1≤2^22)
    (i : Nat) (hi : i+1<(procVs R).length) (t : Nat) (pub : List Fp) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t (start pre+i) pub=0 := by
  have hlen := block_length rs pre post R he
  have hb := block_lt rs pre post R he (i+1) hi
  apply ProcRowTransport.groups_transport (trace rs) (ProcHeightBits.trace R) t t (start pre+i) i pub
  · intro c
    rw [ProcKindHeight.cell_cast]
    exact block_cell rs pre post R he i (by omega) t c
  · intro c
    change Fp.ofNat ((atRow rs ((start pre+i+1)%(2^22))).cell c)=
      (ProcHeightBits.trace R).cell t ((i+1)%(2^22)) c
    rw [Nat.mod_eq_of_lt (by omega : start pre+i+1<2^22),
      Nat.mod_eq_of_lt (by omega : i+1<2^22),ProcKindHeight.cell_cast]
    have h := block_lookup rs pre post R he (i+1) hi
    rw [show start pre+i+1=start pre+(i+1) by omega,h]
  · exact ProcNativeGroups.groups R hd (by omega) t i pub (by omega)

theorem final_groups (rs pre : List Run) (R : Run) (he : rs=pre++[R])
    (hd : ProcData.RunData R) (hcap : (rows rs).length+1≤2^22)
    (i : Nat) (hi : i+1=(procVs R).length) (t : Nat) (pub : List Fp) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t (start pre+i) pub=0 := by
  have hlen := block_length rs pre [] R he
  have hb := block_lt rs pre [] R he i (by omega)
  apply ProcRowTransport.groups_transport (trace rs) (ProcHeightBits.trace R) t t (start pre+i) i pub
  · intro c
    rw [ProcKindHeight.cell_cast]
    exact block_cell rs pre [] R he i (by omega) t c
  · intro c
    change Fp.ofNat ((atRow rs ((start pre+i+1)%(2^22))).cell c)=
      (ProcHeightBits.trace R).cell t ((i+1)%(2^22)) c
    rw [Nat.mod_eq_of_lt (by omega : start pre+i+1<2^22),
      Nat.mod_eq_of_lt (by omega : i+1<2^22),ProcKindHeight.cell_cast]
    rw [show start pre+i+1=start pre+(procVs R).length by omega,
      after_block rs pre [] R he,hi,ProcRoundBoundary.tail_lookup]
  · exact ProcNativeGroups.groups R hd (by omega) t i pub (by omega)

theorem boundary_groups (rs pre post : List Run) (R S : Run) (he : rs=pre++R::S::post)
    (hd : ProcData.RunData R) (ht : S.tau=R.tau+1) (hcap : (rows rs).length+1≤2^22)
    (i : Nat) (hi : i+1=(procVs R).length) (t : Nat) (pub : List Fp) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t (start pre+i) pub=0 := by
  have hb := block_lt rs pre (S::post) R he i (by omega)
  apply ProcLastRow.boundary_groups R S hd ht i hi (trace rs) t (start pre+i) pub
  · exact block_cell rs pre (S::post) R he i (by omega) t
  · intro c
    change Fp.ofNat ((atRow rs ((start pre+i+1)%(2^22))).cell c)=_
    rw [Nat.mod_eq_of_lt (by omega : start pre+i+1<2^22),
      show start pre+i+1=start pre+(procVs R).length by omega,after_block rs pre (S::post) R he]

theorem active_groups (rs : List Run) (hd : ∀R∈rs,ProcData.RunData R)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (hcap : (rows rs).length+1≤2^22) (r t : Nat) (pub : List Fp) (hr : r<(rows rs).length) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t r pub=0 := by
  obtain ⟨pre,R,post,i,he,hi,rfl⟩ := ProcConcatGeometry.active_cases rs r hr
  have hR := hd R (by simp [he])
  by_cases hn : i+1<(procVs R).length
  · exact internal_groups rs pre post R he hR hcap i hn t pub
  · have hl : i+1=(procVs R).length := by omega
    cases post with
    | nil => exact final_groups rs pre R he hR hcap i hl t pub
    | cons S post => exact boundary_groups rs pre post R S he hR (ht pre R S post he) hcap i hl t pub
end ZkFormal.NearV3.Candidates.ProcConcatActive
