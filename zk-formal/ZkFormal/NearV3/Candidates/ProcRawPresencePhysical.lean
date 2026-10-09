import ZkFormal.NearV3.Candidates.ProcCodecPresenceTraffic
namespace ZkFormal.NearV3.Candidates.ProcRawPresencePhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open NearSpec.Bandwidth ProcPriorRawGen ProcPriorRawSlots

theorem row (st : State) (vid t r : Nat) (present : Bool) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_SPOST false =
      if r=0 then [[0,ProcPriorCells.bit present,Fp.ofNat vid]] else [] := by
  rw [ProcCodecPresenceTraffic.raw_row]
  by_cases hr:r<length st.links.length
  · rcases coverage st.links.length r hr with ⟨g,hg,rfl,he⟩|⟨j,g,hj,hg,rfl,he⟩|⟨g,hg,rfl,he⟩
    · by_cases hz:r=0
      · subst r; simp [trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,
          ProcPriorRawFrame.tau,ProcPriorRawFrame.present,ProcPriorRawFrame.vid,isHeader,offset]
      · simp [trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,isHeader,offset,hz]
    · simp [trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,isHeader]
    · simp [trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,isHeader]
  · have he:=padding st.links.length r (by omega)
    have hn:r≠0 := by unfold length at hr; omega
    simp [trace,he,cells,ProcPriorRawFrame.first,hn]

theorem singleton_range {α : Type} (N : Nat) (hN:0<N) (a : α) :
    (List.range N).flatMap (fun r=>if r=0 then [a] else [])=[a] := by
  cases N with
  | zero => omega
  | succ n =>
    rw [List.range_eq_range',List.range'_succ,List.flatMap_cons]
    simp only [Nat.zero_add,ite_true]
    have hz:(List.range' 1 n).flatMap (fun r=>if r=0 then [a] else [])=[] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      have hh:=List.mem_range'.mp hr
      simp [show r≠0 by omega]
    rw [hz,List.append_nil]

theorem physical (st : State) (vid t : Nat) (present : Bool) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_SPOST false) =
      [[0,ProcPriorCells.bit present,Fp.ofNat vid]] := by
  simp only [row]
  exact singleton_range _ (by decide +kernel) _

theorem count (st : State) (vid t : Nat) (present : Bool) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t pub B_SPOST false msg =
      [[0,ProcPriorCells.bit present,Fp.ofNat vid]].count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical st vid t present pub)
end ZkFormal.NearV3.Candidates.ProcRawPresencePhysical
