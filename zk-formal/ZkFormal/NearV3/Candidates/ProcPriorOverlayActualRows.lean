import ZkFormal.NearV3.Candidates.ProcPriorOverlayActualExprs
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayActualRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem source_zero (T : Air.Table) (hT:T∈ProcPriorCodecActualFamily.components)
    (tr : Trace Fp) (r : Nat) (hz:tr.cell 0 r=fun _=>0) (bus : Nat) (sd : Bool) :
    rowTraffic T.interactions tr 0 r [] bus sd=[] := by
  rw [traffic_row]
  apply ProcPriorOverlayTrafficRows.traffic_zero
  intro a ha e he
  have hh:=ProcPriorOverlayActualExprs.padding T hT (tr.cell 0 ((r+1)%tr.height 0))
    (if r=0 then 1 else 0) (if r+1=tr.height 0 then 1 else 0)
    (if r+1=tr.height 0 then 0 else 1) a ha e he
  have heq:rowEnv tr 0 r []=ProcPriorCells.env (fun _=>0)
      (tr.cell 0 ((r+1)%tr.height 0)) (if r=0 then 1 else 0)
      (if r+1=tr.height 0 then 1 else 0) (if r+1=tr.height 0 then 0 else 1):=by
    simp only [rowEnv,ProcPriorCells.env,hz]
    congr 1
    funext c nx
    cases nx <;> simp [hz]
  rwa [heq]

theorem boundary (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i r t : Nat) (hi4:i<4)
    (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (hz:(source i).cell 0 (r-start bs i)=fun _=>0)
    (pub : List Fp) (T : Air.Table) (hT:T∈ProcPriorCodecActualFamily.components)
    (bus : Nat) (sd : Bool) :
    rowTraffic (T.interactions.map (interaction i))
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=[] := by
  rw [traffic_row]
  have hm:(rowEnv (trace bs (fun n=>(source n).cell 0)) t r pub).col (stage i) false=1:=by
    have hh:=ProcPriorOverlayLocal.stage_eval bs source t r i hi4 pub
    rw [hi,ite_eq_left rfl] at hh
    exact hh
  rw [active_traffic T.interactions _ i bus sd hm rfl]
  apply ProcPriorOverlayTrafficRows.traffic_zero
  intro a ha e he
  rw [←expression_eval]
  have hb:=ProcPriorOverlayActualExprs.bounds T hT e
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_append_left _ he⟩))
  change (expression e).eval (trace bs (fun n=>(source n).cell 0)) t r pub=0
  rw [ProcPriorOverlayDataTransport.translated bs _ t r pub e hb.1 hb.2]
  have hg:=position bs hc (fun n=>(source n).cell 0) r hr
  dsimp only at hg
  rw [hi] at hg
  obtain ⟨hstart,hstop,hmax,hd,hf,hl,hn⟩:=hg
  rw [hd,hf,hl,hz]
  exact ProcPriorOverlayActualExprs.padding T hT _ _ _ _ a ha e he

theorem component (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i r t : Nat) (hi4:i<4) (hlog:(source i).log 0=22)
    (used : Nat) (hused:used<stop bs i-start bs i)
    (hz:∀j,used≤j→(source i).cell 0 j=fun _=>0) (hr:r<2^22)
    (pub : List Fp) (T : Air.Table) (hT:T∈ProcPriorCodecActualFamily.components)
    (bus : Nat) (sd : Bool) :
    rowTraffic (T.interactions.map (interaction i))
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=
      if i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r then
        rowTraffic T.interactions (source i) 0 (r-start bs i) [] bus sd else [] := by
  by_cases hi:i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r
  · rw [ite_eq_left hi]
    have hg:=position bs hc (fun n=>(source n).cell 0) r hr
    dsimp only at hg
    rw [←hi] at hg
    by_cases hend:r+1<stop bs i
    · exact ProcPriorOverlayTrafficRows.interior bs hc source i r t hi4 hlog hr hi.symm hend pub
        T.interactions (fun a ha e he=>ProcPriorOverlayActualExprs.bounds T hT e
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,he⟩))) bus sd
    · have he:(source i).cell 0 (r-start bs i)=fun _=>0:=hz _ (by omega)
      rw [boundary bs hc source i r t hi4 hr hi.symm he pub T hT bus sd,
        source_zero T hT (source i) _ he bus sd]
  · rw [ite_eq_right hi]
    exact ProcPriorOverlayTrafficRows.inactive bs source i r t hi4 hi pub T.interactions bus sd
end ZkFormal.NearV3.Candidates.ProcPriorOverlayActualRows
