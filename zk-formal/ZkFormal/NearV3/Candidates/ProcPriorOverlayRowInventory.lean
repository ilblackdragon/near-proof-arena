import ZkFormal.NearV3.Candidates.ProcPriorOverlayActualRows
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayRowInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem flat_row (iss : List (List Interaction)) (tr : Trace Fp)
    (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic iss.flatten tr t r pub bus sd=
      iss.flatMap (fun is=>rowTraffic is tr t r pub bus sd) := by
  induction iss with
  | nil=>rfl
  | cons is iss ih=>simpa only [List.flatten_cons,rowTraffic,List.flatMap_append,List.flatMap_cons] using congrArg (fun x=>rowTraffic is tr t r pub bus sd++x) ih

theorem row (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (used : Nat→Nat)
    (hs:∀T i,(T,i)∈ProcPriorCodecActualFamily.components.zipIdx→
      (source i).log 0=22 ∧ used i<stop bs i-start bs i ∧
      ∀j,used i≤j→(source i).cell 0 j=fun _=>0)
    (r t : Nat) (hr:r<2^22) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic ProcPriorCodecActualFamily.overlay.interactions
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd=
      ProcPriorCodecActualFamily.components.zipIdx.flatMap (fun (T,i)=>
        if i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r then
          rowTraffic T.interactions (source i) 0 (r-start bs i) [] bus sd else []) := by
  change rowTraffic (ProcPriorCodecActualFamily.components.zipIdx.flatMap
    (fun (T,i)=>T.interactions.map (interaction i))) _ t r pub bus sd=_
  simp only [rowTraffic,List.flatMap_assoc]
  apply flatMap_congr'
  intro q hq
  rcases q with ⟨T,i⟩
  have ht:=List.mk_mem_zipIdx_iff_getElem?.mp hq
  have hT:=List.mem_of_getElem? ht
  have hi:i<4:=by
    have hh:=(List.getElem?_eq_some_iff.mp ht).1
    exact hh
  obtain ⟨hl,hu,hz⟩:=hs T i hq
  exact ProcPriorOverlayActualRows.component bs hc source i r t hi hl (used i) hu hz hr pub T hT bus sd
theorem select (bs : List NativeBlock) (source : Nat→Trace Fp) (r bus : Nat) (sd : Bool) :
    ProcPriorCodecActualFamily.components.zipIdx.flatMap (fun (T,i)=>
      if i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r then
        rowTraffic T.interactions (source i) 0 (r-start bs i) [] bus sd else [])=
    let f:=fun i j=>rowTraffic (ProcPriorCodecActualFamily.components[i]!).interactions (source i) 0 j [] bus sd
    if r<cutMemory bs then f 0 r else if r<cutIds bs then f 1 (r-cutMemory bs)
    else if r<cutRaw bs then f 2 (r-cutIds bs) else f 3 (r-cutRaw bs) := by
  dsimp only
  by_cases h0:r<cutMemory bs
  · simp [stageAt,h0,ProcPriorCodecActualFamily.components,components,start]
  · by_cases h1:r<cutIds bs
    · simp [stageAt,h0,h1,ProcPriorCodecActualFamily.components,components,start]
    · by_cases h2:r<cutRaw bs
      · simp [stageAt,h0,h1,h2,ProcPriorCodecActualFamily.components,components,start]
      · simp [stageAt,h0,h1,h2,ProcPriorCodecActualFamily.components,components,start]
end ZkFormal.NearV3.Candidates.ProcPriorOverlayRowInventory
