import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestSlots
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

mutual
theorem seed_value_digests : ∀ (t : PTrie) (tau d n v : Nat),
    (seedNodesT tau d n v t).flatMap preSlotDigests=valueDigestFrom v (valsOf t)
  | .hash _,_,_,_,_=>rfl
  | .leaf k sl m,tau,d,n,v=>by
    simp [seedNodesT,seed_preSlot,valsOf,occs,ownVals]
  | .ext k child m,tau,d,n,v=>by
    simp only [seedNodesT,List.flatMap_cons,seed_preSlot,ownVals,valueDigestFrom,List.nil_append]
    rw [seed_value_digests]
    rfl
  | .branch sl cs m,tau,d,n,v=>by
    simp only [seedNodesT,List.flatMap_cons,seed_preSlot]
    rw [seed_kid_value_digests]
    exact (valueDigestFrom_append v (optSlotVal sl) ((kOccs cs).flatMap ownVals)).symm

theorem seed_kid_value_digests : ∀ (cs : Kids) (tau d n v : Nat),
    (seedKidsT tau d n v cs).flatMap preSlotDigests=valueDigestFrom v ((kOccs cs).flatMap ownVals)
  | .nil,_,_,_,_=>rfl
  | .none cs,tau,d,n,v=>seed_kid_value_digests cs tau d n v
  | .some child cs,tau,d,n,v=>by
    simp only [seedKidsT,List.flatMap_append]
    rw [seed_value_digests,seed_kid_value_digests]
    simpa only [kOccs,List.flatMap_append,valsOf] using (valueDigestFrom_append v (valsOf child) ((kOccs cs).flatMap ownVals)).symm
end

theorem forest_value_digests (ts : List PTrie) (tau n v : Nat) :
    (forestNodes tau n v ts).flatMap preSlotDigests=valueDigestFrom v (forestBytes ts) := by
  induction ts generalizing tau n v with
  | nil=>rfl
  | cons t ts ih=>
    simp only [forestNodes,List.flatMap_append,seed_value_digests,ih,forestBytes,List.flatMap_cons]
    exact (valueDigestFrom_append v (valsOf t) (ts.flatMap valsOf)).symm

/-- Exact ordered VPRE messages of the actual seeded values, including empties. -/
theorem seeded_value_digests (bs : List Bytes) (v : Nat) :
    EmptyValue.valueDigests (seedValuesFrom v bs)=valueDigestFrom v bs := by
  induction bs generalizing v with
  | nil=>rfl
  | cons b bs ih=>
    simp only [seedValuesFrom,EmptyValue.valueDigests,List.map_cons]
    rw [show List.map (fun e=>ZkFormal.Near.Render.digestMsg ⟨msgId K_VPRE e.vid,e.bytes⟩)
      (seedValuesFrom (v+1) bs)=valueDigestFrom (v+1) bs from ih (v+1)]
    simp [seedValue,ZkFormal.Near.Render.digestMsg,Render.shaN,ZkFormal.Near.Render.ofNats,ZkFormal.Near.Render.toNats,digMsg,valueDigestFrom,List.map_map,Function.comp_def,UInt8.ofNat_toNat]

/-- Arbitrary post updates preserve all VPRE requests. -/
theorem updated_value_digests (u : Inputs) (ts : List PTrie) (tau n v : Nat) :
    (records u (forestNodes tau n v ts)).flatMap preSlotDigests=
      EmptyValue.valueDigests (seedValuesFrom v (forestBytes ts)) := by
  simp only [records,List.flatMap_map,Function.comp_def,update_preSlot]
  rw [forest_value_digests,seeded_value_digests]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
