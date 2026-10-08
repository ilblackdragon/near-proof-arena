import ZkFormal.NearV3.Candidates.NativeQueuePhysicalBytes

namespace ZkFormal.NearV3.Candidates.NativeQueueForestPartition
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Qv
open ZkFormal.Algebra

def remainingBytes (pre : PTrie) (rs : List ReadRequest) (base : Nat) : List Msg :=
  ((NearSpecV3.valsOf pre).zipIdx.filter (fun x=>
    !(rs.any (fun r=>valueIndex pre r.key == some x.2)))).flatMap
      (fun x=>emitAt (base+x.2) 0 (x.1.map UInt8.toNat))

/-- Select or retain each value occurrence, without collapsing duplicate bytes. -/
theorem tree_partition (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) (msg : List Fp) :
    cnt ((queueProviders pre rs tau base).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg+
    cnt (remainingBytes pre rs base) msg=
    cnt (NativeValueByteInventory.requests base (NearSpecV3.valsOf pre)) msg := by
  have hp := List.Perm.flatMap_right
    (fun x : Bytes×Nat=>emitAt (base+x.2) 0 (x.1.map UInt8.toNat))
    (List.filter_append_perm (fun x : Bytes×Nat=>rs.any (fun r=>valueIndex pre r.key == some x.2))
      (NearSpecV3.valsOf pre).zipIdx)
  have hb : ((NearSpecV3.valsOf pre).zipIdx.flatMap
      (fun x=>emitAt (base+x.2) 0 (x.1.map UInt8.toNat)))=
      NativeValueByteInventory.requests base (NearSpecV3.valsOf pre) := by
    have hn := congrArg (List.flatMap seedByteMessages)
      (seedValuesFrom_zipIdx base (NearSpecV3.valsOf pre))
    simp only [List.flatMap_map,seedValue_bytes,
      NativeQueuePhysicalBytes.numbered_eq] at hn
    have he : (seedValuesFrom base (NearSpecV3.valsOf pre)).flatMap seedByteMessages=
        NativeValueByteInventory.requests base (NearSpecV3.valsOf pre) := by
      exact NativeValueByteInventory.seed _ _
    exact hn.symm.trans he
  have hc := (hp.map Msg.toFp).count_eq msg
  simp only [List.flatMap_append,List.map_append,List.count_append] at hc
  rw [hb] at hc
  simpa only [queueProviders,queueSelected,remainingBytes,List.flatMap_map,Function.comp_def,cnt] using hc

def forestRemaining : List (PTrie×List ReadRequest)→Nat→List Msg
  | [],_=>[]
  | (pre,rs)::xs,base=>remainingBytes pre rs base++
      forestRemaining xs (base+(NearSpecV3.valsOf pre).length)

/-- Exact complement of all queue providers in a forest, at arbitrary starting
value offset. This covers implicit prestates with their allocated global IDs. -/
theorem forest_partition (xs : List (PTrie×List ReadRequest)) (tau base : Nat) (msg : List Fp) :
    cnt ((queueForestProviders tau base xs).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg+
    cnt (forestRemaining xs base) msg=
    cnt (NativeValueByteInventory.requests base (forestBytes (xs.map Prod.fst))) msg := by
  induction xs generalizing tau base with
  | nil=>simp [queueForestProviders,forestRemaining,forestBytes,NativeValueByteInventory.requests,cnt]
  | cons x xs ih=>
    rcases x with ⟨pre,rs⟩
    have ht := tree_partition pre rs tau base msg
    have hr := ih (tau+1) (base+(NearSpecV3.valsOf pre).length)
    simp only [queueForestProviders,forestRemaining,List.flatMap_append,cnt,List.map_append,List.count_append,
      List.map_cons,forestBytes,List.flatMap_cons,native_valsOf_eq,NativeValueByteInventory.append] at *
    omega

/-- Full physical queue sends plus explicit unselected forest bytes equal
physical EmptyValue receives for the SAME accepted native MainValues. -/
theorem physical_partition {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    (cs : List StoreDuplicateChain.Entry)
    (hval : Render.ValOk (ChainMetadata.assignValues cs
      (seedValuesFrom 0 (forestBytes (m.pre::steps.map ImplicitStepV3.pre)))))
    (tv : Nat) (pub msg : List Fp) :
    let pres := steps.map ImplicitStepV3.pre
    ZkFormal.Air.tableBusCount Qv.Candidates.CombinedTable.interactions
      (Qv.Candidates.CombinedWalkGen.mixedTrace
        (Qv.Candidates.CombinedWalkGen.plan m.pre v pres (NativeQueueIds.resolve m.pre v pres))
        (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))) 22)
      0 pub B_VBYTES true msg+
    cnt (forestRemaining (queueInputs m.pre v pres) 0) msg=
    ZkFormal.Air.tableBusCount Rcpt.Candidates.EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs
        (seedValuesFrom 0 (forestBytes (m.pre::pres)))) pub) tv pub B_VBYTES false msg := by
  dsimp only
  rw [NativeQueuePhysicalBytes.accepted hk hw hc hm hv v hvalid hreads pub msg,
    NativeValueByteInventory.physical _ cs hval tv pub msg]
  simpa only [queueInputs_pre] using forest_partition (queueInputs m.pre v (steps.map ImplicitStepV3.pre)) 0 0 msg

end ZkFormal.NearV3.Candidates.NativeQueueForestPartition
