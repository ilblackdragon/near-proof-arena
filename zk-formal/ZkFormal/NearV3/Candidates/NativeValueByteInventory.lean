import ZkFormal.NearV3.Candidates.NativeAccountPreBytes
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestPipeline

namespace ZkFormal.NearV3.Candidates.NativeValueByteInventory
open NearSpec ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen Assembly Rcpt.Candidates

/-- One request per byte at its actual occurrence ID, including duplicate
values. Empty values have no byte requests. -/
def requests : Nat→List Bytes→List ZkFormal.Near.Msg
  | _,[]=>[]
  | i,b::bs=>emitAt i 0 (b.map UInt8.toNat)++requests (i+1) bs

theorem indexed (bs : List Bytes) (i : Nat) :
    requests i bs=(List.range bs.length).flatMap
      (fun j=>emitAt (i+j) 0 ((bs.getD j []).map UInt8.toNat)) := by
  induction bs generalizing i with
  | nil=>rfl
  | cons b bs ih=>
    simp only [requests,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
      List.flatMap_map,List.getD_cons_zero,Nat.add_zero,List.getD_cons_succ]
    rw [ih]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem append (bs cs : List Bytes) (i : Nat) :
    requests i (bs++cs)=requests i bs++requests (i+bs.length) cs := by
  induction bs generalizing i with
  | nil=>simp [requests]
  | cons b bs ih=>simp [requests,ih,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

theorem seed (bs : List Bytes) (i : Nat) :
    valRecvs (seedValuesFrom i bs) B_VBYTES=requests i bs := by
  induction bs generalizing i with
  | nil=>rfl
  | cons b bs ih=>
    change (if (seedValue i b).vz then [] else
      (List.range (seedValue i b).bytes.length).map (fun p=>[i,p,(seedValue i b).bytes.getD p 0]))++
        valRecvs (seedValuesFrom (i+1) bs) B_VBYTES=_
    rw [ih]
    by_cases hb:b=[]
    · simp [hb,seedValue,requests,emitAt]
    · simp [seedValue,requests,emitAt,List.isEmpty_eq_false_iff.mpr hb]

theorem metadata (cs : List StoreDuplicateChain.Entry) (es : List ValE) :
    valRecvs (ChainMetadata.assignValues cs es) B_VBYTES=valRecvs es B_VBYTES := by
  simp only [valRecvs,ite_true,ChainMetadata.assignValues,List.flatMap_map,ChainMetadata.patchValue]
  rfl

theorem physical (bs : List Bytes) (cs : List StoreDuplicateChain.Entry)
    (hv : Render.ValOk (ChainMetadata.assignValues cs (seedValuesFrom 0 bs)))
    (t : Nat) (pub msg : List Fp) :
    tableBusCount EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs (seedValuesFrom 0 bs)) pub) t pub B_VBYTES false msg=
      cnt (requests 0 bs) msg := by
  rw [show EmptyValue.table.interactions=SizeCount.valTable.interactions++[EmptyValue.emptyInteraction] from rfl]
  rw [EmptyValue.other_counts SizeCount.valTable _ t pub B_VBYTES false msg (Or.inr rfl),
    TrieCountTraffic.value_non_size _ pub t B_VBYTES false msg (by decide),
    ((TrieHeight.value_complete _ hv t pub).2.1 B_VBYTES msg).2]
  change cnt (valRecvs _ B_VBYTES) msg=_
  rw [metadata,seed]

/-- All physical forest byte requests split into actual account sends, untouched
main-state values and every implicit-state value occurrence. The remaining terms
must be supplied by the query/codec/access-key renderers. -/
theorem account_partition {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    {writes : List (List Nat×Bytes)}
    (hkeys : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (h : NodePostUpdate.nativeAccountViews pre post rs=some as)
    (ts : List PTrie) (cs : List StoreDuplicateChain.Entry)
    (hv : Render.ValOk (ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes (pre::ts)))))
    (tr : Trace Fp) (ta tv : Nat) (pub msg : List Fp)
    (ht : TableTraffic AccountEmpty.table.interactions tr ta pub (acctV3Traffic as)) :
    tableBusCount AccountEmpty.table.interactions tr ta pub B_VBYTES true msg+
      cnt (((List.range (NearSpecV3.valsOf pre).length).filter
        (fun i=>!(decide (i∈NodePostUpdate.writtenValueIds pre writes)))).flatMap
          (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg+
      cnt (requests (NearSpecV3.valsOf pre).length (forestBytes ts)) msg=
    tableBusCount EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes (pre::ts)))) pub)
      tv pub B_VBYTES false msg := by
  rw [physical _ cs hv tv pub msg]
  have he : forestBytes (pre::ts)=NearSpecV3.valsOf pre++forestBytes ts := by
    rw [Assembly.native_valsOf_eq]
    rfl
  rw [he,append]
  have ha:=NativeAccountPreBytes.physical_partition hkeys h tr ta pub msg ht
  have hi:=indexed (NearSpecV3.valsOf pre) 0
  simp only [Nat.zero_add] at hi ⊢
  rw [hi]
  simp only [cnt,List.map_append,List.count_append] at ha ⊢
  omega

end ZkFormal.NearV3.Candidates.NativeValueByteInventory
