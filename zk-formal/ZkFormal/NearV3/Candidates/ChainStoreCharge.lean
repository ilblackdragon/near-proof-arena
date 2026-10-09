import ZkFormal.NearV3.Candidates.ChainDuplicateFlags
namespace ZkFormal.NearV3.Candidates.ChainStoreCharge
open ZkFormal.Near StoreDuplicateMetadata CombinedStoreOccurrences StoreClassPartition StoreSelectedCharge

theorem assign_map (cs : List StoreDuplicateChain.Entry) (n : Nat) (vs : List NodeS3) :
    ChainMetadata.assign cs n vs=(vs.zipIdx n).map (fun p=>ChainMetadata.patch cs p.2 p.1) := by
  induction vs generalizing n with
  | nil => rfl
  | cons s ss ih => simp [ChainMetadata.assign,List.zipIdx_cons,ih]

theorem node_charge (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    nodeCharge (ChainMetadata.assign (chain (allOccurrences vs tau es)) 0 vs)=
    nodeCharge (assign (allOccurrences vs tau es) 0 vs) := by
  let rs:=allOccurrences vs tau es
  have hn:=StoreSelectedClasses.combined_ids vs tau es hv
  have he : (ChainMetadata.assign (chain rs) 0 vs).map (fun s=>(s.dup,(s.v.ser false).length))=
      (assign rs 0 vs).map (fun s=>(s.dup,(s.v.ser false).length)) := by
    rw [assign_map,StoreSelectedCounts.assign_map]
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hr : (⟨nodeKey p.1,eidN p.2⟩ : Occurrence)∈rs :=
      List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have hd:=ChainDuplicateFlags.metadata_dup rs hn _ hr
    simpa [Function.comp_def,ChainMetadata.patch,patch] using congrArg
      (fun b=>(b,(p.1.v.ser false).length)) hd
  have hh:=congrArg (fun xs : List (Bool×Nat)=>
    ((xs.filter fun x=>!x.1).map fun x=>x.2+4).sum) he
  simpa [nodeCharge,List.filter_map,List.map_map,Function.comp_def] using hh

theorem value_charge (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    valueCharge (ChainMetadata.assignValues (chain (allOccurrences vs tau es)) es)=
    valueCharge (ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es) := by
  let rs:=allOccurrences vs tau es
  have hn:=StoreSelectedClasses.combined_ids vs tau es hv
  have he : (ChainMetadata.assignValues (chain rs) es).map (fun e=>(e.dup,e.bytes.length))=
      (ValueDuplicateMetadata.assign rs tau es).map (fun e=>(e.dup,e.bytes.length)) := by
    simp only [ChainMetadata.assignValues,ValueDuplicateMetadata.assign,List.map_map]
    apply List.map_congr_left
    intro e he
    have hr : (⟨(tau e,toBytes e.bytes),eidV e⟩ : Occurrence)∈rs :=
      List.mem_append_right _ (List.mem_map.mpr ⟨e,he,rfl⟩)
    have hd:=ChainDuplicateFlags.metadata_dup rs hn _ hr
    simpa [Function.comp_def,ChainMetadata.patchValue,ValueDuplicateMetadata.patch] using congrArg
      (fun b=>(b,e.bytes.length)) hd
  have hh:=congrArg (fun xs : List (Bool×Nat)=>
    ((xs.filter fun x=>!x.1).map fun x=>x.2+4).sum) he
  simpa [valueCharge,List.filter_map,List.map_map,Function.comp_def] using hh

/-- The actual predecessor-chain record patches retain exactly the checked
native class charge, including four-byte prefixes and empty value records. -/
theorem exact_charge (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    nodeCharge (ChainMetadata.assign (chain (allOccurrences vs tau es)) 0 vs)+
      valueCharge (ChainMetadata.assignValues (chain (allOccurrences vs tau es)) es)=
    HonestStoreRepresentatives.charge (keys (allOccurrences vs tau es)) := by
  rw [node_charge vs tau es hv,value_charge vs tau es hv]
  exact StoreSelectedCharge.exact_charge vs tau es hv
/-- Native stores pay the actual chain-patched node/value records under the
unchanged unfolding cap. Validity and byte provenance are derived. -/
theorem native_charge (ts : List NearSpec.PTrie) (store : Nat→List NearSpec.Bytes)
    (hw : ∀t∈ts,t.wf=true) (hb : Assembly.preBytes ts≤2000000)
    (hs : ∀p∈ts.zipIdx,Stored (NearSpecV3.mkStore (store p.2)) p.1) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let tau:=NativeStoreProvenance.valueTau ts
    let cs:=chain (allOccurrences vs tau es)
    nodeCharge (ChainMetadata.assign cs 0 vs)+valueCharge (ChainMetadata.assignValues cs es)≤
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store) := by
  dsimp only
  rw [node_charge _ _ _ (NativeValueWf.forest_wf ts hw hb),
    value_charge _ _ _ (NativeValueWf.forest_wf ts hw hb)]
  exact NativeValueWf.forest_charge ts store hw hb hs

end ZkFormal.NearV3.Candidates.ChainStoreCharge
