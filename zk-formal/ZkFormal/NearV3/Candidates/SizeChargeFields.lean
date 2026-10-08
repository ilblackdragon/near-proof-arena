import ZkFormal.NearV3.Candidates.SizeComponents
import ZkFormal.NearV3.Candidates.ChainStoreCharge
namespace ZkFormal.NearV3.Candidates.SizeChargeFields
open ZkFormal.Near Render StoreSelectedCharge SizeComponents

private theorem sum_prefix {α : Type} (xs : List α) (f : α→Nat) :
    (xs.map fun x=>f x+4).sum=(xs.map f).sum+4*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons];omega

theorem value_payload (es : List ValE) (h : ∀e∈es,
    (e.vz=true→e.len=0 ∧ e.bytes=[]) ∧ (e.vz=false→e.bytes.length=e.len ∧ 0<e.len)) :
    ((es.filter fun e=>!e.dup).map fun e=>e.bytes.length).sum=
      ((es.filter fun e=>!e.vz && !e.dup).map ValE.len).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he:=h e (by simp)
    have ht:=ih (fun e he=>h e (by simp [he]))
    cases hd : e.dup <;> cases hz : e.vz
    all_goals simp [hd,hz,he.1,he.2,ht]

theorem fields_charge (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) (hv : ValWf es) :
    (view vs es bs).x0+(view vs es bs).x1+4*((counts vs es).nodes+(counts vs es).values)=
      nodeCharge vs+valueCharge es := by
  unfold nodeCharge valueCharge
  rw [sum_prefix,sum_prefix,value_payload es hv.shape]
  simp only [view,counts]
  omega

/-- The concrete SIZE receiver payload and count columns account for exactly
the actual chain-patched store charge, including empty value records. -/
theorem chain_fields (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeWf3 vs) (hv : ValWf es) (bs : List SrcpB) :
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs tau es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    (view ns vals bs).x0+(view ns vals bs).x1+4*((counts ns vals).nodes+(counts ns vals).values)=
      HonestStoreRepresentatives.charge (StoreClassPartition.keys (CombinedStoreOccurrences.allOccurrences vs tau es)) := by
  dsimp only
  rw [fields_charge _ _ bs (ChainMetadata.value_wf _ es hv
    (StoreClassPartition.combined_metadata vs tau es hn hv).2.1)]
  exact ChainStoreCharge.exact_charge vs tau es hv
private theorem filter_sum_le {α : Type} (xs : List α) (p : α→Bool) (f : α→Nat) :
    ((xs.filter p).map f).sum≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega

/-- SIZE payload omits duplicate records and empty-value marker rows, so it
never exceeds the actual unfiltered node/value serialized bytes. -/
theorem payload_le (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) (hv : ValWf es) :
    (view vs es bs).x0+(view vs es bs).x1≤
      (vs.map (fun s=>(s.v.ser false).length)).sum+(es.map (fun e=>e.bytes.length)).sum := by
  have hn:=filter_sum_le vs (fun s=>!s.dup) (fun s=>(s.v.ser false).length)
  have hh:=filter_sum_le es (fun e=>!e.dup) (fun e=>e.bytes.length)
  rw [value_payload es hv.shape] at hh
  exact Nat.add_le_add hn hh

theorem chain_payload_le (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeWf3 vs) (hv : ValWf es) (bs : List SrcpB) :
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs tau es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    (view ns vals bs).x0+(view ns vals bs).x1≤
      (vs.map (fun s=>(s.v.ser false).length)).sum+(es.map (fun e=>e.bytes.length)).sum := by
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs tau es)
  have hh:=payload_le (ChainMetadata.assign cs 0 vs) (ChainMetadata.assignValues cs es) bs
    (ChainMetadata.value_wf _ es hv (StoreClassPartition.combined_metadata vs tau es hn hv).2.1)
  simpa only [ChainMetadata.assign_bytes,ChainMetadata.assignValues,List.map_map,
    Function.comp_def,ChainMetadata.patchValue] using hh

/-- Native unfolding pays the SIZE base payload under its unchanged 2M cap,
strictly within the existing 3M base-payload limit. -/
theorem native_base (ts : List NearSpec.PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000) (hn : NodeWf3 (Assembly.forestNodes 0 0 0 ts))
    (bs : List SrcpB) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let v:=view (ChainMetadata.assign cs 0 vs) (ChainMetadata.assignValues cs es) bs
    v.x0+v.x1≤3000000 := by
  have hh:=chain_payload_le _ (NativeStoreProvenance.valueTau ts) _ hn
    (NativeValueWf.forest_wf ts hw hb) bs
  have he:=Rcpt.Candidates.forest_occurrence_bytes ts hw
  simp only [Assembly.forestStoreViews] at he
  dsimp only
  omega

/-- Remaining total-budget input is native encoded accounting, not an AIR
slack/constraint assumption: original stores plus source bytes and public overhead. -/
theorem native_valid (ts : List NearSpec.PTrie) (store : Nat→List NearSpec.Bytes)
    (hw : ∀t∈ts,t.wf=true) (hb : Assembly.preBytes ts≤2000000)
    (hn : NodeWf3 (Assembly.forestNodes 0 0 0 ts))
    (hs : ∀p∈ts.zipIdx,Stored (NearSpecV3.mkStore (store p.2)) p.1)
    (pub : List ZkFormal.Algebra.Fp) (bs : List SrcpB)
    (htotal : ovhNat pub+Rcpt.Candidates.DedupRender.size bs+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid pub (view ns vals bs) (counts ns vals) := by
  dsimp only
  refine ⟨native_base ts hw hb hn bs,?_⟩
  let vs:=Assembly.forestNodes 0 0 0 ts
  let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
  have hv:=ChainMetadata.value_wf cs es (NativeValueWf.forest_wf ts hw hb)
    (StoreClassPartition.combined_metadata vs _ es hn (NativeValueWf.forest_wf ts hw hb)).2.1
  have hf:=fields_charge (ChainMetadata.assign cs 0 vs) (ChainMetadata.assignValues cs es) bs hv
  have hc:=ChainStoreCharge.native_charge ts store hw hb hs
  change _+_+_+Rcpt.Candidates.DedupRender.size bs+_≤8388608
  dsimp only [vs,es,cs] at hf
  dsimp only at hc
  omega

end ZkFormal.NearV3.Candidates.SizeChargeFields
