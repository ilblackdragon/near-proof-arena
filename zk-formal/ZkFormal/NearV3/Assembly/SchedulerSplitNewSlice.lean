import ZkFormal.NearV3.Assembly.SchedulerSplitPairWidth
import ZkFormal.NearV3.Assembly.SchedulerSplitSlotFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near

/-- LSa and ESn1's sole new child digest comes from actual output0. Copied
ESn1 child bytes affect its offset but create no additional SHA demand. -/
theorem traceUpsert_split_new_slice {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    {p : TreePart} (hp : p∈run.parts) (hk : p.kind=.SPB)
    (hc : run.terminal=.LSa ∨ run.terminal=.ESn1) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) (hf : FieldsOk Q)
    (hq : Q.q=(nodeEnc p.output).map UInt8.toNat) :
    ∃a,run.parts[0]?=some a ∧
      ((nodeEnc p.output).drop (if run.terminal=.LSa then 39 else
        if run.splitCursor [0,15]=1 then 3 else 35)).take 32=sha256 (nodeEnc a.output) := by
  have hs:=traceUpsert_split_shapes root [0,15] v run hr p hp hk
  have hfacts:=traceUpsert_split_slot_facts root [0,15] v run hr
  have hnew:=splitNewSlotNative_metadata hr (hfacts.1 (by rcases hc with h|h;exact Or.inl h;exact Or.inr (Or.inr (Or.inr h))))
  rcases hc with hc|hc
  · simp only [hc] at hs
    obtain ⟨sv,child,mem,hout,hchild⟩:=hs
    obtain ⟨a,ha,hoa⟩:=Option.map_eq_some_iff.mp hchild
    have hsha:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
    have hh:child.hashOf.length=32:=by rw [←hoa,←hsha];simp
    have hx:splitNewSlotNative run<16:=by rw [hnew];split <;> decide
    have hslice:=split_single_physical_slice hout he hf hq hx hh
    refine ⟨a,ha,?_⟩
    simpa only [hc,ite_true,←hoa,←hsha] using hslice
  · simp only [hc] at hs
    obtain ⟨old,new,mem,hout,hchild⟩:=hs
    obtain ⟨a,ha,hoa⟩:=Option.map_eq_some_iff.mp hchild
    have hsha:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
    have hn:new.hashOf.length=32:=by rw [←hoa,←hsha];simp
    have hd:=hfacts.2 (Or.inr (Or.inr hc))
    rw [hnew] at hout hd
    have hx:splitOldSlot run<16:=by
      rw [splitOldSlot_metadata]
      exact splitNibble_lt (traceUpsert_sources root [0,15] v run hw hr).1
    have htotal:=split_pair_hash_lengths hout he hf hq hx hd
    have ho:old.hashOf.length=32:=by omega
    have hslice:=split_pair_child_slices (run.splitCursor [0,15]) (splitOldSlot run) old new mem hx hd ho hn
    refine ⟨a,ha,?_⟩
    rw [hc,if_neg (by decide),hout]
    by_cases ht:run.splitCursor [0,15]=1
    · simpa only [ht,ite_true,←hoa,←hsha] using hslice.1
    · simpa only [ht,ite_false,←hoa,←hsha] using hslice.2

end ZkFormal.NearV3.Assembly
