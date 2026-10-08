import ZkFormal.NearV3.Assembly.SchedulerSplitSingleSlice
import ZkFormal.NearV3.Assembly.SchedulerSplitSlotFacts
import ZkFormal.NearV3.Assembly.SchedulerFreshFieldSlice

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near

/-- Both payloads in LSb/ESl0 are tied to actual jobs: fresh value0 and the
moved leaf/extension output1, with exact physical byte offsets5 and39. -/
theorem traceUpsert_split_moved_slices {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    {p : TreePart} (hp : p∈run.parts) (hk : p.kind=.SPB)
    (hc : run.terminal=.LSb ∨ run.terminal=.ESl0) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) (hf : FieldsOk Q)
    (hq : Q.q=(nodeEnc p.output).map UInt8.toNat) :
    ∃a,run.parts[0]?=some a ∧
      ((nodeEnc p.output).drop 5).take 32=sha256 v ∧
      ((nodeEnc p.output).drop 39).take 32=sha256 (nodeEnc a.output) := by
  have hshape:=traceUpsert_split_shapes root [0,15] v run hr p hp hk
  have hshape' : ∃sv child mem,p.output=.branch (some sv) (kids1 (splitOldSlot run) child) mem ∧
      nativePartOutput run 0=some child := by
    rcases hc with h|h <;> simpa only [h] using hshape
  obtain ⟨sv,child,mem,hout,hchild⟩:=hshape'
  obtain ⟨a,ha,houta⟩:=Option.map_eq_some_iff.mp hchild
  have hhash:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hx:splitOldSlot run<16:=by
    rw [splitOldSlot_metadata]
    exact splitNibble_lt (traceUpsert_sources root [0,15] v run hw hr).1
  have hh:child.hashOf.length=32:=by rw [←houta,←hhash];simp
  have h39:=split_single_physical_slice hout he hf hq hx hh
  have h5:=traceUpsert_fresh_field_slice hr hp (by rcases hc with h|h <;> simp [freshDigestKind,hk,h]) he
  have ht:Q.ty=3:=by simpa [hout,nativeNodeType] using encodeTreePart_type he
  refine ⟨a,ha,?_,?_⟩
  · simpa only [ht,show ¬(3=0) by decide,ite_false] using h5
  · rw [←houta,←hhash] at h39
    exact h39

end ZkFormal.NearV3.Assembly
