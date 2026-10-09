import ZkFormal.NearV3.Assembly.SchedulerSplitSlotFacts
import ZkFormal.NearV3.Assembly.SchedulerSplitHashOrder

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near

/-- LSc/ESn0's two physical digest windows contain the actual moved output0
and fresh output1, in the exact slot order chosen by the scheduler cursor. -/
theorem traceUpsert_split_pair_slices {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    {p : TreePart} (hp : p∈run.parts) (hk : p.kind=.SPB)
    (hc : run.terminal=.LSc ∨ run.terminal=.ESn0) :
    ∃a b,run.parts[0]?=some a ∧ run.parts[1]?=some b ∧
      ((nodeEnc p.output).drop 3).take 32=
        (if run.splitCursor [0,15]=1 then sha256 (nodeEnc b.output) else sha256 (nodeEnc a.output)) ∧
      ((nodeEnc p.output).drop 35).take 32=
        (if run.splitCursor [0,15]=1 then sha256 (nodeEnc a.output) else sha256 (nodeEnc b.output)) := by
  have hshape:=traceUpsert_split_shapes root [0,15] v run hr p hp hk
  have hh : ∃a b m,p.output=.branch none (kids2 (splitOldSlot run) a (splitNewSlotNative run) b) m ∧
      nativePartOutput run 0=some a ∧ nativePartOutput run 1=some b := by
    rcases hc with h|h <;> simpa only [h] using hshape
  obtain ⟨old,new,mem,hout,ha,hb⟩:=hh
  obtain ⟨a,ha,hoa⟩:=Option.map_eq_some_iff.mp ha
  obtain ⟨b,hb,hob⟩:=Option.map_eq_some_iff.mp hb
  have hsha:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hshb:=upsertShaJob_node_digest hr (List.mem_of_getElem? hb)
  have hcases:run.terminal=.LSc ∨ run.terminal=.ESn0 ∨ run.terminal=.ESn1:=by
    rcases hc with h|h;exact Or.inl h;exact Or.inr (Or.inl h)
  have hf:=traceUpsert_split_slot_facts root [0,15] v run hr
  have hnew:=splitNewSlotNative_metadata hr (hf.1 (Or.inr hcases))
  have hd:=hf.2 hcases
  rw [hnew] at hout hd
  have hx:splitOldSlot run<16:=by
    rw [splitOldSlot_metadata]
    exact splitNibble_lt (traceUpsert_sources root [0,15] v run hw hr).1
  have ho:old.hashOf.length=32:=by rw [←hoa,←hsha];simp
  have hn:new.hashOf.length=32:=by rw [←hob,←hshb];simp
  have hs:=split_pair_child_slices (run.splitCursor [0,15]) (splitOldSlot run) old new mem hx hd ho hn
  refine ⟨a,b,ha,hb,?_⟩
  rw [hout]
  simpa only [←hoa,←hob,←hsha,←hshb] using hs

end ZkFormal.NearV3.Assembly
