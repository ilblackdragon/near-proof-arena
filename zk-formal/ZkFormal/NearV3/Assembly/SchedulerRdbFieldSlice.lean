import ZkFormal.NearV3.Assembly.SchedulerBranchFieldSlice
import ZkFormal.NearV3.Render.Ups.NativeBranchGeometry
import ZkFormal.NearV3.Render.Ups.BranchSideAllocation
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- The actual rebuilt branch's physical first/last window hashes precisely
the preceding native output. Its child widths and selected slot are derived
from source wf and actual execution, with no post-update memory consistency. -/
theorem traceUpsert_rdb_field_slice (recordId : PTrie→Nat)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    {k : Nat} {a b : TreePart} (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hk : b.kind=.RDB) (base : UpsPartI) {Q : UpsPartI}
    (he : encodeTreePart (positionedPart recordId (fdepth root [0,15]-1) run (k+1) b base) b=some Q)
    (I : UpsInst) :
    ((nodeEnc b.output).drop ((if Q.ty=2 then 3 else 39)+
      32*(if S15B I Q then nWin Q.shape-1 else 0))).take 32=sha256 (nodeEnc a.output) := by
  obtain ⟨sv,kids,mem,outKids,outMem,hsrc,hout,_,_,hwout⟩:=
    traceUpsert_branch_geometry hr hw (List.mem_of_getElem? hb) hk 0
  have hside:=positionedPart_branchSide recordId (fdepth root [0,15]-1) hr (k+1) b hb hk base
  have hsd:Q.sd=(positionedPart recordId (fdepth root [0,15]-1) run (k+1) b base).sd :=
    (encodeTreePart_positions he).2.2.1
  have hkind:Q.kind=0:=by rw [encodeTreePart_kind he,hk];rfl
  have hs:Q.sd=0∨Q.sd=1:=by rw [hsd];exact hside.1
  have hslot:b.slot=edgeSlot Q.sd:=by rw [hsd];exact hside.2
  have hc:=traceUpsert_outputChild hr ha hb (Or.inl hk)
  simp only [outputPathChild,hout] at hc
  rw [hslot] at hc
  have hv : ∀s∈sv,s.valueRef.length=36 := by
    cases sv with
    | none=>simp
    | some s=>
      intro x hx
      simp only [Option.mem_some_iff] at hx
      subst x
      have hsw := (traceUpsert_sources root [0,15] v run hw hr).2 b (List.mem_of_getElem? hb)
      rw [hsrc] at hsw
      cases s <;> simp_all [PTrie.wf,slotOk,Slot.valueRef]
  have hh:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hhash:a.output.hashOf.length=32:=by rw [←hh];simp
  have hsli:=native_branch_field_slice hout he Q.sd hs hwout.1 hwout.2.2.1 hv hc hhash
  simpa only [S15B,hkind,Nat.reduceBEq,Bool.true_and,Bool.false_and,Bool.or_false,hh] using hsli

end ZkFormal.NearV3.Assembly
