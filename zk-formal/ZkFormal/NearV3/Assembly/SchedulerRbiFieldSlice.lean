import ZkFormal.NearV3.Assembly.SchedulerBranchFieldSlice
import ZkFormal.NearV3.Assembly.SchedulerBranchOutputShape
import ZkFormal.NearV3.Assembly.SchedulerRbiInfo
import ZkFormal.NearV3.Assembly.SchedulerParentChain

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- An actual inserted branch consumes the preceding native fresh-leaf hash at
the correct physical first/last digest window. -/
theorem traceUpsert_rbi_field_slice {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    {k : Nat} {a b : TreePart} (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hk : b.kind=.RBI) {base Q : UpsPartI} (he : encodeTreePart base b=some Q)
    (I : UpsInst) (hts : I.ts=run.splitCursor [0,15]) :
    ((nodeEnc b.output).drop ((if Q.ty=2 then 3 else 39)+
      32*(if S15B I Q then nWin Q.shape-1 else 0))).take 32=sha256 (nodeEnc a.output) := by
  obtain ⟨sv,kids,mem,hout,hlen,hwkids,hv⟩:=
    traceUpsert_branch_output_shape hr hw (List.mem_of_getElem? hb) (Or.inr hk)
  let sd:=if I.ts=1 then 0 else 1
  have hs:sd=0∨sd=1:=by unfold sd;split <;> simp_all
  have hslot:b.slot=edgeSlot sd := by
    unfold sd
    rw [hts]
    exact traceUpsert_rbi_side hr (List.mem_of_getElem? hb) hk
  have hc:=traceUpsert_parentChild hr ha hb (by simp [parentDigestKind,hk])
  simp only [outputPathChild,hout] at hc
  rw [hslot] at hc
  have hkind:Q.kind=5:=by rw [encodeTreePart_kind he,hk];rfl
  have hh:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hhash:a.output.hashOf.length=32:=by rw [←hh];simp
  have hsli:=native_branch_field_slice hout he sd hs hlen hwkids hv hc hhash
  by_cases ht:I.ts=1 <;> simpa [S15B,hkind,sd,ht,hh] using hsli

end ZkFormal.NearV3.Assembly
