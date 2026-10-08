import ZkFormal.NearV3.Assembly.SchedulerUpperDigestWindow
import ZkFormal.NearV3.Assembly.SchedulerParentChain
import ZkFormal.NearV3.Assembly.SchedulerFreshFieldSlice

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near

/-- Exact physical extension offset for an actual rebuilt ancestor. The
referenced digest is the preceding output job, with no post-update wf premise. -/
theorem traceUpsert_extension_field_slice {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : b.kind=.RDE ∨ b.kind=.WEX ∨ b.kind=.PT) {base Q : UpsPartI}
    (he : encodeTreePart base b=some Q) :
    ((nodeEnc b.output).drop (5+Q.qhk)).take 32=sha256 (nodeEnc a.output) := by
  have hupper : parentDigestKind b.kind := by
    rcases hu with h|h|h <;> simp [parentDigestKind,h]
  have hc:=traceUpsert_parentChild hr ha hb hupper
  have hh:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hlen:a.output.hashOf.length=32:=by rw [←hh];exact ArenaCore.sha256_length _
  have ht:=(trace_encoded_typeFacts hr (List.mem_of_getElem? hb) he).tyExt
  have hkind:=encodeTreePart_kind he
  have hty:Q.ty=1 := by
    apply ht
    rcases hu with hu|hu|hu <;> rw [hkind,hu] <;> simp [UpsRows.UKind.ix]
  have hnt:=encodeTreePart_type he
  have hq:=(encodeTreePart_prefix he).1
  cases ho:b.output with
  | hash h=>simp [ho,nativeNodeType] at hnt;omega
  | leaf key slot mem=>simp [ho,nativeNodeType] at hnt;omega
  | branch slot kids mem=>cases slot <;> simp [ho,nativeNodeType] at hnt <;> omega
  | ext key child mem=>
    simp only [outputPathChild,ho,Option.some.injEq] at hc
    subst child
    simp only [ho,nativeHplen] at hq
    rw [hq,hh]
    simpa only [u32_len,ZkFormal.Near.Render.NodeInfo.hexPrefix_len,Nat.reduceAdd]
      using extension_digest_window key a.output mem hlen

end ZkFormal.NearV3.Assembly
