import ZkFormal.NearV3.Assembly.SchedulerFreshDigestWindow
import ZkFormal.NearV3.Render.Ups.NativePrefixMetadata

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen

/-- A native fresh value occurs at the exact physical leaf/branch field offset,
including the full-u32 variable hex-prefix header. -/
theorem native_fresh_field_slice {p : TreePart} {v : Bytes} {base Q : UpsPartI}
    (hv : outputValue p.output=some (.val v)) (he : encodeTreePart base p=some Q) :
    ((nodeEnc p.output).drop (if Q.ty=0 then 9+Q.qhk else 5)).take 32=sha256 v := by
  have ht:=encodeTreePart_type he
  have hq:=(encodeTreePart_prefix he).1
  cases ho:p.output with
  | hash h=>simp [outputValue,ho] at hv
  | ext key child mem=>simp [outputValue,ho] at hv
  | leaf key slot mem=>
    simp only [outputValue,ho,Option.some.injEq] at hv
    subst slot
    simp only [ho,nativeNodeType] at ht
    simp only [ho,nativeHplen] at hq
    rw [ht,if_pos rfl,hq]
    simpa only [u32_len,ZkFormal.Near.Render.NodeInfo.hexPrefix_len,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.reduceAdd]
      using leaf_value_digest_window key v mem
  | branch slot kids mem=>
    simp only [outputValue,ho] at hv
    subst slot
    simp only [ho,nativeNodeType] at ht
    rw [ht,if_neg (by decide)]
    simpa only [u32_len,Nat.reduceAdd] using branch_value_digest_window v kids mem

/-- Native execution discharges the fresh-value slot premise for every actual
fresh value consumer, including split branches and newly inserted leaves. -/
theorem traceUpsert_fresh_field_slice {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) {p : TreePart} (hp : p∈run.parts)
    (hf : freshDigestKind run.terminal p.kind=true) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) :
    ((nodeEnc p.output).drop (if Q.ty=0 then 9+Q.qhk else 5)).take 32=sha256 v :=
  native_fresh_field_slice (traceUpsert_fresh_slots root key v run hr p hp hf) he

end ZkFormal.NearV3.Assembly
