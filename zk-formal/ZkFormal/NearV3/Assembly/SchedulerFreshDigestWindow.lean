import ZkFormal.NearV3.Assembly.SchedulerFreshSlots

namespace ZkFormal.NearV3.Assembly
open NearSpec Render.UpsGen

/-- Every fresh value request in the native plan names the digest of the SAME
inserted bytes at an actual serialized leaf/branch window. No caller-supplied
hash identity or final-output wf hypothesis is needed. -/
theorem traceUpsert_fresh_digest_window {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {p : TreePart} (hp : p∈run.parts)
    (hf : freshDigestKind run.terminal p.kind=true) :
    ∃offset,((nodeEnc p.output).drop offset).take 32=sha256 value := by
  have hv:=traceUpsert_fresh_slots root key value run hr p hp hf
  cases he:p.output with
  | hash h=>simp [outputValue,he] at hv
  | ext key c mem=>simp [outputValue,he] at hv
  | leaf key slot mem=>
    simp only [outputValue,he,Option.some.injEq] at hv
    subst slot
    exact ⟨1+(u32 (hexPrefix key true).length).length+(hexPrefix key true).length+
      (u32 value.length).length,leaf_value_digest_window key value mem⟩
  | branch slot kids mem=>
    simp only [outputValue,he] at hv
    subst slot
    exact ⟨1+(u32 value.length).length,branch_value_digest_window value kids mem⟩

end ZkFormal.NearV3.Assembly
