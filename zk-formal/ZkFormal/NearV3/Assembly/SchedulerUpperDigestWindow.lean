import ZkFormal.NearV3.Assembly.NativeSerializedDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec ZkFormal.Near Render.UpsGen

/-- Actual rebuilt extension/branch parents contain precisely the preceding
native SHA job's digest. Serialization and hash identity both follow from
runtime outputs, including modular-memory outputs that need not be wf. -/
theorem traceUpsert_upper_digest_window {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b) (hu : upperKind b.kind) :
    ∃offset,((nodeEnc b.output).drop offset).take 32=sha256 (nodeEnc a.output) := by
  have hc:=traceUpsert_outputChild hr ha hb hu
  have hh:=upsertShaJob_node_digest hr (List.mem_of_getElem? ha)
  have hlen : a.output.hashOf.length=32 := by rw [←hh];exact ArenaCore.sha256_length _
  cases he : b.output with
  | hash h=>simp [outputPathChild,he] at hc
  | leaf key slot mem=>simp [outputPathChild,he] at hc
  | ext key child mem=>
    simp only [outputPathChild,he,Option.some.injEq] at hc
    subst child
    refine ⟨1+(u32 (hexPrefix key false).length).length+(hexPrefix key false).length,?_⟩
    rw [extension_digest_window _ _ _ hlen,hh]
  | branch val kids mem=>
    simp only [outputPathChild,he] at hc
    refine ⟨(branchHashPrefix val kids).length+childHashOffset kids b.slot,?_⟩
    rw [branch_child_digest_window _ _ _ _ _ hc hlen,hh]

end ZkFormal.NearV3.Assembly
