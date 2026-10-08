import ZkFormal.NearV3.Assembly.SchedulerNativeDigests
import ZkFormal.NearV3.Render.Ups.TreeOutputChain

namespace ZkFormal.NearV3.Assembly
open NearSpec ZkFormal.Near Render.UpsGen

/-- The digest of each indexed output part is the concrete job at that same
index. This holds without requiring the updated native memory to fit u64. -/
theorem upsert_part_digest {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (tau : Nat) {k : Nat} {p : TreePart}
    (hp : run.parts[k]?=some p) :
    (upsertShaJobs tau value run)[k+1]?=some (upsertShaJob tau (k+1) (nodeEnc p.output)) ∧
    Sha.Gen.expectedDigests [upsertShaJob tau (k+1) (nodeEnc p.output)]=
      [digMsg (upsertJobId tau (k+1)) (nodeEnc p.output).length (p.output.hashOf.map UInt8.toNat)] := by
  constructor
  · rw [upsertShaJobs_part,hp];rfl
  · have hh:=upsertShaJob_node_digest hr (List.mem_of_getElem? hp)
    simp only [Sha.Gen.expectedDigests,upsertShaJob,List.filter_cons_of_pos,List.filter_nil,
      List.map_cons,List.map_nil,List.length_map,nativeBytes_roundtrip,hh]
    rfl

/-- Each rebuilt proper ancestor embeds the immediately preceding native
output and its exact SHA digest. Extension and selected branch-child cases
come from the runtime trace, not a hash-injectivity or flat-trie assumption. -/
theorem upsert_upper_child_digest {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (tau : Nat) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b) (hu : upperKind b.kind) :
    ∃child,outputPathChild b=some child ∧
      (upsertShaJobs tau value run)[k+1]?=some (upsertShaJob tau (k+1) (nodeEnc child)) ∧
      Sha.Gen.expectedDigests [upsertShaJob tau (k+1) (nodeEnc child)]=
        [digMsg (upsertJobId tau (k+1)) (nodeEnc child).length (child.hashOf.map UInt8.toNat)] := by
  exact ⟨a.output,traceUpsert_outputChild hr ha hb hu,upsert_part_digest hr tau ha⟩

end ZkFormal.NearV3.Assembly
