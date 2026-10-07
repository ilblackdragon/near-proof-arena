import ZkFormal.NearV3.Assembly.UpsertShaEncoding
import ZkFormal.NearV3.Render.Ups.TreeOutputLinks

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem upsertShaJobs_digest {tau : Nat} {v : Bytes} {run : TreeRun}
    {M : ZkFormal.Sha.Gen.Msg} (hm : M∈upsertShaJobs tau v run) :
    [M.id,M.bytes.length]++(sha256 (M.bytes.map UInt8.ofNat)).map UInt8.toNat ∈
      ZkFormal.Sha.Gen.expectedDigests (upsertShaJobs tau v run) := by
  apply List.mem_map.mpr
  exact ⟨M,List.mem_filter.mpr ⟨hm,(upsertShaJobs_bytes hm).1⟩,rfl⟩

theorem upsertShaJobs_value_digest (tau : Nat) (v : Bytes) (run : TreeRun) :
    [upsertJobId tau 0,v.length]++(sha256 v).map UInt8.toNat ∈
      ZkFormal.Sha.Gen.expectedDigests (upsertShaJobs tau v run) := by
  have h := upsertShaJobs_digest (List.mem_of_getElem? (upsertShaJobs_value tau v run))
  simpa [upsertShaJob,Function.comp_def] using h

theorem upsertShaJobs_part_digest {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (tau i : Nat) {p : TreePart}
    (hp : run.parts[i]?=some p) :
    [upsertJobId tau (i+1),(nodeEnc p.output).length]++p.output.hashOf.map UInt8.toNat ∈
      ZkFormal.Sha.Gen.expectedDigests (upsertShaJobs tau v run) := by
  have hg : (upsertShaJobs tau v run)[i+1]?=some (upsertShaJob tau (i+1) (nodeEnc p.output)) := by
    rw [upsertShaJobs_part,hp]; rfl
  have hd := upsertShaJobs_digest (List.mem_of_getElem? hg)
  simpa [upsertShaJob,Function.comp_def,upsertShaJob_node_digest hr (List.mem_of_getElem? hp)] using hd

/-- Last allocated node job is exactly the native upsert's new root preimage. -/
theorem upsertShaJobs_root {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (tau : Nat) :
    (upsertShaJobs tau v run)[run.parts.length]?=
      some (upsertShaJob tau run.parts.length (nodeEnc run.output)) := by
  obtain ⟨p,hp,ho⟩ := Option.map_eq_some_iff.mp (traceUpsert_rootOutput hr)
  have hmem := List.mem_of_getLast? hp
  have hn : 0<run.parts.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
  rw [List.getLast?_eq_getElem?] at hp
  have hj := upsertShaJobs_part tau v run (run.parts.length-1)
  rw [hp] at hj
  have hi : run.parts.length-1+1=run.parts.length := by omega
  simpa [hi,ho] using hj

theorem upsertShaJobs_root_digest {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (tau : Nat) :
    [upsertJobId tau run.parts.length,(nodeEnc run.output).length]++run.output.hashOf.map UInt8.toNat ∈
      ZkFormal.Sha.Gen.expectedDigests (upsertShaJobs tau v run) := by
  obtain ⟨p,hp,ho⟩ := Option.map_eq_some_iff.mp (traceUpsert_rootOutput hr)
  have hmem := List.mem_of_getLast? hp
  have hn : 0<run.parts.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
  rw [List.getLast?_eq_getElem?] at hp
  have h := upsertShaJobs_part_digest hr tau (run.parts.length-1) hp
  have hi : run.parts.length-1+1=run.parts.length := by omega
  simpa [hi,ho] using h

end ZkFormal.NearV3.Assembly
