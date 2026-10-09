import ZkFormal.NearV3.Assembly.SchedulerSanityJobs
import ZkFormal.NearV3.Assembly.UpsertShaEncoding

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen

private theorem shaFrom_native_digests (tau start : Nat) (parts : List TreePart)
    (h : ∀p∈parts,sha256 (nodeEnc p.output)=p.output.hashOf) :
    Sha.Gen.expectedDigests (upsertShaFrom tau start (parts.map (fun p=>nodeEnc p.output)))=
      parts.mapIdx (fun i p=>digMsg (upsertJobId tau (start+i)) (nodeEnc p.output).length
        (p.output.hashOf.map UInt8.toNat)) := by
  induction parts generalizing start with
  | nil => rfl
  | cons p ps ih =>
    have hh := h p (by simp)
    have ht := ih (start+1) (fun p hp=>h p (by simp [hp]))
    simp only [List.map_cons,upsertShaFrom,Sha.Gen.expectedDigests,upsertShaJob,
      List.filter_cons_of_pos,List.map_cons,List.mapIdx_cons,Nat.add_zero] at ⊢
    change ([upsertJobId tau start,(nodeEnc p.output).map UInt8.toNat |>.length]++
      (sha256 (((nodeEnc p.output).map UInt8.toNat).map UInt8.ofNat)).map UInt8.toNat)::
      Sha.Gen.expectedDigests (upsertShaFrom tau (start+1) (ps.map (fun p=>nodeEnc p.output)))=_
    rw [nativeBytes_roundtrip,hh,List.length_map,ht]
    simp only [digMsg,List.singleton_append,List.cons_append,List.nil_append]
    congr 2
    funext i p
    rw [show start+1+i=start+(i+1) by omega]

/-- Every emitted scheduler node digest is its actual native output hash, with
its original global transition and part IDs. No output-wf or hash premise. -/
theorem upsert_native_digest_inventory {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (tau : Nat) :
    Sha.Gen.expectedDigests (upsertShaJobs tau value run)=
      digMsg (upsertJobId tau 0) value.length ((sha256 value).map UInt8.toNat)::
        run.parts.mapIdx (fun i p=>digMsg (upsertJobId tau (i+1)) (nodeEnc p.output).length
          (p.output.hashOf.map UInt8.toNat)) := by
  have hp := shaFrom_native_digests tau 1 run.parts (fun p hp=>upsertShaJob_node_digest hr hp)
  simp only [upsertShaJobs,upsertShaFrom,Sha.Gen.expectedDigests,upsertShaJob,
    List.filter_cons_of_pos,List.map_cons] at ⊢
  change ([upsertJobId tau 0,(value.map UInt8.toNat).length]++
    (sha256 ((value.map UInt8.toNat).map UInt8.ofNat)).map UInt8.toNat)::
    Sha.Gen.expectedDigests (upsertShaFrom tau 1 (run.parts.map (fun p=>nodeEnc p.output)))=_
  rw [nativeBytes_roundtrip,List.length_map,hp]
  simp [digMsg,Nat.add_comm]

/-- Sanity digest output is tied to the SAME native scheduler state bytes. -/
theorem scheduler_native_sanity_digest (tau : Nat) {u : SchedulerUpsertWitness} (hv : u.Valid) :
    ∃input links,input.length=64 ∧ u.value=(Bandwidth.State.mk links (sha256 input)).encode ∧
      Sha.Gen.expectedDigests [schedulerSanityJob tau u]=
        [digMsg (11+16*tau) 64 ((sha256 input).map UInt8.toNat)] := by
  obtain ⟨input,hi,hlen,links,hstate⟩ := SchedulerUpsertWitness.sanity hv
  refine ⟨input,links,hlen,hstate,?_⟩
  simp [Sha.Gen.expectedDigests,schedulerSanityJob,hi,List.map_map,Function.comp_def,hlen,digMsg]

end ZkFormal.NearV3.Assembly
