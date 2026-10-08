import ZkFormal.NearV3.Assembly.SchedulerDigestFrame

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private def blankPart : TreePart := ⟨.RLP,.hash [],.hash [],0⟩

private theorem indexed_plan (cs : UCase) (start : Nat) (ps : List TreePart) :
    (List.range ps.length).flatMap (fun k=>partDigestUses cs (start+k) (ps.getD k blankPart).kind)=
      planDigestUses cs start (ps.map TreePart.kind) := by
  induction ps generalizing start with
  | nil=>rfl
  | cons p ps ih=>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getD_cons_zero,List.getD_cons_succ,List.map_cons,planDigestUses,Nat.add_zero]
    rw [←ih (start+1)]
    congr 1
    apply congrArg (fun f=>(List.range ps.length).flatMap f)
    funext k
    simp only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem flat_perm {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil=>exact List.Perm.refl []
  | cons x xs ih=>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (fun y hy=>h y (by simp [hy])))

/-- All concrete serialized node-window IDs are exactly the native plan's
non-root job IDs, including branch-order permutations and repeated values. -/
theorem native_node_job_ids {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {I : Render.UpsInst}
    (hframe : NativeDigestFrame run I) (hi : InstOk I) (hparts : NativePartFamily I)
    (hn : ∀k,k<nQ I→(part I k).kind=0∨(part I k).kind=5→0<nWin (part I k).shape) :
    (digestJobIds ((List.range (nQ I)).flatMap (fun k=>
      (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)))).Perm
      ((List.range (nQ I)).map (fieldJob I)) := by
  unfold digestJobIds
  rw [List.map_flatMap]
  have hperm : ((List.range (nQ I)).flatMap (fun k=>
      digestJobIds ((List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)))).Perm
      ((List.range (nQ I)).flatMap (fun k=>
        (partDigestUses run.terminal k (run.parts.getD k blankPart).kind).map (fieldJob I))) := by
    apply flat_perm
    intro k hk
    have hkb:=List.mem_range.mp hk
    have hkr:k<run.parts.length:=by rw [←hframe.2.2.1];exact hkb
    have hget:run.parts[k]?=some (run.parts.getD k blankPart) := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hkr,Option.getD_some]
    obtain ⟨_,hf,hp,hw,_⟩:=hparts k hkb
    exact physical_native_part_job_ids hframe hi hget hf hp hw (hn k hkb)
  have he : (List.range (nQ I)).flatMap (fun k=>
      (partDigestUses run.terminal k (run.parts.getD k blankPart).kind).map (fieldJob I))=
      (List.range (nQ I)).map (fieldJob I) := by
    rw [←List.map_flatMap,hframe.2.2.1]
    have hh:=indexed_plan run.terminal 0 run.parts
    simp only [Nat.zero_add] at hh
    rw [hh,planned_digest_uses (traceUpsert_plan root key value run hr)]
  exact he ▸ hperm

/-- W3 contributes precisely the final root job ID. -/
theorem root_job_id (I : Render.UpsInst) :
    digestJobIds (digestRowMsgs I (.w 3))=[fieldJob I (nQ I)] := by
  unfold digestJobIds digestRowMsgs digestRowCell
  rw [walk_digest]
  simp [fieldJob,digMsg]

/-- Whole-instance physical DIGEST job IDs form exactly the native SHA batch.
Hash payload equality and native nonempty-child discharge remain separate. -/
theorem native_instance_job_ids {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {I : Render.UpsInst}
    (hframe : NativeDigestFrame run I) (hi : InstOk I) (hparts : NativePartFamily I)
    (hn : ∀k,k<nQ I→(part I k).kind=0∨(part I k).kind=5→0<nWin (part I k).shape) :
    (digestJobIds (digestRowMsgs I (.w 3)++(List.range (nQ I)).flatMap (fun k=>
      (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)))).Perm
      ((upsertShaJobs I.tau value run).map (fun M=>(Fp.ofNat M.id).toNat)) := by
  have hnids:=native_node_job_ids hr hframe hi hparts hn
  change (digestJobIds (digestRowMsgs I (.w 3))++
    digestJobIds ((List.range (nQ I)).flatMap (fun k=>
      (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)))).Perm _
  rw [root_job_id]
  apply List.Perm.trans ((List.Perm.refl _).append hnids)
  have he : (upsertShaJobs I.tau value run).map (fun M=>(Fp.ofNat M.id).toNat)=
      (List.range (nQ I+1)).map (fieldJob I) := by
    have hh := congrArg (List.map (fun n : Nat => (Fp.ofNat n).toNat))
      (upsert_jobs_indexed I.tau value run)
    change _ = (List.range (nQ I+1)).map (fun j => (Fp.ofNat (upsertJobId I.tau j)).toNat)
    simpa only [List.map_map, Function.comp_def, hframe.2.2.1] using hh
  rw [he,List.range_succ,List.map_append,List.map_cons,List.map_nil]
  exact List.perm_append_comm

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
