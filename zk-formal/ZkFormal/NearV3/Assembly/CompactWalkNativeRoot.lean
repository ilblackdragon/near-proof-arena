import ZkFormal.NearV3.Assembly.CompactWalkDigests

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows Render.UpsGen

private theorem range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i=>xs.getD i d)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range]
  rw [←List.getElem_eq_getD (h:=hj) d]

/-- The actual W3 physical lookup is supplied by the last native upsert SHA job.
Field encoding is exact even before adding global no-wrap bounds. -/
theorem allocated_walk_root_digest {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : Render.UpsInst}
    (hv : u.Valid) (ha : AllocatedNativeInstance us tau u I) (hs : NativeShaFamily u I) (D : URow) :
    (Sha.Gen.expectedDigests [upsertShaJob I.tau (nQ I) (nodeEnc u.run.output)]).map Msg.toFp=
      (compactMsgs (fun x=>((wCell I 3 x : Int):Fp).toNat) D B_DIGEST false).map Msg.toFp := by
  have hd := allocated_root_digest hv ha hs
  have hl := congrArg (List.map List.length) hd
  simp only [Sha.Gen.expectedDigests,upsertShaJob,List.filter_cons_of_pos,List.filter_nil,List.map_cons,
    List.map_nil,List.length_append,List.length_cons,List.length_nil,ArenaCore.sha256_length,
    List.length_map,digMsg] at hl
  have hp : I.post.length=32 := by
    simp only [List.cons.injEq] at hl
    omega
  rw [hd,walk_digest]
  simp only [ite_true,Msg.toFp,List.map_cons,List.map_nil,digMsg,List.map_append,List.map_map,
    Function.comp_def,Fp.ofNat_toNat]
  have he := congrArg (List.map Fp.ofNat) (range_getD I.post 0)
  rw [hp] at he
  simp only [List.map_map,Function.comp_def] at he
  rw [he]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
