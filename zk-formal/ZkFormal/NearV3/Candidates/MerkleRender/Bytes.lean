import ZkFormal.NearV3.Candidates.MerkleRender.NativeTraffic

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen ZkFormal.NearV3.Rcpt.Candidates

private theorem flat_filter {α β : Type} (p : α→Bool) (f : α→List β) (xs : List α) :
    (xs.filter p).flatMap f=xs.flatMap (fun x => if p x then f x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

/-- The semantic BYTE sends are exactly the concrete whole-message SHA jobs. -/
theorem view_bytes (leaves : List (List Nat)) (pub : List Fp) (hn : 1≤leaves.length) :
    mrkSends pub (generatedView leaves.length (levelTable leaves)) B_BYTES=
      (merkleShaJobs leaves).flatMap (fun m => emitAt m.id 0 m.bytes) := by
  let lv := levelTable leaves
  have hqs : ((mrkShape leaves.length).map (gNode lv)).zip
      (List.range ((mrkShape leaves.length).map (gNode lv)).length)=
      (List.range (mrkShape leaves.length).length).map
        (fun k => (gNode lv ((mrkShape leaves.length).getD k default),k)) := by
    rw [zip_range_getD (default : MrkNode),List.length_map]
    apply List.map_congr_left
    intro k hk
    have hh := List.mem_range.mp hk
    simp [List.getD_eq_getElem?_getD,hh]
  simp only [mrkSends,generatedView,if_pos rfl,ite_true]
  rw [hqs]
  simp only [List.flatMap_map,merkleShaJobs,flat_filter]
  rw [ZkFormal.Near.Render.flatMap_getD default (mrkShape leaves.length)]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro k hk
  have hki := List.mem_range.mp hk
  have hget : (mrkShape leaves.length).getD k default=(mrkShape leaves.length)[k] := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hki,Option.getD_some]
  have hm : (mrkShape leaves.length).getD k default∈mrkShape leaves.length := by
    rw [hget]; exact List.getElem_mem _
  have hr := shape_rec hn hm
  obtain ⟨h1,h2,h3,h4,_⟩ := hr
  rcases hx : (mrkShape leaves.length).getD k default with ⟨j,i,h⟩
  rw [hx] at h1 h2 h3 h4
  cases h with
  | false => simp [gNode]
  | true =>
    have hb := hashedBefore_eq hn lv hki (by rw [←hget,hx])
    rw [←hget,hx] at hb
    simp only [gNode,if_true]
    rw [hb]
    simp only [ch,lv,levelTable_get leaves (j-1) (by omega)]

/-- Exact physical BYTE multiplicities match the concrete native jobs, for
both empty and nonempty outcome lists. These are the jobs counted by the allocator. -/
theorem outcome_bytes (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481) (m : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_BYTES true m=
      (((merkleShaJobs (outcomePreimages os)).flatMap (fun j => emitAt j.id 0 j.bytes)).map Msg.toFp).count m := by
  by_cases he : os=[]
  · subst os
    have hj : merkleShaJobs (outcomePreimages [])=[] := by
      apply List.eq_nil_of_length_eq_zero
      rw [merkleShaJobs_count]
      rfl
    rw [hj]
    simp [outcomeTrace,honestTrace,tableBusCount_eq,MerkleEmpty.empty_traffic]
    rw [show (List.range (MerkleEmpty.emptyTrace.height T_MRK)).flatMap (fun _ => ([] : List (List Fp)))=[] from
      List.flatMap_eq_nil_iff.mpr (by intros; rfl)]
    rfl
  · have hp : 1≤os.length := by cases os <;> simp_all
    have ht := (outcome_nonempty_traffic os pub hp hn) B_BYTES m
    have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
    have hv := view_bytes (outcomePreimages os) (MerklePublic.aliasPublic pub) (by rwa [hl])
    rw [hl] at hv
    simpa only [mrkTraffic,hv] using ht.1

end ZkFormal.NearV3.Candidates.MerkleRender
