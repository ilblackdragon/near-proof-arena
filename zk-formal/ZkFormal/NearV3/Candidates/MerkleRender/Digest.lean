import ZkFormal.NearV3.Candidates.MerkleRender.DigestNodes

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen BusDigest BusMpos ZkFormal.NearV3.Rcpt.Candidates

private theorem filter_map {α β : Type} (p : α→Bool) (f : α→β) (xs : List α) :
    (xs.filter p).map f=xs.filterMap (fun x => if p x then some (f x) else none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx,ih]

/-- Every semantic DIGEST request is supplied once by a leaf or internal hash
job. Promoted nodes cancel; there is no extra SHA job for a promotion. -/
theorem view_digest (leaves : List (List Nat)) (pub : List Fp) (hn : 1≤leaves.length)
    (hroot : (List.range 32).map (fun j => pubNat pub (PV_OUT+j))=
      (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).dig) :
    (mrkRecvs pub (generatedView leaves.length (levelTable leaves)) B_DIGEST).Perm
      ((leafShaJobs leaves).map digestMsg++(merkleShaJobs leaves).map digestMsg) := by
  have hmm : merkleShaJobs leaves=(mrkShape leaves.length).filterMap (fun x =>
      if x.2.2 then some (⟨msgId K_MRK (qBase leaves.length x.1+x.2.1),
        (((levelTable leaves).getD (x.1-1) []).getD (2*x.2.1) default).dig++
        (((levelTable leaves).getD (x.1-1) []).getD (2*x.2.1+1) default).dig⟩ : ZkFormal.Near.Render.Msg)
      else none) := by
    rw [merkleShaJobs,filter_map]
    rw [filterMap_flatMap',filterMap_flatMap']
    apply ZkFormal.Near.Render.flatMap_congr'
    intro x hx
    obtain ⟨hj1,hjn,hi,hd,_⟩ := shape_rec hn hx
    rw [levelTable_get leaves (x.1-1) (by omega)]
  rw [hmm]
  change (mrkRecvs pub ⟨leaves.length,topJ leaves.length,
    (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).id,
    (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).len,
    (mrkShape leaves.length).map (gNode (levelTable leaves))⟩ B_DIGEST).Perm _
  have hqs : ((mrkShape leaves.length).map (gNode (levelTable leaves))).zip
      (List.range ((mrkShape leaves.length).map (gNode (levelTable leaves))).length) =
      (List.range (mrkShape leaves.length).length).map
        fun k => (gNode (levelTable leaves) ((mrkShape leaves.length).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hR : mrkRecvs pub ⟨leaves.length, topJ leaves.length,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).id,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).len,
        (mrkShape leaves.length).map (gNode (levelTable leaves))⟩ B_DIGEST =
      dm (levelTable leaves) (topJ leaves.length, 0) :: ((mrkShape leaves.length).flatMap hk).map (dm (levelTable leaves)) := by
    simp only [mrkRecvs, B_DIGEST, ↓reduceIte]
    rw [hroot, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [hqs, List.flatMap_map, List.map_flatMap, flatMap_getD default (mrkShape leaves.length)]
    apply ZkFormal.Near.Render.flatMap_congr'; intro k _
    rcases hxk : (mrkShape leaves.length).getD k default with ⟨j, i, h⟩
    cases h <;> rfl
  rw [hR]
  have hrot : (mrkShape leaves.length).flatMap childPos ++ [(topJ leaves.length, 0)] =
      (List.range leaves.length).map (fun i => (0, i)) ++
        (mrkShape leaves.length).map (fun x => (x.1, x.2.1)) :=
    rot leaves.length (leaves.length + 1) 0 hn (by simp [size])
  have e1 : (mrkShape leaves.length).flatMap childPos =
      (mrkShape leaves.length).flatMap (fun x => hk x ++ pk x) := by
    apply ZkFormal.Near.Render.flatMap_congr'; intro x _; obtain ⟨j, i, h⟩ := x; cases h <;> simp [hk, pk]
  have e2 : (mrkShape leaves.length).map (fun x => (x.1, x.2.1)) =
      (mrkShape leaves.length).flatMap (fun x => hp x ++ pp x) := map_hp_pp _ _
  have e3 : ((mrkShape leaves.length).flatMap pk).map (dm (levelTable leaves)) =
      ((mrkShape leaves.length).flatMap pp).map (dm (levelTable leaves)) := by
    rw [List.map_flatMap, List.map_flatMap]; apply ZkFormal.Near.Render.flatMap_congr'; intro x hx
    cases hh : x.2.2
    · exact concrete_promoted leaves hn hx hh
    · simp [pk, pp, hh]
  have e4 : ((mrkShape leaves.length).flatMap hp).map (dm (levelTable leaves)) =
      ((mrkShape leaves.length).filterMap fun x =>
        if x.2.2 then some (⟨msgId K_MRK (qBase leaves.length x.1 + x.2.1),
          (((levelTable leaves).getD (x.1 - 1) []).getD (2 * x.2.1) default).dig ++
            (((levelTable leaves).getD (x.1 - 1) []).getD (2 * x.2.1 + 1) default).dig⟩ : Render.Msg)
        else none).map digestMsg := by
    rw [List.map_flatMap, filterMap_flatMap', List.map_flatMap]
    apply ZkFormal.Near.Render.flatMap_congr'; intro x hx
    rw [concrete_hashed leaves hn hx]
    cases x.2.2 <;> rfl
  have e5 := concrete_leaves leaves
  rw [List.perm_iff_count]; intro a
  have key := congrArg (List.count a ∘ List.map (dm (levelTable leaves))) hrot
  rw [e1, e2] at key
  have c1 := ((perm_flatMap_append hk pk (mrkShape leaves.length)).map (dm (levelTable leaves))).count_eq a
  have c2 := ((perm_flatMap_append hp pp (mrkShape leaves.length)).map (dm (levelTable leaves))).count_eq a
  simp only [Function.comp_apply, List.map_append, List.count_append] at key c1 c2
  rw [e3] at c1
  rw [e4] at c2
  rw [e5] at key
  simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, List.count_append] at key ⊢
  omega


/-- The physical DIGEST multiplicities equal the concrete native leaf and
internal jobs. The premise is the public root pin, not a traffic assumption. -/
theorem outcome_digest (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481)
    (ho : (List.range 32).map (fun j => pubNat (MerklePublic.aliasPublic pub) (PV_OUT+j))=
      toNats (NearSpec.outcomeRoot os)) (m : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_DIGEST false m=
      ((((leafShaJobs (outcomePreimages os))++merkleShaJobs (outcomePreimages os)).map digestMsg).map Msg.toFp).count m := by
  by_cases he : os=[]
  · subst os
    have hj : merkleShaJobs (outcomePreimages [])=[] := by
      apply List.eq_nil_of_length_eq_zero
      rw [merkleShaJobs_count]
      rfl
    rw [hj]
    simp [outcomeTrace,honestTrace,tableBusCount_eq,MerkleEmpty.empty_traffic,
      leafShaJobs,outcomePreimages]
    rw [show (List.range (MerkleEmpty.emptyTrace.height T_MRK)).flatMap (fun _ => ([] : List (List Fp)))=[] from
      List.flatMap_eq_nil_iff.mpr (by intros; rfl)]
    rfl
  · have hp : 1≤os.length := by cases os <;> simp_all
    have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
    have hr : (List.range 32).map (fun j => pubNat (MerklePublic.aliasPublic pub) (PV_OUT+j))=
        (((levelTable (outcomePreimages os)).getD (topJ (outcomePreimages os).length) []).getD 0 default).dig := by
      rw [hl,levelTable_root os hp]
      exact ho
    have hv := view_digest (outcomePreimages os) (MerklePublic.aliasPublic pub) (by rwa [hl]) hr
    rw [hl] at hv
    have ht := (outcome_nonempty_traffic os pub hp hn) B_DIGEST m
    rw [ht.2]
    have hc := (hv.map Msg.toFp).count_eq m
    simpa only [mrkTraffic,List.map_append] using hc

end ZkFormal.NearV3.Candidates.MerkleRender
