import ZkFormal.Near.Render.Proof.DigMrk

/-!
# ZkFormal.Near.Render.Proof.DigMrk2 — the `mrk` table's `DIGEST` receives

`mrk` receives the root's digest (against the claim's outcome root) and both
children of every hashed node.  By the position rotation of `BusMpos.rot`
(children of all shape nodes plus the root = the leaves plus all shape
nodes), and since a promoted node is its child, these are exactly the leaves
and the hashed nodes, each once: the digests of the `LEAF(r)` and `MRK(q)`
SHA messages (`mrk_digest`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusDigest
open MrkGen MrkTraffic BusMpos

/-- The `DIGEST` message of merkle position `p`. -/
def dm (lv : List (List MNode)) (p : Nat × Nat) : ZkFormal.Near.Msg :=
  digMsg ((lv.getD p.1 []).getD p.2 default).id ((lv.getD p.1 []).getD p.2 default).len
    ((lv.getD p.1 []).getD p.2 default).dig

def hk (x : Nat × Nat × Bool) : List (Nat × Nat) := if x.2.2 then childPos x else []
def pk (x : Nat × Nat × Bool) : List (Nat × Nat) := if x.2.2 then [] else childPos x
def hp (x : Nat × Nat × Bool) : List (Nat × Nat) := if x.2.2 then [(x.1, x.2.1)] else []
def pp (x : Nat × Nat × Bool) : List (Nat × Nat) := if x.2.2 then [] else [(x.1, x.2.1)]

/-- The `LEAF(r)` SHA messages. -/
def leafMsgs (I : Info) : List Render.Msg := (List.range I.nRcpt).map fun r => ⟨msgId K_LEAF r, leafBytes I r⟩

theorem filterMap_flatMap' {α β : Type} (F : α → Option β) :
    ∀ l : List α, l.filterMap F = l.flatMap fun x => (F x).toList
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons, List.flatMap_cons, filterMap_flatMap' F l]
    cases F x <;> rfl

theorem map_hp_pp {β : Type} (f : Nat × Nat × Bool → β) :
    ∀ l : List (Nat × Nat × Bool), l.map f = l.flatMap fun x => (if x.2.2 then [f x] else []) ++ (if x.2.2 then [] else [f x])
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.flatMap_cons, map_hp_pp f l]
    cases x.2.2 <;> rfl

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem nR_pos : 1 ≤ (mkInfo c.1 e).nRcpt := by
  show 1 ≤ e.rs.length; rw [hg.len]; exact hg.n_pos

theorem topJ_lt : topJ (mkInfo c.1 e).nRcpt < (mkInfo c.1 e).nRcpt + 2 := by
  obtain ⟨_, rok, _, r, hr, _, _, _, h2⟩ := recs_facts _ (nR_pos hg)
  have := (rok r (List.mem_of_getLast? hr)).2.1
  omega

theorem leaf_len {r : Nat} (hr : r < e.rs.length) : (leafBytes (mkInfo c.1 e) r).length = 68 := by
  have h := RcptP.d_id hg (r := r) hr
  rw [RcptP.Df_eq hr] at h
  simp only [leafBytes, List.length_append, NodeInfo.leBytes_len, MrkGen.shaN_length]
  simp only [rdOf] at h
  rw [h]

theorem dm_promoted {x : Nat × Nat × Bool} (hx : x ∈ mrkShape (mkInfo c.1 e).nRcpt) (hh : x.2.2 = false)
    (lv : List (List MNode)) (hlv : lv = (List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))) :
    (pk x).map (dm lv) = (pp x).map (dm lv) := by
  obtain ⟨hj1, hjn, hi, hd, _⟩ := shape_rec (nR_pos hg) hx
  obtain ⟨j, i, h⟩ := x
  simp only at hh hj1 hjn hi hd
  subst hh
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [pk, pp, childPos, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, dm,
    Nat.add_sub_cancel]
  rw [hlv, lv_getD _ (show j' + 1 < _ by omega), lv_getD _ (show j' < _ by omega),
    levels_succ_getD _ j' i hi, ite_eq_right_of_eq_false _ _ (by simp at hd; simp; omega)]

theorem dm_hashed {x : Nat × Nat × Bool} (hx : x ∈ mrkShape (mkInfo c.1 e).nRcpt)
    (lv : List (List MNode)) (hlv : lv = (List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))) :
    (hp x).map (dm lv) =
      (if x.2.2 then [digestMsg ⟨msgId K_MRK (qBase (mkInfo c.1 e).nRcpt x.1 + x.2.1),
        ((lv.getD (x.1 - 1) []).getD (2 * x.2.1) default).dig ++
          ((lv.getD (x.1 - 1) []).getD (2 * x.2.1 + 1) default).dig⟩] else []) := by
  obtain ⟨hj1, hjn, hi, hd, _⟩ := shape_rec (nR_pos hg) hx
  obtain ⟨j, i, h⟩ := x
  simp only at hj1 hjn hi hd ⊢
  cases h with
  | false => rfl
  | true =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h2 : 2 * i + 1 < size (mkInfo c.1 e).nRcpt j' := by simpa using hd.symm
    simp only [hp, ↓reduceIte, List.map_cons, List.map_nil, dm, Nat.add_sub_cancel, digestMsg, digMsg]
    rw [hlv, lv_getD _ (show j' + 1 < _ by omega), lv_getD _ (show j' < _ by omega),
      levels_succ_getD _ j' i hi]
    simp only [h2, ↓reduceIte]
    simp only [List.length_append, levels_getD_dig (mkInfo c.1 e) j' (2 * i) (by omega),
      levels_getD_dig (mkInfo c.1 e) j' _ h2]

/-- **The mrk receives on `DIGEST`.** -/
theorem mrk_digest :
    (mrkRecvs (pubOf c.1) (mrkViewOf (mkInfo c.1 e)) B_DIGEST).Perm
      ((leafMsgs (mkInfo c.1 e)).map digestMsg ++ (mrkMsgs (mkInfo c.1 e)).map digestMsg) := by
  have hn1 := nR_pos hg
  have hv : mrkViewOf (mkInfo c.1 e) =
      ⟨(mkInfo c.1 e).nRcpt, topJ (mkInfo c.1 e).nRcpt,
        ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).id,
        ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c.1 e).nRcpt).map (gNode ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))))⟩ := rfl
  have hroot : (List.range 32).map (fun j => pubNat (pubOf c.1) (PV_OUT + j)) =
      ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).dig := by
    rw [lv_getD _ (topJ_lt hg), root_dig hg]; exact Link.pub_out (c := c) ⟨hg.pv, hg.chain⟩
  have hmm : mrkMsgs (mkInfo c.1 e) = (mrkShape (mkInfo c.1 e).nRcpt).filterMap fun x =>
      if x.2.2 then some ⟨msgId K_MRK (qBase (mkInfo c.1 e).nRcpt x.1 + x.2.1),
        ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (x.1 - 1) []).getD (2 * x.2.1) default).dig ++
          ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (x.1 - 1) []).getD (2 * x.2.1 + 1) default).dig⟩
      else none := rfl
  rw [hv, hmm]
  generalize hlv : (List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e)) = lv at hroot ⊢
  have hqs : ((mrkShape (mkInfo c.1 e).nRcpt).map (gNode lv)).zip
      (List.range ((mrkShape (mkInfo c.1 e).nRcpt).map (gNode lv)).length) =
      (List.range (mrkShape (mkInfo c.1 e).nRcpt).length).map
        fun k => (gNode lv ((mrkShape (mkInfo c.1 e).nRcpt).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hR : mrkRecvs (pubOf c.1) ⟨(mkInfo c.1 e).nRcpt, topJ (mkInfo c.1 e).nRcpt,
        ((lv.getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).id,
        ((lv.getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c.1 e).nRcpt).map (gNode lv)⟩ B_DIGEST =
      dm lv (topJ (mkInfo c.1 e).nRcpt, 0) :: ((mrkShape (mkInfo c.1 e).nRcpt).flatMap hk).map (dm lv) := by
    simp only [mrkRecvs, B_DIGEST, ↓reduceIte]
    rw [hroot, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [hqs, List.flatMap_map, List.map_flatMap, flatMap_getD default (mrkShape (mkInfo c.1 e).nRcpt)]
    apply flatMap_congr'; intro k _
    rcases hxk : (mrkShape (mkInfo c.1 e).nRcpt).getD k default with ⟨j, i, h⟩
    cases h <;> rfl
  rw [hR]
  have hrot : (mrkShape (mkInfo c.1 e).nRcpt).flatMap childPos ++ [(topJ (mkInfo c.1 e).nRcpt, 0)] =
      (List.range (mkInfo c.1 e).nRcpt).map (fun i => (0, i)) ++
        (mrkShape (mkInfo c.1 e).nRcpt).map (fun x => (x.1, x.2.1)) :=
    rot (mkInfo c.1 e).nRcpt ((mkInfo c.1 e).nRcpt + 1) 0 hn1 (by simp [size])
  have e1 : (mrkShape (mkInfo c.1 e).nRcpt).flatMap childPos =
      (mrkShape (mkInfo c.1 e).nRcpt).flatMap (fun x => hk x ++ pk x) := by
    apply flatMap_congr'; intro x _; obtain ⟨j, i, h⟩ := x; cases h <;> simp [hk, pk]
  have e2 : (mrkShape (mkInfo c.1 e).nRcpt).map (fun x => (x.1, x.2.1)) =
      (mrkShape (mkInfo c.1 e).nRcpt).flatMap (fun x => hp x ++ pp x) := map_hp_pp _ _
  have e3 : ((mrkShape (mkInfo c.1 e).nRcpt).flatMap pk).map (dm lv) =
      ((mrkShape (mkInfo c.1 e).nRcpt).flatMap pp).map (dm lv) := by
    rw [List.map_flatMap, List.map_flatMap]; apply flatMap_congr'; intro x hx
    cases hh : x.2.2
    · exact dm_promoted hg hx hh lv hlv.symm
    · simp [pk, pp, hh]
  have e4 : ((mrkShape (mkInfo c.1 e).nRcpt).flatMap hp).map (dm lv) =
      ((mrkShape (mkInfo c.1 e).nRcpt).filterMap fun x =>
        if x.2.2 then some (⟨msgId K_MRK (qBase (mkInfo c.1 e).nRcpt x.1 + x.2.1),
          ((lv.getD (x.1 - 1) []).getD (2 * x.2.1) default).dig ++
            ((lv.getD (x.1 - 1) []).getD (2 * x.2.1 + 1) default).dig⟩ : Render.Msg)
        else none).map digestMsg := by
    rw [List.map_flatMap, filterMap_flatMap', List.map_flatMap]
    apply flatMap_congr'; intro x hx
    rw [dm_hashed hg hx lv hlv.symm]
    cases x.2.2 <;> rfl
  have e5 : ((List.range (mkInfo c.1 e).nRcpt).map fun i => (0, i)).map (dm lv) =
      (leafMsgs (mkInfo c.1 e)).map digestMsg := by
    simp only [List.map_map, leafMsgs]
    apply List.map_congr_left; intro r hr
    have hr' : r < e.rs.length := List.mem_range.1 hr
    simp only [Function.comp_apply, dm, digestMsg, digMsg]
    rw [← hlv, lv_getD _ (by omega)]
    simp [levels, List.getD_eq_getElem?_getD, hr', leaf_len hg hr', Info.nRcpt, mkInfo_e]
  rw [List.perm_iff_count]; intro a
  have key := congrArg (List.count a ∘ List.map (dm lv)) hrot
  rw [e1, e2] at key
  have c1 := ((perm_flatMap_append hk pk (mrkShape (mkInfo c.1 e).nRcpt)).map (dm lv)).count_eq a
  have c2 := ((perm_flatMap_append hp pp (mrkShape (mkInfo c.1 e).nRcpt)).map (dm lv)).count_eq a
  simp only [Function.comp_apply, List.map_append, List.count_append] at key c1 c2
  rw [e3] at c1
  rw [e4] at c2
  rw [e5] at key
  simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, List.count_append] at key ⊢
  omega

end

end BusDigest

end ZkFormal.Near.Render
