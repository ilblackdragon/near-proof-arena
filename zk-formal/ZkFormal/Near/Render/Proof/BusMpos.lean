import ZkFormal.Near.Render.Proof.MrkTraffic3

/-!
# ZkFormal.Near.Render.Proof.BusMpos — `MposBusStmt`

Positions `(j, i)` of the merkle tree: `rcpt` offers level 0 (the leaves),
`mrk` offers levels `1 … J` (one per shape node) and takes every child plus
the root `(J, 0)`.  The children of level `j` are exactly level `j − 1` in
order (`children_level`), so the taken positions are a rotation of the
offered ones; every message is `[j, i, id, len]` of node `(j, i)`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusMpos
open MrkGen MrkTraffic

def childPos (x : Nat × Nat × Bool) : List (Nat × Nat) :=
  if x.2.2 then [(x.1 - 1, 2 * x.2.1), (x.1 - 1, 2 * x.2.1 + 1)] else [(x.1 - 1, 2 * x.2.1)]

theorem children_level (j sp : Nat) : ∀ s, (2 * s = sp ∨ 2 * s = sp + 1) →
    ((List.range s).map fun i => (j + 1, i, decide (2 * i + 1 < sp))).flatMap childPos =
      (List.range sp).map fun i => (j, i)
  | 0, h => by rcases h with h | h <;> simp <;> omega
  | s + 1, h => by
    rw [List.range_succ, List.map_append, List.flatMap_append]
    have ih := children_level j (2 * s) s (Or.inl rfl)
    have e1 : ((List.range s).map fun i => (j + 1, i, decide (2 * i + 1 < sp))) =
        ((List.range s).map fun i => (j + 1, i, decide (2 * i + 1 < 2 * s))) := by
      apply List.map_congr_left; intro i hi; have := List.mem_range.1 hi
      congr 3; apply propext; omega
    rw [e1, ih]
    rcases h with h | h
    · rw [← h, show 2 * (s + 1) = 2 * s + 1 + 1 by omega, List.range_succ, List.range_succ]
      simp [childPos, show 2 * s + 1 < 2 * (s + 1) by omega]
    · rw [show sp = 2 * s + 1 by omega, List.range_succ]
      simp [childPos]

variable (n : Nat)

theorem rot : ∀ f j0, 1 ≤ size n j0 → size n j0 ≤ f →
    (mrkLevels f (j0 + 1) (size n j0)).flatMap childPos ++
        [((((mrkLevels f (j0 + 1) (size n j0)).getLast?).map (·.1)).getD 1, 0)] =
      (List.range (size n j0)).map (fun i => (j0, i)) ++
        (mrkLevels f (j0 + 1) (size n j0)).map (fun x => (x.1, x.2.1))
  | 0, _, h1, h2 => absurd h2 (by omega)
  | f + 1, j0, h1, h2 => by
    have hs : size n (j0 + 1) = (size n j0 + 1) / 2 := rfl
    have hs1 : 1 ≤ size n (j0 + 1) := by omega
    simp only [mrkLevels, ← hs]
    have hc := children_level j0 (size n j0) (size n (j0 + 1)) (by omega)
    have hpos : ((List.range (size n (j0 + 1))).map fun i => (j0 + 1, i, decide (2 * i + 1 < size n j0))).map
        (fun x => (x.1, x.2.1)) = (List.range (size n (j0 + 1))).map fun i => (j0 + 1, i) := by
      simp [List.map_map, Function.comp_def]
    split
    · rename_i h1'
      simp only [List.append_nil, List.map_append]
      rw [hc, hpos, h1']
      simp
    · rename_i h1'
      have ih := rot f (j0 + 1) hs1 (by omega)
      have hne : mrkLevels f (j0 + 1 + 1) (size n (j0 + 1)) ≠ [] := by
        cases f with
        | zero => omega
        | succ f => simp [mrkLevels]; omega
      rw [List.flatMap_append, List.map_append, hc, hpos, List.getLast?_append]
      cases hl : (mrkLevels f (j0 + 1 + 1) (size n (j0 + 1))).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at hl; exact absurd hl hne
      | some a =>
        rw [hl] at ih
        simp only [Option.some_or, List.append_assoc]
        rw [ih]

theorem levels_succ_getD (I : Info) (j i : Nat) (hi : i < size I.nRcpt (j + 1)) :
    (levels I (j + 1)).getD i default =
      if 2 * i + 1 < size I.nRcpt j then
        ⟨msgId K_MRK (qBase I.nRcpt (j + 1) + i), 64,
          shaN (((levels I j).getD (2 * i) default).dig ++ ((levels I j).getD (2 * i + 1) default).dig)⟩
      else (levels I j).getD (2 * i) default := by
  have hl := levelsI_len I j
  have hi' : i < ((levels I j).length + 1) / 2 := by rw [hl]; exact hi
  rw [List.getD_eq_getElem?_getD]
  simp only [levels]
  rw [List.getElem?_map, List.getElem?_range hi', Option.map_some, Option.getD_some, hl]

/-- The message of position `p`. -/
def msgOf (lv : List (List MNode)) (p : Nat × Nat) : ZkFormal.Near.Msg :=
  [p.1, p.2, ((lv.getD p.1 []).getD p.2 default).id, ((lv.getD p.1 []).getD p.2 default).len]

end BusMpos

end ZkFormal.Near.Render

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

set_option maxHeartbeats 1000000 in
open BusMpos MrkGen MrkTraffic in
/-- **`MposBusStmt`.** -/
theorem mposBus : MposBusStmt := by
  intro c e hg m
  rw [hcount_eq, hcount_eq]
  have hv : mrkViewOf (bundle c e).info =
      ⟨(mkInfo c e).nRcpt, topJ (mkInfo c e).nRcpt,
        ((((List.range ((mkInfo c e).nRcpt + 2)).map (levels (mkInfo c e))).getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).id,
        ((((List.range ((mkInfo c e).nRcpt + 2)).map (levels (mkInfo c e))).getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c e).nRcpt).map (gNode ((List.range ((mkInfo c e).nRcpt + 2)).map (levels (mkInfo c e))))⟩ := rfl
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkRecvs, walkSends, rcptTraffic, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_FINAL, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, hv]
  have hn1 : 1 ≤ (mkInfo c e).nRcpt := by rw [show (mkInfo c e).nRcpt = e.rs.length from rfl, hg.len]; exact hg.n_pos
  have hS1 : rcptSends (pubOf c) (rcptViewsOf (bundle c e).info) 9 =
      ((List.range (mkInfo c e).nRcpt).map fun r => (0, r)).map
        (msgOf ((List.range ((mkInfo c e).nRcpt + 2)).map (levels (mkInfo c e)))) := by
    simp only [rcptSends, Nat.reduceEqDiff, if_false, if_true, rcptViewsOf, rcptData, bundle_info, List.length_map,
      List.length_range, zip_range_map, List.map_map]
    apply List.map_congr_left; intro r hr
    have hr' := List.mem_range.1 hr
    simp only [Function.comp_apply, msgOf, lv_getD (mkInfo c e) (show 0 < (mkInfo c e).nRcpt + 2 by omega)]
    simp [levels, List.getD_eq_getElem?_getD, hr']
  generalize hlv : (List.range ((mkInfo c e).nRcpt + 2)).map (levels (mkInfo c e)) = lv at hS1 ⊢
  have hlvj : ∀ j, j < (mkInfo c e).nRcpt + 2 → lv.getD j [] = levels (mkInfo c e) j := by
    intro j hj; rw [← hlv]; exact lv_getD _ hj
  have hqs : ((mrkShape (mkInfo c e).nRcpt).map (gNode lv)).zip
      (List.range ((mrkShape (mkInfo c e).nRcpt).map (gNode lv)).length) =
      (List.range (mrkShape (mkInfo c e).nRcpt).length).map
        fun k => (gNode lv ((mrkShape (mkInfo c e).nRcpt).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hgetD : ∀ k (hk : k < (mrkShape (mkInfo c e).nRcpt).length),
      (mrkShape (mkInfo c e).nRcpt).getD k default = (mrkShape (mkInfo c e).nRcpt)[k] := by
    intro k hk; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have hS2 : mrkSends (pubOf c) ⟨(mkInfo c e).nRcpt, topJ (mkInfo c e).nRcpt,
        ((lv.getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).id,
        ((lv.getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c e).nRcpt).map (gNode lv)⟩ 9 =
      ((mrkShape (mkInfo c e).nRcpt).map fun x => (x.1, x.2.1)).map (msgOf lv) := by
    simp only [mrkSends, B_BYTES, B_MPOS, Nat.reduceEqDiff, if_false, if_true]
    rw [hqs]
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    have hx := shape_rec hn1 (List.getElem_mem h1)
    rcases hxk : (mrkShape (mkInfo c e).nRcpt)[k] with ⟨j, i, h⟩
    rw [hxk] at hx
    obtain ⟨hj1, hjn, hi, hh, _⟩ := hx
    simp only at hj1 hjn hi hh
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hg' : (mrkShape (mkInfo c e).nRcpt).getD k default = (j' + 1, i, h) := by rw [hgetD k h1, hxk]
    have hg'' : (mrkShape (mkInfo c e).nRcpt).getD k (0, 0, false) = (j' + 1, i, h) := hg'
    simp only [hg', mrkPos, hg'', msgOf, hlvj (j' + 1) (by omega), levels_succ_getD _ j' i hi]
    cases h with
    | true =>
      simp at hh
      simp only [gNode, if_true, hh]
      rw [hashedBefore_eq hn1 lv h1 (by rw [hxk]), hxk]
    | false =>
      simp at hh
      simp only [gNode, Bool.false_eq_true, if_false, show ¬ (2 * i + 1 < size (mkInfo c e).nRcpt j') by omega, ch,
        Nat.add_sub_cancel, hlvj j' (by omega)]
  have hR : mrkRecvs (pubOf c) ⟨(mkInfo c e).nRcpt, topJ (mkInfo c e).nRcpt,
        ((lv.getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).id,
        ((lv.getD (topJ (mkInfo c e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c e).nRcpt).map (gNode lv)⟩ 9 =
      ((topJ (mkInfo c e).nRcpt, 0) :: (mrkShape (mkInfo c e).nRcpt).flatMap childPos).map (msgOf lv) := by
    simp only [mrkRecvs, B_DIGEST, B_MPOS, Nat.reduceEqDiff, if_false, if_true, List.map_cons]
    rw [List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [hqs, List.flatMap_map, List.map_flatMap, flatMap_getD default (mrkShape (mkInfo c e).nRcpt)]
    apply flatMap_congr'; intro k hk
    have hk' := List.mem_range.1 hk
    rcases hxk : (mrkShape (mkInfo c e).nRcpt).getD k default with ⟨j, i, h⟩
    have hxk' : (mrkShape (mkInfo c e).nRcpt).getD k (0, 0, false) = (j, i, h) := hxk
    simp only [Function.comp_apply, mrkPos, hxk']
    cases h <;> rfl
  rw [hS1, hS2, hR]
  simp only [cnt, ← List.count_append, ← List.map_append]
  have hrot : (mrkShape (mkInfo c e).nRcpt).flatMap childPos ++ [(topJ (mkInfo c e).nRcpt, 0)] =
      (List.range (mkInfo c e).nRcpt).map (fun i => (0, i)) ++
        (mrkShape (mkInfo c e).nRcpt).map (fun x => (x.1, x.2.1)) :=
    rot (mkInfo c e).nRcpt ((mkInfo c e).nRcpt + 1) 0 hn1 (by simp [size])
  rw [← hrot]
  exact (((List.perm_append_singleton _ _).map (msgOf lv)).map Msg.toFp).count_eq m

end ZkFormal.Near.Render
