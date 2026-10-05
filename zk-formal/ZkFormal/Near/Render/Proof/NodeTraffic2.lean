import ZkFormal.Near.Render.Proof.NodeTraffic1
import ZkFormal.Near.Render.Proof.BusCommon

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic2 — node traffic: BYTES, VSLOT, PARENT receives

Per bus, the rows' traffic (`rows_decomp`) is a permutation of the honest
view's traffic.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace NodeTr
open NodeCells NodeGen NodeInfo

/-- The rows of node `n` as functions of the position. -/
abbrev mkR (I : Info) (n p : Nat) : NRec :=
  ⟨n, p, ((NodeLay.layN I n).getD p default).1, ((NodeLay.layN I n).getD p default).2,
    (I.pre.getD n []).getD p 0, (I.post.getD n []).getD p 0⟩

theorem filterMap_flat {α β : Type} (f : α → Option β) : ∀ l : List α, l.filterMap f = l.flatMap fun x => (f x).toList
  | [] => rfl
  | a :: l => by cases h : f a <;> simp [List.filterMap_cons, h, filterMap_flat f l]

theorem flatMap_first {β : Type} (L : Nat) (hL : 1 ≤ L) (g : Nat → List β) (hg : ∀ p, p ≠ 0 → g p = []) :
    (List.range L).flatMap g = g 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [flatMap_nil' (fun p _ => hg _ (Nat.succ_ne_zero p))]; simp

/-- The views of the honest node table, as `(view, id)` pairs. -/
theorem zipViews (I : Info) (u : Std.HashMap Edge Nat) :
    (nodeViewsOf I u).zip (List.range (nodeViewsOf I u).length) =
      (List.range I.ns.size).map fun n => (nodeViewOf I u n, n) := by
  simp [nodeViewsOf, zip_range_map]

section
variable (I : Info) (u : Std.HashMap Edge Nat) (pub : List Fp) (r : NRec)
theorem RT_bytes : RT I u pub r B_BYTES true =
    [Msg.toFp [msgId K_NPRE r.n, r.pos, r.b], Msg.toFp [msgId K_NPOST r.n, r.pos, r.pb]] := by simp [RT]
theorem RT_vslot : RT I u pub r B_VSLOT false = if V I u r 144 = 1 then [[V I u r 4]] else [] := by
  simp [RT, B_VSLOT, B_BYTES, B_DIGEST, B_PARENT]
theorem RT_parentS : RT I u pub r B_PARENT true =
    if V I u r 143 = 1 then [[V I u r 137, Fp.ofNat (rowCell I u r 7 + 1), V I u r 138, V I u r 154]] else [] := by
  simp [RT, B_BYTES, B_DIGEST, B_PARENT]
theorem RT_parentR : RT I u pub r B_PARENT false =
    if r.pos = 0 ∧ ¬ (r.n = 0 ∧ r.pos = 0) then [[V I u r 4, V I u r 7, V I u r 6, V I u r 153]] else [] := by
  simp [RT, B_BYTES, B_DIGEST, B_PARENT]
theorem RT_digest : RT I u pub r B_DIGEST false =
    (if V I u r 142 = 1 then [V I u r 140 :: V I u r 141 :: (List.range 32).map fun i => V I u r (72 + i)] else []) ++
    (if V I u r 142 = 1 then [Fp.ofNat (rowCell I u r 140 + 1) :: V I u r 141 ::
      (List.range 32).map fun i => V I u r (104 + i)] else []) ++
    (if r.n = 0 ∧ r.pos = 0 then [((K_NPRE : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_PRE + i) 0,
      ((K_NPOST : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_POST + i) 0] else []) := by
  simp [RT, B_BYTES, B_DIGEST]
theorem RT_edge (s : Bool) : RT I u pub r B_EDGE s =
    (if V I u r 145 = 1 then [[V I u r 4, V I u r 146, V I u r 147, V I u r 148, V I u r 149,
      if s then 0 else V I u r 150]] else []) ++
    (if V I u r 160 = 1 then [[V I u r 4, Fp.ofNat (2 * rowCell I u r 23 + rowCell I u r 27 + 1), Fp.ofNat (loN I u r),
      V I u r 161, V I u r 162, if s then 0 else V I u r 151]] else []) := by
  simp [RT, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]
theorem RT_other (b : Nat) (s : Bool) (h1 : ¬ (b = B_BYTES ∧ s = true)) (h2 : ¬ (b = B_DIGEST ∧ s = false))
    (h3 : b ≠ B_PARENT) (h4 : ¬ (b = B_VSLOT ∧ s = false)) (h5 : b ≠ B_EDGE) : RT I u pub r b s = [] := by
  simp only [RT]; rw [if_neg h1, if_neg h2, if_neg (fun h => h3 h.1), if_neg (fun h => h3 h.1), if_neg h4, if_neg h5]
end

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs


theorem len_pre {n : Nat} (hn : n < e.ns.length) :
    (NodeLay.layN (mkInfo c.1 e) n).length = ((mkInfo c.1 e).pre.getD n []).length ∧
    (NodeLay.layN (mkInfo c.1 e) n).length = ((mkInfo c.1 e).post.getD n []).length := by
  rw [NodeLay.pre_layout hg hs.keys hn, NodeLay.post_layout hg hs.keys hn]; simp

theorem tBytes : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_BYTES true).Perm
      ((nodeSends (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) B_BYTES).map Msg.toFp) := by
  simp only [nodeSends, if_true, zipViews, info_N, List.flatMap_map, List.map_flatMap]
  apply perm_flatMap_congr; intro n hn
  have hn' := List.mem_range.1 hn
  have hser0 := view_pre hg hn' (hs.keys _ (List.getElem_mem hn'))
  have hser1 := view_post hg hn' (hs.keys _ (List.getElem_mem hn'))
  obtain ⟨l1, l2⟩ := len_pre hg hs hn'
  simp only [nodeViewOf, info_nodeAt hn', hser0, hser1, NodeLay.nodeRecs_eq, List.flatMap_map, RT_bytes,
    List.map_append]
  refine (List.Perm.of_eq (flatMap_congr' fun a _ => (List.singleton_append (l := [_])).symm)).trans
    ((perm_flatMap_append _ _ _).trans ?_)
  rw [flatMap_single (fun _ _ => rfl), flatMap_single (fun _ _ => rfl)]
  simp only [emitAt, List.map_map, ← l1, ← l2, Nat.zero_add]
  exact List.Perm.refl _

theorem tVslot : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_VSLOT false).Perm
      ((nodeRecvs (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) (publicOf c) B_VSLOT).map Msg.toFp) := by
  simp only [RT_vslot]
  simp only [nodeRecvs, B_VSLOT, B_DIGEST, B_PARENT, Nat.reduceEqDiff, if_false, if_true, zipViews, info_N,
    List.filterMap_map]
  apply List.Perm.of_eq
  rw [filterMap_flat, List.map_flatMap]
  apply flatMap_congr'; intro n hn
  have hn' := List.mem_range.1 hn
  have hL := layN_pos (mkInfo c.1 e) n
  simp only [NodeLay.nodeRecs_eq, List.flatMap_map, V, rc_gV, rc_nid, Function.comp_apply, nodeViewOf,
    view_touched, info_nodeAt hn']
  rw [flatMap_first _ hL _ (fun p hp => by simp [hp, b2n, ofNat0'])]
  by_cases ht : e.ns[n].touched = true <;> simp [ht, b2n, ofNat1', ofNat0', Msg.toFp]

theorem tParentR : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_PARENT false).Perm
      ((nodeRecvs (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) (publicOf c) B_PARENT).map Msg.toFp) := by
  simp only [RT_parentR]
  simp only [nodeRecvs, B_VSLOT, B_DIGEST, B_PARENT, Nat.reduceEqDiff, if_false, if_true, zipViews, info_N]
  apply List.Perm.of_eq
  obtain ⟨M, hM⟩ : ∃ M, e.ns.length = M + 1 := ⟨e.ns.length - 1, by have := hg.shape.nonempty; omega⟩
  have hper : ∀ n, n < e.ns.length → ((nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      if r.pos = 0 ∧ ¬ (r.n = 0 ∧ r.pos = 0) then [[V (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) r 4,
        V (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) r 7, V (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) r 6,
        V (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) r 153]] else []) =
      if n = 0 then [] else [Msg.toFp [n, (mkInfo c.1 e).depth.getD n 0, ((mkInfo c.1 e).pre.getD n []).length,
        (mkInfo c.1 e).res.getD n n]] := by
    intro n hn
    rw [NodeLay.nodeRecs_eq, List.flatMap_map, flatMap_first _ (layN_pos _ n) _ (fun p hp => by simp [hp])]
    by_cases h0 : n = 0 <;> simp [h0, V, rc_nid, rc_depth, rc_len, rc_res, Msg.toFp]
  rw [flatMap_congr' (fun n hn => hper n (List.mem_range.1 hn)), hM, List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map, List.map_cons, List.drop_one, List.tail_cons, List.map_map, List.map_map]
  simp only [if_true, Nat.succ_ne_zero, if_false, List.nil_append]
  rw [flatMap_single (fun _ _ => rfl), List.map_map]
  apply List.map_congr_left; intro n hn
  have hn' : n + 1 < e.ns.length := by have := List.mem_range.1 hn; omega
  have hser0 := view_pre hg hn' (hs.keys _ (List.getElem_mem hn'))
  simp [nodeViewOf, info_nodeAt hn', hser0, Msg.toFp]

end

end NodeTr

end ZkFormal.Near.Render
