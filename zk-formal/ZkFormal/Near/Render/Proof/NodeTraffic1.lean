import ZkFormal.Near.Render.Proof.NodeRowT

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic1 — the node table's traffic, node by node

`rows_decomp`: the traffic of all rows of the node table is the
concatenation, node by node, of the row traffic `RT` of the node's records
(the `SUM` and padding rows have none).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace NodeCells
open NodeGen

/-- The traffic of a node row on bus `b`, side `s` (`first`: row 0). -/
def RT (I : Info) (u : Std.HashMap Edge Nat) (pub : List Fp) (r : NRec) (b : Nat) (s : Bool) : List (List Fp) :=
  let first := decide (r.n = 0 ∧ r.pos = 0)
  if b = B_BYTES ∧ s = true then [Msg.toFp [msgId K_NPRE r.n, r.pos, r.b], Msg.toFp [msgId K_NPOST r.n, r.pos, r.pb]]
  else if b = B_DIGEST ∧ s = false then
    (if V I u r 142 = 1 then [V I u r 140 :: V I u r 141 :: (List.range 32).map fun i => V I u r (72 + i)] else []) ++
    (if V I u r 142 = 1 then [Fp.ofNat (rowCell I u r 140 + 1) :: V I u r 141 ::
      (List.range 32).map fun i => V I u r (104 + i)] else []) ++
    (if first then [((K_NPRE : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_PRE + i) 0,
      ((K_NPOST : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_POST + i) 0] else [])
  else if b = B_PARENT ∧ s = true then
    if V I u r 143 = 1 then [[V I u r 137, Fp.ofNat (rowCell I u r 7 + 1), V I u r 138, V I u r 154]] else []
  else if b = B_PARENT ∧ s = false then
    if r.pos = 0 ∧ first = false then [[V I u r 4, V I u r 7, V I u r 6, V I u r 153]] else []
  else if b = B_VSLOT ∧ s = false then (if V I u r 144 = 1 then [[V I u r 4]] else [])
  else if b = B_EDGE then
    (if V I u r 145 = 1 then [[V I u r 4, V I u r 146, V I u r 147, V I u r 148, V I u r 149,
      if s then 0 else V I u r 150]] else []) ++
    (if V I u r 160 = 1 then [[V I u r 4, Fp.ofNat (2 * rowCell I u r 23 + rowCell I u r 27 + 1), Fp.ofNat (loN I u r),
      V I u r 161, V I u r 162, if s then 0 else V I u r 151]] else [])
  else []

/-- The traffic of a node row is `RT`. -/
theorem row_RT {I : Info} {u : Std.HashMap Edge Nat} {r : NRec} {tr : Trace Fp} {q : Nat} {pub : List Fp}
    (hc : ∀ col, col < 163 → tr.cell T_NODE q col = Fp.ofNat (rowCell I u r col))
    (hq : q = 0 ↔ (r.n = 0 ∧ r.pos = 0)) (b : Nat) (s : Bool) :
    rowTraffic Node.interactions tr T_NODE q pub b s = RT I u pub r b s := by
  unfold RT
  by_cases h1 : b = B_BYTES ∧ s = true
  · obtain ⟨rfl, rfl⟩ := h1; rw [row_bytes hc]; simp
  rw [if_neg h1]
  by_cases h2 : b = B_DIGEST ∧ s = false
  · obtain ⟨rfl, rfl⟩ := h2; rw [row_digest hc]; simp only [B_DIGEST, B_BYTES, and_self, if_true]
    by_cases h0 : q = 0
    · simp [h0, hq.1 h0]
    · have : ¬ (r.n = 0 ∧ r.pos = 0) := fun h => h0 (hq.2 h)
      simp [h0, this]
  rw [if_neg h2]
  by_cases h3 : b = B_PARENT ∧ s = true
  · obtain ⟨rfl, rfl⟩ := h3; rw [row_parentS hc]; simp
  rw [if_neg h3]
  by_cases h4 : b = B_PARENT ∧ s = false
  · obtain ⟨rfl, rfl⟩ := h4; rw [row_parentR hc]
    simp only [V, rc_nf, B_PARENT, and_self, if_true]
    by_cases hp : r.pos = 0
    · by_cases h0 : q = 0
      · have := hq.1 h0
        simp [hp, h0, b2n, this, ofNat1']
        decide
      · have : r.n ≠ 0 := fun h => h0 (hq.2 ⟨h, hp⟩)
        have e : (1 : Fp) - 0 = 1 := by decide
        simp [hp, h0, b2n, this, ofNat1', e]
    · have h0 : q ≠ 0 := fun h => hp (hq.1 h).2
      have e : (0 : Fp) - 0 = 0 := by decide
      simp [hp, h0, b2n, ofNat0', e]
  rw [if_neg h4]
  by_cases h5 : b = B_VSLOT ∧ s = false
  · obtain ⟨rfl, rfl⟩ := h5; rw [row_vslot hc]; simp
  rw [if_neg h5]
  by_cases h6 : b = B_EDGE
  · subst h6; rw [row_edge hc, if_pos rfl]
  rw [if_neg h6]
  exact row_other b s h1 h2 (fun h => by subst h; cases s <;> simp_all) h5 h6

/-! ## Records -/

theorem layN_pos (I : Info) (n : Nat) : 1 ≤ (NodeLay.layN I n).length := by
  simp only [NodeLay.layN, layout]
  cases h : I.nodeAt n with
  | leaf k v m => simp [fieldsOf, F.len]
  | ext k kid m => simp [fieldsOf, F.len]
  | branch v kids m => cases v <;> simp [fieldsOf, F.len]

theorem nodeRecs_len (I : Info) (n : Nat) : (nodeRecs I n).length = (NodeLay.layN I n).length := by
  rw [NodeLay.nodeRecs_eq]; simp

theorem nodeRecs_get (I : Info) (n p : Nat) (hp : p < (nodeRecs I n).length) :
    ((nodeRecs I n).getD p default).n = n ∧ ((nodeRecs I n).getD p default).pos = p := by
  rw [nodeRecs_len] at hp
  rw [NodeLay.nodeRecs_eq]; simp [List.getD_eq_getElem?_getD, hp]

theorem mem_nodeRecs {I : Info} {n : Nat} {r : NRec} (h : r ∈ nodeRecs I n) : r.n = n := by
  rw [NodeLay.nodeRecs_eq] at h; simp only [List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; rfl

theorem first_iff (I : Info) (hN : 0 < I.ns.size) {q : Nat} (hq : q < (recsOf I).length) :
    q = 0 ↔ (((recsOf I).getD q default).n = 0 ∧ ((recsOf I).getD q default).pos = 0) := by
  have hsplit : recsOf I = nodeRecs I 0 ++ (List.range (I.ns.size - 1)).flatMap (fun n => nodeRecs I (n + 1)) := by
    unfold recsOf
    obtain ⟨M, hM⟩ : ∃ M, I.ns.size = M + 1 := ⟨I.ns.size - 1, by omega⟩
    rw [hM, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]; simp
  have hL := layN_pos I 0
  rw [← nodeRecs_len] at hL
  by_cases h0 : q < (nodeRecs I 0).length
  · have hg : (recsOf I).getD q default = (nodeRecs I 0).getD q default := by
      rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_left h0, ← List.getD_eq_getElem?_getD]
    rw [hg, (nodeRecs_get I 0 q h0).1, (nodeRecs_get I 0 q h0).2]; simp
  · have hlt : q < (recsOf I).length := hq
    rw [hsplit] at hlt
    have hm : (recsOf I).getD q default ∈ (List.range (I.ns.size - 1)).flatMap (fun n => nodeRecs I (n + 1)) := by
      rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      rw [List.length_append] at hlt
      rw [List.getElem?_eq_getElem (by omega)]; simp only [Option.getD_some]; exact List.getElem_mem _
    obtain ⟨n, -, hn⟩ := List.mem_flatMap.1 hm
    have := mem_nodeRecs hn
    constructor
    · intro h; omega
    · intro h; omega

end NodeCells

section
open NodeCells NodeGen
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem rows_decomp (b : Nat) (s : Bool) :
    ((List.range ((render c.1 e).height T_NODE)).flatMap fun q =>
      rowTraffic Node.interactions (render c.1 e) T_NODE q (publicOf c) b s) =
    (List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r b s := by
  obtain ⟨_, hH, hcell⟩ := node_render c.1 e
  have hN : (mkInfo c.1 e).ns.size = e.ns.length := NodeInfo.info_N
  have hN0 : 0 < (mkInfo c.1 e).ns.size := by rw [hN]; exact hg.shape.nonempty
  have hle : (recsOf (mkInfo c.1 e)).length + 1 ≤ 2 ^ LOf (mkInfo c.1 e) := le_pow_logOf _
  have hR : 1 ≤ (recsOf (mkInfo c.1 e)).length := by
    unfold recsOf
    obtain ⟨M, hM⟩ : ∃ M, (mkInfo c.1 e).ns.size = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN0).symm⟩
    rw [hM, List.range_succ_eq_map, List.flatMap_cons]
    have := layN_pos (mkInfo c.1 e) 0; rw [← nodeRecs_len] at this
    simp; omega
  rw [hH, range_split (show (recsOf (mkInfo c.1 e)).length ≤ 2 ^ LOf (mkInfo c.1 e) by omega), List.flatMap_append,
    flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      have := List.mem_range.1 hq'
      apply row_off (by omega)
      intro col hcol
      rw [hcell _ col (by omega) (by rcases hcol with h | h | h | h | h | h | h <;> subst h <;> decide)]
      simp only [cell, recsA, List.size_toArray, show ¬ (recsOf (mkInfo c.1 e)).length + q' < (recsOf (mkInfo c.1 e)).length by omega,
        if_false]
      split
      · rcases hcol with h | h | h | h | h | h | h <;> subst h <;> rfl
      · rcases hcol with h | h | h | h | h | h | h <;> subst h <;> rfl),
    List.append_nil]
  have hrow : ∀ q, q < (recsOf (mkInfo c.1 e)).length →
      rowTraffic Node.interactions (render c.1 e) T_NODE q (publicOf c) b s =
        RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) ((recsOf (mkInfo c.1 e)).getD q default) b s := by
    intro q hq
    apply row_RT _ (first_iff _ hN0 hq)
    intro col hcol
    rw [hcell q col (by omega) hcol]
    simp [cell, recsA, hq, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [flatMap_congr' (fun q hq => hrow q (List.mem_range.1 hq)), ← flatMap_getD default (recsOf (mkInfo c.1 e))
    (fun r => RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r b s)]
  simp only [recsOf, List.flatMap_assoc, hN]

end

end ZkFormal.Near.Render
