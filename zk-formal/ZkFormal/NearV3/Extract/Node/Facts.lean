import ZkFormal.NearV3.Extract.NodeView
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.NodeFacts — row facts of the `node` table

Each lemma reads a few constraints of `Tables/Node.lean` on one row (and the
next row) and states them as field equations.
-/

namespace ZkFormal.NearV3.NodeProof3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3

variable {tr : Trace Fp} {pub : List Fp}


theorem con (hL : TableLocal NodeV3.table tr T_NODE pub) {r : Nat} (hr : r < tr.height T_NODE)
    {e : Expr} (he : e ∈ NodeV3.constraints) : e.eval tr T_NODE r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height T_NODE) : (r + 1) % tr.height T_NODE = r + 1 :=
  Nat.mod_eq_of_lt h

theorem mem_of {e : Expr} (h : e ∈ cBool ∨ e ∈ cRows ∨ e ∈ cTrans ∨ e ∈ cFields ∨ e ∈ cBytes ∨ e ∈ cWindows ∨
    e ∈ cLinks) : e ∈ NodeV3.constraints := by
  unfold NodeV3.constraints; simp only [List.mem_append]
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem height_le : tr.height T_NODE ≤ 2 ^ 22 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_ge : 2 ≤ tr.height T_NODE := by
  have := hL.log_ge; unfold Trace.height
  calc 2 = 2 ^ 1 := rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) this

theorem isBool {r : Nat} (hr : r < tr.height T_NODE) {x : Nat} (hx : x ∈ boolCols) :
    tr.cell T_NODE r x = 0 ∨ tr.cell T_NODE r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold NodeV3.constraints NodeV3.cBool
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨x, hx, rfl⟩))))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem bool01 {r x : Nat} (hr : r < tr.height T_NODE) (hx : x ∈ boolCols) (h : ¬ tr.cell T_NODE r x = 1) :
    tr.cell T_NODE r x = 0 := (isBool hL hr hx).resolve_right h

/-- Row structure facts. -/
theorem rowFacts {r : Nat} (hr : r < tr.height T_NODE) :
    tr.cell T_NODE r tl + (tr.cell T_NODE r te + (tr.cell T_NODE r tb1 + tr.cell T_NODE r tb2)) = tr.cell T_NODE r act ∧
    (tr.cell T_NODE r sTAG + (tr.cell T_NODE r sHPL + (tr.cell T_NODE r sHPF + (tr.cell T_NODE r sKEY + (tr.cell T_NODE r sVLEN + (tr.cell T_NODE r sVH +
      (tr.cell T_NODE r sBM + (tr.cell T_NODE r sCH + (tr.cell T_NODE r sMEM + 0))))))))) = tr.cell T_NODE r act ∧
    tr.cell T_NODE r act * tr.cell T_NODE r sumr = 0 ∧
    (tr.cell T_NODE r nf = 1 → tr.cell T_NODE r act = 1 ∧ tr.cell T_NODE r sTAG = 1 ∧ tr.cell T_NODE r fs = 1 ∧ tr.cell T_NODE r pos = 0 ∧ tr.cell T_NODE r idx = 0) ∧
    (tr.cell T_NODE r nl = 1 → tr.cell T_NODE r act = 1 ∧ tr.cell T_NODE r fe = 1 ∧ tr.cell T_NODE r sMEM = 1 ∧ tr.cell T_NODE r pos + 1 = tr.cell T_NODE r len) ∧
    (tr.cell T_NODE r sMEM = 1 → tr.cell T_NODE r fe = 1 → tr.cell T_NODE r nl = 1) := by
  have h1 := con hL hr (e := sub (.add (c tl) (.add (c te) isBr)) (c act)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h2 := con hL hr (e := sub (sum (states.map c)) (c act)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h3 := con hL hr (e := .mul (c act) (c sumr)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h4 := con hL hr (e := .mul (c nf) (Dsl.not (c act))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h5 := con hL hr (e := .mul (c nl) (Dsl.not (c act))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h6 := con hL hr (e := .mul (c nf) (Dsl.not (c sTAG))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h7 := con hL hr (e := .mul (c nf) (Dsl.not (c fs))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h8 := con hL hr (e := .mul (c nf) (c pos)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h9 := con hL hr (e := .mul (c nf) (c idx)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h10 := con hL hr (e := .mul (c nl) (Dsl.not (c fe))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h11 := con hL hr (e := .mul (c nl) (Dsl.not (c sMEM))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h12 := con hL hr (e := mul3 (c sMEM) (c fe) (Dsl.not (c nl))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h13 := con hL hr (e := .mul (c nl) (sub (.add (c pos) (k 1)) (c len))) (by simp [NodeV3.constraints, NodeV3.cRows])
  simp only [isBr, states, List.map, eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k,
    eval_sum_cons, eval_sum_nil] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  refine ⟨by grind, by grind, h3, fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · rw [h] at h4 h6 h7 h8 h9; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at h5 h10 h11 h13; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at h12; grind

theorem firstRow (h0 : 0 < tr.height T_NODE) :
    tr.cell T_NODE 0 act = 1 ∧ tr.cell T_NODE 0 nf = 1 ∧ tr.cell T_NODE 0 nid = 0 ∧ tr.cell T_NODE 0 sz = 0 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c act))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h2 := con hL h0 (e := .mul .isFirst (Dsl.not (c nf))) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h3 := con hL h0 (e := .mul .isFirst (c nid)) (by simp [NodeV3.constraints, NodeV3.cRows])
  have h5 := con hL h0 (e := .mul .isFirst (c sz)) (by simp [NodeV3.constraints, NodeV3.cRows])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1 h2 h3 h5
  exact ⟨by grind, by grind, by grind, by grind⟩

theorem lastRow (h0 : 0 < tr.height T_NODE) : tr.cell T_NODE (tr.height T_NODE - 1) act = 0 := by
  have h1 := con hL (by omega : tr.height T_NODE - 1 < _) (e := .mul .isLast (c act))
    (by simp [NodeV3.constraints, NodeV3.cRows])
  simp only [eval_mul, eval_c, eval_isLast, if_pos (show tr.height T_NODE - 1 + 1 = tr.height T_NODE by omega)] at h1
  grind

/-- Inside a node. -/
theorem inNode {r : Nat} (hr : r + 1 < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1) (hl : tr.cell T_NODE r nl = 0) :
    tr.cell T_NODE (r + 1) act = 1 ∧ tr.cell T_NODE (r + 1) nf = 0 ∧ tr.cell T_NODE (r + 1) pos = tr.cell T_NODE r pos + 1 ∧
    ∀ x ∈ nodeConst, tr.cell T_NODE (r + 1) x = tr.cell T_NODE r x := by
  have hr' : r < tr.height T_NODE := by omega
  have h1 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c nl))) (Dsl.not (n act)))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h2 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c nl))) (n nf)) (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h3 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c nl))) (sub (n pos) (.add (c pos) (k 1))))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  simp only [eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [ha, hl] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_⟩
  have h4 := con hL hr' (e := .mul (.mul (c act) (Dsl.not (c nl))) (sub (n x) (c x)))
    (mem_of (Or.inr (Or.inr (Or.inl (by
      unfold cTrans; simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨x, hx, rfl⟩))))))
  simp only [eval_mul, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h4
  rw [ha, hl] at h4; grind

/-- After a node end. -/
theorem atEnd {r : Nat} (hr : r + 1 < tr.height T_NODE) (hl : tr.cell T_NODE r nl = 1) :
    tr.cell T_NODE (r + 1) act + tr.cell T_NODE (r + 1) sumr = 1 ∧
    (tr.cell T_NODE (r + 1) act = 1 → tr.cell T_NODE (r + 1) nf = 1 ∧ tr.cell T_NODE (r + 1) nid = tr.cell T_NODE r nid + 1) := by
  have hr' : r < tr.height T_NODE := by omega
  have h1 := con hL hr' (e := .mul (c nl) (sub (k 1) (.add (n act) (n sumr)))) (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h2 := con hL hr' (e := mul3 (c nl) (n act) (Dsl.not (n nf))) (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h3 := con hL hr' (e := mul3 (c nl) (n act) (sub (n nid) (.add (c nid) (k 1))))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [hl] at h1 h2 h3
  refine ⟨by grind, fun h => ?_⟩
  rw [h] at h2 h3; exact ⟨by grind, by grind⟩

/-- SUM / padding rows are followed by padding. -/
theorem afterInactive {r : Nat} (hr : r + 1 < tr.height T_NODE) (ha : tr.cell T_NODE r act = 0) :
    tr.cell T_NODE (r + 1) act = 0 ∧ tr.cell T_NODE (r + 1) sumr = (if tr.cell T_NODE r sumr = 1 then 0 else tr.cell T_NODE (r + 1) sumr) ∧
    (tr.cell T_NODE r sumr = 0 → tr.cell T_NODE (r + 1) sumr = 0) := by
  have hr' : r < tr.height T_NODE := by omega
  have ht : ¬ (r + 1 = tr.height T_NODE) := by omega
  have h1 := con hL hr' (e := mul3 .isTransition (c sumr) (n act)) (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h2 := con hL hr' (e := mul3 .isTransition (c sumr) (n sumr)) (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h3 := con hL hr' (e := mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n act))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  have h4 := con hL hr' (e := mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n sumr))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_add, eval_isTransition, if_neg ht, nxt hr]
    at h1 h2 h3 h4
  rw [ha] at h3 h4
  rcases isBool hL hr' (x := sumr) (by simp [boolCols]) with hs | hs
  · rw [hs] at h3 h4; exact ⟨by grind, by simp [hs], fun _ => by grind⟩
  · rw [hs] at h1 h2; exact ⟨by grind, by simp [hs]; grind, fun h => by rw [hs] at h; exact absurd h fp_one_ne_zero⟩

/-- The size counter (non-duplicate record bytes). -/
theorem sizeFacts {r : Nat} (hr : r < tr.height T_NODE) (hr1 : r + 1 < tr.height T_NODE) :
    tr.cell T_NODE (r + 1) sz = tr.cell T_NODE r sz + tr.cell T_NODE r act * (1 - tr.cell T_NODE r dup) := by
  have h1 := con hL hr (e := .mul .isTransition (sub (n sz) (.add (c sz) (.mul (c act) (Dsl.not (c dup))))))
    (by simp [NodeV3.constraints, NodeV3.cTrans])
  simp only [eval_mul, eval_c, eval_n, eval_sub, eval_add, eval_not, eval_isTransition,
    if_neg (show ¬ r + 1 = tr.height T_NODE by omega), nxt hr1] at h1
  grind

end ZkFormal.NearV3.NodeProof3
