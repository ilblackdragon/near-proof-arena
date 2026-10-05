import ZkFormal.Near.Render.Proof.NodeSeq
import ZkFormal.Near.Render.Proof.NodeEv

/-!
# ZkFormal.Near.Render.Proof.NodeRow0 — the node table's constraints, row by row

`constr_of`: the constraints of the honest node table hold once every group of
constraints vanishes over the integers on every row (`GroupOk`).  Rows are
node rows `mkR I n p` (`row_node`, `q = off n + p`), the `SUM` row (`q = R`)
or padding (`q > R`); `X_node`/`X_sum`/`X_pad` give their cells.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq

section
variable (c : Claim) (e : Ext)

abbrev U : Std.HashMap Edge Nat := edgeUses (walksOf (mkInfo c e))
abbrev RN : Nat := (recsOf (mkInfo c e)).length
abbrev HN : Nat := 2 ^ LOf (mkInfo c e)

/-- Integer cells of the honest node table. -/
def X (q x : Nat) : Int := (cell (mkInfo c e) (U c e) (recsA (mkInfo c e)) (totalOf (mkInfo c e)) q x : Int)

/-- A group of constraints vanishes over the integers on every row. -/
def GroupOk (es : List Expr) : Prop :=
  ∀ q, q < HN c e → ∀ (C D P : Nat → Int), (∀ x, x < 163 → C x = X c e q x) →
    (∀ x, x < 163 → D x = X c e ((q + 1) % HN c e) x) →
    ∀ ex ∈ es, ev C D (if q = 0 then 1 else 0) (if q + 1 = HN c e then 1 else 0)
      (if q + 1 = HN c e then 0 else 1) P ex = 0

theorem groupOk_append {a b : List Expr} (ha : GroupOk c e a) (hb : GroupOk c e b) : GroupOk c e (a ++ b) := by
  intro q hq C D P hC hD ex hex
  rcases List.mem_append.1 hex with h | h
  · exact ha q hq C D P hC hD ex h
  · exact hb q hq C D P hC hD ex h

end

theorem constr_of {c : WfClaim} {e : Ext} (h : GroupOk c.1 e Node.constraints) :
    ∀ r, r < (render c.1 e).height T_NODE → ∀ ex ∈ Node.constraints,
      ex.eval (render c.1 e) T_NODE r (publicOf c) = 0 := by
  obtain ⟨_, hH, hcell⟩ := node_render c.1 e
  intro q hq ex hex
  rw [hH] at hq
  have hq' : (q + 1) % 2 ^ LOf (mkInfo c.1 e) < 2 ^ LOf (mkInfo c.1 e) := Nat.mod_lt _ (Nat.two_pow_pos _)
  apply eval_zero_of_ev (cellsI_ok (fun x hx => hcell q x hq hx))
    (by rw [hH]; exact cellsI_ok (fun x hx => hcell _ x hq' hx))
  rw [hH]
  exact h q hq _ _ _ (fun x hx => by simp [cellsI, hx, X]) (fun x hx => by simp [cellsI, hx, X]) ex hex

/-! ## Row kinds -/

section
variable {c : Claim} {e : Ext}

theorem X_node {q : Nat} (hq : q < RN c e) (x : Nat) :
    X c e q x = (rowCell (mkInfo c e) (U c e) ((recsOf (mkInfo c e)).getD q default) x : Int) := by
  simp [X, cell, recsA, hq, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem X_sum (x : Nat) : X c e (RN c e) x = (sumCell (totalOf (mkInfo c e)) x : Int) := by
  simp [X, cell, recsA]

theorem X_pad {q : Nat} (hq : RN c e < q) (x : Nat) : X c e q x = (padCell (totalOf (mkInfo c e)) x : Int) := by
  have hq' : (recsOf (mkInfo c e)).length < q := hq
  simp [X, cell, recsA, show ¬ q < (recsOf (mkInfo c e)).length by omega,
    show q ≠ (recsOf (mkInfo c e)).length by omega]

theorem RN_off : RN c e = off (mkInfo c e) e.ns.length := by
  simp only [RN, recsOf, NodeInfo.info_N, recs_len']

theorem RN_lt : RN c e + 1 ≤ HN c e := le_pow_logOf _

theorem off_pos {I : Info} {n : Nat} (h : 0 < n) : 0 < off I n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := layN_pos I m; rw [← nodeRecs_len] at this
  simp only [off]; omega

theorem recs_getD (n p : Nat) (hn : n < e.ns.length) (hp : p < (NodeLay.layN (mkInfo c e) n).length) :
    (recsOf (mkInfo c e)).getD (off (mkInfo c e) n + p) default = mkR (mkInfo c e) n p := by
  rw [recsOf, NodeInfo.info_N, recs_get' _ _ hn (by rw [nodeRecs_len]; exact hp), NodeLay.nodeRecs_eq]
  simp [List.getD_eq_getElem?_getD, hp]

/-- A node row: node `n`, position `p`. -/
theorem row_node {q : Nat} (hq : q < RN c e) :
    ∃ n p, n < e.ns.length ∧ p < (NodeLay.layN (mkInfo c e) n).length ∧
      (recsOf (mkInfo c e)).getD q default = mkR (mkInfo c e) n p ∧ q = off (mkInfo c e) n + p := by
  rw [RN_off] at hq
  obtain ⟨n, p, h1, h2, h3⟩ := recs_cover' _ _ hq
  rw [nodeRecs_len] at h2
  exact ⟨n, p, h1, h2, by rw [h3, recs_getD n p h1 h2], h3⟩

theorem first_row {n p : Nat} : off (mkInfo c e) n + p = 0 ↔ n = 0 ∧ p = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn; simp [off] at h; exact ⟨rfl, h⟩
    · have := off_pos (I := mkInfo c e) (Nat.pos_of_ne_zero hn); omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- The row after node row `(n, p)`. -/
theorem next_row {n p : Nat} (hn : n < e.ns.length) (hp : p < (NodeLay.layN (mkInfo c e) n).length) :
    (p + 1 < (NodeLay.layN (mkInfo c e) n).length ∧ off (mkInfo c e) n + p + 1 < RN c e ∧
      (recsOf (mkInfo c e)).getD (off (mkInfo c e) n + p + 1) default = mkR (mkInfo c e) n (p + 1)) ∨
    (p + 1 = (NodeLay.layN (mkInfo c e) n).length ∧ n + 1 < e.ns.length ∧
      off (mkInfo c e) n + p + 1 < RN c e ∧
      (recsOf (mkInfo c e)).getD (off (mkInfo c e) n + p + 1) default = mkR (mkInfo c e) (n + 1) 0) ∨
    (p + 1 = (NodeLay.layN (mkInfo c e) n).length ∧ n + 1 = e.ns.length ∧ off (mkInfo c e) n + p + 1 = RN c e) := by
  have hL : ∀ m, (nodeRecs (mkInfo c e) m).length = (NodeLay.layN (mkInfo c e) m).length := nodeRecs_len _
  have hoff : off (mkInfo c e) (n + 1) = off (mkInfo c e) n + (NodeLay.layN (mkInfo c e) n).length := by
    simp only [off, hL]
  have hmono := off_mono (mkInfo c e) (show n + 1 ≤ e.ns.length by omega)
  rw [RN_off]
  by_cases h1 : p + 1 < (NodeLay.layN (mkInfo c e) n).length
  · left
    refine ⟨h1, by omega, ?_⟩
    rw [Nat.add_assoc, recs_getD n (p + 1) hn h1]
  · right
    by_cases h2 : n + 1 < e.ns.length
    · left
      have hl1 := layN_pos (mkInfo c e) (n + 1)
      have hmono2 := off_mono (mkInfo c e) (show n + 2 ≤ e.ns.length by omega)
      have hoff2 : off (mkInfo c e) (n + 2) = off (mkInfo c e) (n + 1) + (NodeLay.layN (mkInfo c e) (n + 1)).length := by
        simp only [off, hL]
      refine ⟨by omega, h2, by omega, ?_⟩
      rw [show off (mkInfo c e) n + p + 1 = off (mkInfo c e) (n + 1) + 0 by omega, recs_getD (n + 1) 0 h2 (by omega)]
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [show e.ns.length = n + 1 by omega, hoff]; omega

end

end NodeRow

end ZkFormal.Near.Render
