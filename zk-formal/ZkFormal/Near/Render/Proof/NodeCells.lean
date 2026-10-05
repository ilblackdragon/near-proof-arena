import ZkFormal.Near.Render.Proof.NodeLayout

/-!
# ZkFormal.Near.Render.Proof.NodeCells — the node table of `render`, cell by cell

`node_render`: the node table is `mkTab (2^L) 163 (NodeGen.cell …)`; the
cells of a node row by column (`rc_*`, all `rfl`); the bus traffic of a node
row (`row_traffic`: `nodeRowT`, one item per interaction).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace NodeCells
open NodeGen

/-! ## The table -/

abbrev recsA (I : Info) : Array NRec := (recsOf I).toArray
abbrev totalOf (I : Info) : Nat := szBefore I I.ns.size
abbrev LOf (I : Info) : Nat := logOf ((recsOf I).length + 1)

theorem node_render (c : Claim) (e : Ext) :
    (render c e).log T_NODE = LOf (mkInfo c e) ∧ (render c e).height T_NODE = 2 ^ LOf (mkInfo c e) ∧
    ∀ q col, q < 2 ^ LOf (mkInfo c e) → col < 163 →
      (render c e).cell T_NODE q col = Fp.ofNat (cell (mkInfo c e) (edgeUses (walksOf (mkInfo c e)))
        (recsA (mkInfo c e)) (totalOf (mkInfo c e)) q col) := by
  have hp : partOf (bundle c e) T_NODE = mkTab (2 ^ LOf (mkInfo c e)) Node.width
      (cell (mkInfo c e) (edgeUses (walksOf (mkInfo c e))) (recsA (mkInfo c e)) (totalOf (mkInfo c e))) := by
    simp only [partOf, T_NODE, bundle, nodeRowsAll, LOf, recsA, totalOf, List.size_toArray]
  exact render_mkTab (by decide) (by decide) hp

/-! ## Cells of a node row -/

section
variable (I : Info) (u : Std.HashMap Edge Nat) (r : NRec)

theorem rc_act : rowCell I u r 0 = 1 := rfl
theorem rc_nf : rowCell I u r 1 = b2n (r.pos = 0) := rfl
theorem rc_nl : rowCell I u r 2 = b2n (r.pos + 1 = (I.pre.getD r.n []).length) := rfl
theorem rc_sumr : rowCell I u r 3 = 0 := rfl
theorem rc_nid : rowCell I u r 4 = r.n := rfl
theorem rc_pos : rowCell I u r 5 = r.pos := rfl
theorem rc_len : rowCell I u r 6 = (I.pre.getD r.n []).length := rfl
theorem rc_depth : rowCell I u r 7 = I.depth.getD r.n 0 := rfl
theorem rc_b : rowCell I u r 8 = r.b := rfl
theorem rc_pb : rowCell I u r 9 = r.pb := rfl
theorem rc_tl : rowCell I u r 10 = (typeOf (I.nodeAt r.n)).1 := rfl
theorem rc_te : rowCell I u r 11 = (typeOf (I.nodeAt r.n)).2.1 := rfl
theorem rc_tb1 : rowCell I u r 12 = (typeOf (I.nodeAt r.n)).2.2.1 := rfl
theorem rc_tb2 : rowCell I u r 13 = (typeOf (I.nodeAt r.n)).2.2.2 := rfl
theorem rc_state (x : Nat) (h1 : 14 ≤ x) (h2 : x < 23) : rowCell I u r x = b2n (r.f.state = x) := by
  unfold rowCell
  rw [if_pos (by omega)]
  match x, h1, h2 with
  | 14, _, _ | 15, _, _ | 16, _, _ | 17, _, _ | 18, _, _ | 19, _, _ | 20, _, _ | 21, _, _ | 22, _, _ => rfl
  | x + 23, _, h => omega
theorem rc_idx : rowCell I u r 23 = r.idx := rfl
theorem rc_fs : rowCell I u r 24 = b2n (r.idx = 0) := rfl
theorem rc_fe : rowCell I u r 25 = b2n (r.idx + 1 = r.f.len (hplenOf (I.nodeAt r.n))) := rfl
theorem rc_hplen : rowCell I u r 26 = hplenOf (I.nodeAt r.n) := rfl
theorem rc_odd : rowCell I u r 27 = oddOf (I.nodeAt r.n) := rfl
theorem rc_nokey : rowCell I u r 28 = nokeyOf (I.nodeAt r.n) := rfl
theorem rc_hbit (i : Nat) (hi : i < 4) :
    rowCell I u r (29 + i) = if r.f.nib then bitOf (r.b / 16) i else 0 := by
  simp only [rowCell, show ¬ 29 + i < 29 by omega, show 29 + i < 33 by omega, if_false, if_true,
    Nat.add_sub_cancel_left]
theorem rc_lbit (i : Nat) (hi : i < 4) :
    rowCell I u r (33 + i) = if r.f.nib then bitOf (r.b % 16) i else 0 := by
  simp only [rowCell, show ¬ 33 + i < 29 by omega, show ¬ 33 + i < 33 by omega, show 33 + i < 37 by omega,
    if_false, if_true, Nat.add_sub_cancel_left]
theorem rc_bm (i : Nat) (hi : i < 16) : rowCell I u r (37 + i) = bitOf (bmvOf (I.nodeAt r.n)) i := by
  simp only [rowCell, show ¬ 37 + i < 29 by omega, show ¬ 37 + i < 33 by omega, show ¬ 37 + i < 37 by omega,
    show 37 + i < 53 by omega, if_false, if_true, Nat.add_sub_cancel_left]
theorem rc_nochild : rowCell I u r 53 = nochildOf (I.nodeAt r.n) := rfl
theorem rc_jj (i : Nat) (hi : i < 16) :
    rowCell I u r (54 + i) = (match r.f.chw with | some w => b2n (w.slot = some i) | none => 0) := by
  simp only [rowCell, show ¬ 54 + i < 29 by omega, show ¬ 54 + i < 33 by omega, show ¬ 54 + i < 37 by omega,
    show ¬ 54 + i < 53 by omega, show ¬ 54 + i = 53 by omega, show 54 + i < 70 by omega, if_false, if_true,
    Nat.add_sub_cancel_left]
  generalize r.f.chw = x; cases x <;> rfl
theorem rc_w : rowCell I u r 70 = (match r.f.chw with | some w => w.w | none => 0) := rfl
theorem rc_lastw : rowCell I u r 71 = (match r.f.chw with | some w => b2n w.lastw | none => 0) := rfl
theorem rc_reg (i : Nat) (hi : i < 32) :
    rowCell I u r (72 + i) = (match r.f.win with | some w => w.pre.getD (r.idx + i) 0 | none => 0) := by
  simp only [rowCell, show ¬ 72 + i < 29 by omega, show ¬ 72 + i < 33 by omega, show ¬ 72 + i < 37 by omega,
    show ¬ 72 + i < 53 by omega, show ¬ 72 + i = 53 by omega, show ¬ 72 + i < 70 by omega,
    show ¬ 72 + i = 70 by omega, show ¬ 72 + i = 71 by omega, show 72 + i < 104 by omega, if_false, if_true,
    Nat.add_sub_cancel_left]
  generalize r.f.win = x; cases x <;> rfl
theorem rc_preg (i : Nat) (hi : i < 32) :
    rowCell I u r (104 + i) = (match r.f.win with | some w => w.post.getD (r.idx + i) 0 | none => 0) := by
  simp only [rowCell, show ¬ 104 + i < 29 by omega, show ¬ 104 + i < 33 by omega, show ¬ 104 + i < 37 by omega,
    show ¬ 104 + i < 53 by omega, show ¬ 104 + i = 53 by omega, show ¬ 104 + i < 70 by omega,
    show ¬ 104 + i = 70 by omega, show ¬ 104 + i = 71 by omega, show ¬ 104 + i < 104 by omega,
    show 104 + i < 136 by omega, if_false, if_true, Nat.add_sub_cancel_left]
  generalize r.f.win = x; cases x <;> rfl
theorem rc_rv : rowCell I u r 136 = (match r.f.chw with | some w => b2n w.look | none => 0) := rfl
theorem rc_cid : rowCell I u r 137 = (match r.f.chw with | some w => w.cid | none => 0) := rfl
theorem rc_clen : rowCell I u r 138 = (match r.f.chw with | some w => w.clen | none => 0) := rfl
theorem rc_tv : rowCell I u r 139 = b2n (I.nodeAt r.n).touched := rfl
theorem rc_dI : rowCell I u r 140 = (match digOf r with | some d => d.1 | none => 0) := rfl
theorem rc_dL : rowCell I u r 141 = (match digOf r with | some d => d.2.1 | none => 0) := rfl
theorem rc_gD : rowCell I u r 142 = (match digOf r with | some _ => 1 | none => 0) := rfl
theorem rc_gP : rowCell I u r 143 = (match digOf r with | some (_, _, true) => 1 | _ => 0) := rfl
theorem rc_gV : rowCell I u r 144 = b2n (r.pos = 0 ∧ (I.nodeAt r.n).touched = true) := rfl
theorem rc_gA : rowCell I u r 145 = gateCell (edgeAOf I r) := rfl
theorem rc_aI : rowCell I u r 146 = edgeCell (edgeAOf I r) u 1 := rfl
theorem rc_aS : rowCell I u r 147 = edgeCell (edgeAOf I r) u 2 := rfl
theorem rc_aN : rowCell I u r 148 = edgeCell (edgeAOf I r) u 3 := rfl
theorem rc_aJ : rowCell I u r 149 = edgeCell (edgeAOf I r) u 4 := rfl
theorem rc_mA : rowCell I u r 150 = multCell (edgeAOf I r) u := rfl
theorem rc_mB : rowCell I u r 151 = multCell (edgeBOf I r) u := rfl
theorem rc_sz : rowCell I u r 152 = szBefore I r.n + r.pos := rfl
theorem rc_res : rowCell I u r 153 = I.res.getD r.n r.n := rfl
theorem rc_cres : rowCell I u r 154 = (match r.f.chw with | some w => w.cres | none => 0) := rfl
theorem rc_xres : rowCell I u r 155 = xresOf I (I.nodeAt r.n) := rfl
theorem rc_xrv : rowCell I u r 156 = b2n (xrvOf (I.nodeAt r.n)) := rfl
theorem rc_xdead : rowCell I u r 157 = b2n (xdeadOf (I.nodeAt r.n)) := rfl
theorem rc_xlast0 : rowCell I u r 158 = b2n (xlast0Of (I.nodeAt r.n)) := rfl
theorem rc_eext : rowCell I u r 159 = b2n (eextOf' (I.nodeAt r.n)) := rfl
theorem rc_gB : rowCell I u r 160 = gateCell (edgeBOf I r) := rfl
theorem rc_bN : rowCell I u r 161 = edgeCell (edgeBOf I r) u 3 := rfl
theorem rc_bJ : rowCell I u r 162 = edgeCell (edgeBOf I r) u 4 := rfl

end

end NodeCells

end ZkFormal.Near.Render
