import ZkFormal.Near.Render.Proof.NodeCells

/-!
# ZkFormal.Near.Render.Proof.NodeRowT — bus traffic of one node-table row
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace NodeCells
open NodeGen

theorem ofNat1' : Fp.ofNat 1 = 1 := rfl
theorem ofNat0' : Fp.ofNat 0 = 0 := rfl

theorem ofNat_succ' (x : Nat) : Fp.ofNat x + 1 = Fp.ofNat (x + 1) := by rw [← ofNat1', ofNat_add']

theorem lo_fp (a b c d : Nat) : 1 * Fp.ofNat a + (Fp.ofNat (2 * b) + (Fp.ofNat (4 * c) + (Fp.ofNat (8 * d) + 0))) =
    Fp.ofNat (a + 2 * b + 4 * c + 8 * d) := by
  rw [← ofNat1', ofNat_mul', Nat.one_mul, ← ofNat0', ofNat_add', ofNat_add', ofNat_add', ofNat_add']
  congr 1; omega

def V (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (col : Nat) : Fp := Fp.ofNat (rowCell I u r col)

section
variable {I : Info} {u : Std.HashMap Edge Nat} {r : NRec} {tr : Trace Fp} {q : Nat} {pub : List Fp}
  (hc : ∀ col, col < 163 → tr.cell T_NODE q col = Fp.ofNat (rowCell I u r col))
include hc

theorem row_bytes : rowTraffic Node.interactions tr T_NODE q pub B_BYTES true =
    [Msg.toFp [msgId K_NPRE r.n, r.pos, r.b], Msg.toFp [msgId K_NPOST r.n, r.pos, r.pb]] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  simp only [eval_c, eval_mid, eval_k, Node.act, Node.nid, Node.pos, Node.b, Node.pb, hc 0 (by decide),
    hc 4 (by decide), hc 5 (by decide), hc 8 (by decide), hc 9 (by decide), rc_act, rc_nid, rc_pos, rc_b, rc_pb]
  simp [Msg.toFp, msgId, natCast_eq, K_NPRE, K_NPOST, ofNat1']

theorem row_vslot : rowTraffic Node.interactions tr T_NODE q pub B_VSLOT false =
    if V I u r 144 = 1 then [[V I u r 4]] else [] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  simp only [eval_c, Node.gV, Node.nid, hc 144 (by decide), hc 4 (by decide), V]
  by_cases h : Fp.ofNat (rowCell I u r 144) = 1 <;> simp [h]

theorem row_parentS : rowTraffic Node.interactions tr T_NODE q pub B_PARENT true =
    if V I u r 143 = 1 then [[V I u r 137, Fp.ofNat (rowCell I u r 7 + 1), V I u r 138, V I u r 154]] else [] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  simp only [eval_c, eval_add, eval_k, Node.gP, Node.cid, Node.depth, Node.clen, Node.cres, hc 143 (by decide),
    hc 137 (by decide), hc 7 (by decide), hc 138 (by decide), hc 154 (by decide), V]
  by_cases h : Fp.ofNat (rowCell I u r 143) = 1 <;> simp [h, natCast_eq, ofNat1', ofNat_succ']

theorem row_parentR : rowTraffic Node.interactions tr T_NODE q pub B_PARENT false =
    if V I u r 1 - (if q = 0 then 1 else 0) = 1 then [[V I u r 4, V I u r 7, V I u r 6, V I u r 153]] else [] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  simp only [eval_c, eval_sub, eval_isFirst, Node.nf, Node.nid, Node.depth, Node.len, Node.res, hc 1 (by decide),
    hc 4 (by decide), hc 7 (by decide), hc 6 (by decide), hc 153 (by decide), V]
  by_cases h : Fp.ofNat (rowCell I u r 1) - (if q = 0 then 1 else 0) = 1 <;> simp [h]

theorem row_digest : rowTraffic Node.interactions tr T_NODE q pub B_DIGEST false =
    (if V I u r 142 = 1 then [V I u r 140 :: V I u r 141 :: (List.range 32).map fun i => V I u r (72 + i)] else []) ++
    (if V I u r 142 = 1 then [Fp.ofNat (rowCell I u r 140 + 1) :: V I u r 141 :: (List.range 32).map fun i => V I u r (104 + i)]
      else []) ++
    (if q = 0 then [((K_NPRE : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_PRE + i) 0,
      ((K_NPOST : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_POST + i) 0] else []) := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  have h1 : ((List.range 32).map fun i => tr.cell T_NODE q (Node.reg i)) = (List.range 32).map fun i => V I u r (72 + i) :=
    List.map_congr_left fun i hi => hc _ (by have := List.mem_range.1 hi; simp [Node.reg]; omega)
  have h2 : ((List.range 32).map fun i => tr.cell T_NODE q (Node.preg i)) = (List.range 32).map fun i => V I u r (104 + i) :=
    List.map_congr_left fun i hi => hc _ (by have := List.mem_range.1 hi; simp [Node.preg]; omega)
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.map_map,
    Function.comp_def, eval_c, eval_add, eval_k, eval_pub, eval_isFirst, Node.gD, Node.dI, Node.dL, Node.len]
  simp only [hc 142 (by decide), hc 140 (by decide), hc 141 (by decide), hc 6 (by decide), h1, h2]
  simp only [V]
  by_cases hq : q = 0 <;> by_cases h : Fp.ofNat (rowCell I u r 142) = 1 <;>
    simp [hq, h, ofNat1', natCast_eq, ofNat_succ']


/-- Low nibble from the `lbit` cells. -/
def loN (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) : Nat :=
  rowCell I u r 33 + 2 * rowCell I u r 34 + 4 * rowCell I u r 35 + 8 * rowCell I u r 36

theorem row_edge (s : Bool) : rowTraffic Node.interactions tr T_NODE q pub B_EDGE s =
    (if V I u r 145 = 1 then [[V I u r 4, V I u r 146, V I u r 147, V I u r 148, V I u r 149,
      if s then 0 else V I u r 150]] else []) ++
    (if V I u r 160 = 1 then [[V I u r 4, Fp.ofNat (2 * rowCell I u r 23 + rowCell I u r 27 + 1), Fp.ofNat (loN I u r),
      V I u r 161, V I u r 162, if s then 0 else V I u r 151]] else []) := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, B_BYTES, B_DIGEST,
    B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff, and_true, and_false, false_and, if_false, if_true,
    List.append_nil, List.nil_append, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_map]
  cases s <;>
  simp only [Bool.false_eq_true, if_false, if_true, and_true, and_false, List.append_nil, List.nil_append,
    Node.edgeA, Node.edgeB, Node.kiE, Node.loE, bits, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, eval_c, eval_add, eval_k, eval_smul, eval_sum_cons, eval_sum_nil,
    Node.gA, Node.gB, Node.nid, Node.aI, Node.aS, Node.aN, Node.aJ, Node.mA, Node.mB, Node.bN, Node.bJ, Node.idx,
    Node.odd, Node.lbit] <;>
  simp only [Nat.reduceAdd, Nat.reducePow, hc 4 (by decide), hc 145 (by decide), hc 146 (by decide), hc 147 (by decide), hc 148 (by decide), hc 149 (by decide), hc 150 (by decide), hc 151 (by decide), hc 160 (by decide), hc 161 (by decide), hc 162 (by decide), hc 23 (by decide), hc 27 (by decide), hc 33 (by decide), hc 34 (by decide), hc 35 (by decide), hc 36 (by decide)] <;>
  simp only [V, loN] <;>
  by_cases h1 : Fp.ofNat (rowCell I u r 145) = 1 <;> by_cases h2 : Fp.ofNat (rowCell I u r 160) = 1 <;>
  simp [h1, h2, natCast_eq, ofNat_add', ofNat_mul', ofNat1', ofNat0'] <;>
  exact ⟨ofNat_succ' _, lo_fp _ _ _ _⟩

end

theorem row_other {tr : Trace Fp} {q : Nat} {pub : List Fp} (b : Nat) (s : Bool)
    (h1 : ¬ (b = B_BYTES ∧ s = true)) (h2 : ¬ (b = B_DIGEST ∧ s = false)) (h3 : b ≠ B_PARENT)
    (h4 : ¬ (b = B_VSLOT ∧ s = false)) (h5 : b ≠ B_EDGE) :
    rowTraffic Node.interactions tr T_NODE q pub b s = [] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil]
  cases s <;> simp_all [B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE] <;> omega

/-- A row with all gates off (`SUM`, padding). -/
theorem row_off {tr : Trace Fp} {q : Nat} {pub : List Fp} (hq : q ≠ 0)
    (hz : ∀ col, col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 143 ∨ col = 144 ∨ col = 145 ∨ col = 160 →
      tr.cell T_NODE q col = 0) (b : Nat) (s : Bool) :
    rowTraffic Node.interactions tr T_NODE q pub b s = [] := by
  simp only [rowTraffic, Node.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, multNat_one,
    eval_c, eval_sub, eval_isFirst, Node.act, Node.gD, Node.gP, Node.nf, Node.gV, Node.gA, Node.gB, hq,
    hz 0 (by simp), hz 1 (by simp), hz 142 (by simp), hz 143 (by simp), hz 144 (by simp), hz 145 (by simp),
    hz 160 (by simp)]
  have : (0 : Fp) - 0 = 0 := by decide
  simp [this]

end NodeCells

end ZkFormal.Near.Render
