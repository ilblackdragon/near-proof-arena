import ZkFormal.Near.Render.Proof.MrkRecs
import ZkFormal.Near.Render.Proof.SortLocal

/-!
# ZkFormal.Near.Render.Proof.MrkLocal — `MrkLocalStmt`

Every row is the root row, a node row (record `(j, i, h, p)`), or padding;
the constraints are checked per row case (`caseIn`: inside a segment,
`caseSame`/`caseNext`: a node followed by the next node of its level / the
first node of the next level, `caseTop`: the top node's last row,
`caseRoot`, `casePad`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkLocal
open SortLocal (ofNat0 ofNat1)
open MrkGen

theorem inv_fact {s : Nat} (h1 : 2 ≤ s) (h2 : s ≤ 256) :
    (Fp.ofNat s - 1) * Fp.ofNat (invP (s - 1)) = 1 := by
  have e : Fp.ofNat s - 1 = Fp.ofNat (s - 1) := by
    have : Fp.ofNat s = Fp.ofNat (s - 1) + 1 := by rw [← ofNat1, ofNat_add']; congr 1; omega
    rw [this]; grind
  have hne : Fp.ofNat (s - 1) ≠ 0 := by
    intro h0
    have := congrArg Fp.toNat h0
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [show ZkFormal.Algebra.P = 2013265921 from rfl]; omega)] at this
    rw [Fp.toNat_zero] at this; omega
  rw [e, invP, Fp.ofNat_toNat, Fp.mul_inv_cancel hne]

theorem nodeCell_reg (n : Nat) (lv : List (List MNode)) (j i p x : Nat) (hx : x < 32) :
    nodeCell n lv (j, i, true, p) (Mrk.reg x) =
      (if p / 32 = 0 then (lv.getD (j - 1) []).getD (2 * i) default
        else (lv.getD (j - 1) []).getD (2 * i + 1) default).dig.getD (p % 32 + x) 0 := by
  simp only [nodeCell, Mrk.reg, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.mj,
    Mrk.sg, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.cId, Mrk.cLen, Mrk.mi, Mrk.gM, Mrk.gO, Mrk.oId,
    Mrk.oLen, and_self, show 26 + x ≠ 0 by omega, show 26 + x ≠ 1 by omega, show 26 + x ≠ 2 by omega, show 26 + x ≠ 3 by omega, show 26 + x ≠ 4 by omega, show 26 + x ≠ 5 by omega, show 26 + x ≠ 6 by omega, show 26 + x ≠ 7 by omega, show 26 + x ≠ 8 by omega, show 26 + x ≠ 9 by omega, show 26 + x ≠ 10 by omega, show 26 + x ≠ 11 by omega, show 26 + x ≠ 12 by omega, show 26 + x ≠ 13 by omega, show 26 + x ≠ 14 by omega, show 26 + x ≠ 15 by omega, show 26 + x ≠ 16 by omega, show 26 + x ≠ 17 by omega, show 26 + x ≠ 18 by omega, show 26 + x ≠ 19 by omega, show 26 + x ≠ 20 by omega, show 26 + x ≠ 21 by omega, show 26 + x ≠ 22 by omega, show 26 + x ≠ 23 by omega, show 26 + x ≠ 24 by omega, show 26 + x ≠ 25 by omega, if_false, if_true, show 26 ≤ 26 + x ∧ 26 + x < 26 + 32 by omega, Nat.add_sub_cancel_left]

section cases
variable {tr : Trace Fp} {pub : List Fp} {H q : Nat} {n : Nat} {lv : List (List MNode)}
  (hH : tr.height T_MRK = H)
include hH

set_option maxHeartbeats 4000000 in
/-- Inside a hashed segment. -/
theorem caseIn {j i p : Nat} (hok : RecOk n (j, i, true, p)) (hp : p < 63) (hq0 : q ≠ 0) (hql : q + 1 < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK q col = Fp.ofNat (nodeCell n lv (j, i, true, p) col))
    (hB : ∀ col, col < 58 → tr.cell T_MRK (q + 1) col = Fp.ofNat (nodeCell n lv (j, i, true, p + 1) col))
    (hn1 : 1 ≤ n) (hn256 : n ≤ 256)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK q pub = 0 := by
  have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hql
  have hql' : ¬ q + 1 = H := by omega
  have f1 : p % 32 ≠ 31 → (p + 1) % 32 = p % 32 + 1 ∧ (p + 1) / 32 = p / 32 := by intro h; omega
  obtain ⟨hj1, hjn, hi, hh, hp64, _⟩ := hok
  simp only at hj1 hjn hi hh hp64
  have hsz : size n j = (size n (j - 1) + 1) / 2 := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; rfl
  have hinv : size n j ≠ 1 → (Fp.ofNat (size n j) - 1) * Fp.ofNat (invP (size n j - 1)) = 1 := fun h =>
    inv_fact (by have := size_pos n hn1 j; omega) (by have := size_le n j; omega)
  simp only [Mrk.constraints, Mrk.nodeConst, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (((⟨x, hx, rfl⟩ | h) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · have hc1 := hA Mrk.sg (by decide)
    have hc2 := hA Mrk.wl (by decide)
    have hc3 := hB (Mrk.reg x) (by simp only [Mrk.reg]; omega)
    have hc4 := hA (Mrk.reg (x + 1)) (by simp only [Mrk.reg]; omega)
    simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, hH, hn', hc1, hc2, hc3, hc4,
      nodeCell_reg n lv j i _ x (by omega), nodeCell_reg n lv j i _ (x + 1) (by omega)]
    simp only [nodeCell, Mrk.sg, Mrk.wl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv,
      Mrk.mj, Mrk.pw, Mrk.wn, Mrk.wf, Nat.reduceEqDiff, if_false, if_true, ofNat1]
    by_cases h31 : p % 32 = 31
    · simp only [h31, if_true, ofNat1]; grind
    · obtain ⟨g1, g2⟩ := f1 h31
      simp only [h31, if_false, ofNat0, g1, g2, show p % 32 + 1 + x = p % 32 + (x + 1) by omega]
      grind

end cases

end MrkLocal

end ZkFormal.Near.Render
