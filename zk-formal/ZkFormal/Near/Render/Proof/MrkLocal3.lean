import ZkFormal.Near.Render.Proof.MrkLocal

/-!
# ZkFormal.Near.Render.Proof.MrkLocal3 — the root row and padding rows
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkLocal
open SortLocal (ofNat0 ofNat1)
open MrkGen

section cases
variable {tr : Trace Fp} {pub : List Fp} {H : Nat} {n : Nat} {lv : List (List MNode)}
  (hH : tr.height T_MRK = H)
include hH

set_option maxHeartbeats 4000000 in
/-- The root row (row `0`), followed by node `(1, 0)`. -/
theorem caseRoot (hql : 1 < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK 0 col = Fp.ofNat (rootCell n lv col))
    (hB : ∀ col, col < 58 → tr.cell T_MRK (0 + 1) col = Fp.ofNat (nodeCell n lv (1, 0, decide (1 < n), 0) col))
    (hpn : Mrk.nPubE.eval tr T_MRK 0 pub = Fp.ofNat n) (hn1 : 1 ≤ n) (hn256 : n ≤ 256)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK 0 pub = 0 := by
  have hn' : (0 + 1) % H = 0 + 1 := Nat.mod_eq_of_lt hql
  have hql' : ¬ 0 + 1 = H := by omega
  have hs0 : size n (1 - 1) = n := rfl
  have hqb1 : qBase n 1 = 0 := rfl
  have hinv : size n 1 ≠ 1 → (Fp.ofNat (size n 1) - 1) * Fp.ofNat (invP (size n 1 - 1)) = 1 := fun h =>
    inv_fact (by have := size_pos n hn1 1; omega) (by have := size_le n 1; omega)
  have hsz : size n 1 = (n + 1) / 2 := rfl
  simp only [Mrk.constraints, Mrk.nodeConst, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (((⟨x, hx, rfl⟩ | h) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, hpn, hH, hn', hA, hB, hs0, hqb1, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, hpn, hH, hn', hA, hB, hs0, hqb1, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, hpn, hH, hn', hA, hB, hs0, hqb1, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · have hc1 := hA Mrk.sg (by decide)
    simp only [eval_mul3, eval_c, hc1]
    simp only [rootCell, Mrk.sg, Mrk.rt, Mrk.gM, Mrk.mj, Mrk.cId, Mrk.cLen, Nat.reduceEqDiff, if_false, ofNat0]
    grind

/-- A padding row (all cells `0`). -/
theorem casePad {q : Nat} (hq0 : q ≠ 0) (hq : q < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK q col = 0)
    (hnx : q + 1 < H → tr.cell T_MRK (q + 1) Mrk.sg = 0 ∧ tr.cell T_MRK (q + 1) Mrk.pr = 0)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK q pub = 0 := by
  have hnx' : q + 1 < H → tr.cell T_MRK ((q + 1) % H) 1 = 0 ∧ tr.cell T_MRK ((q + 1) % H) 2 = 0 := by
    intro hl; rw [Nat.mod_eq_of_lt hl]; exact hnx hl
  simp only [Mrk.constraints, Mrk.nodeConst, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (((⟨x, hx, rfl⟩ | h) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_c, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, hA, Nat.reduceLT]; grind)
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_smul, eval_mid,
      eval_k, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.endE, Mrk.nActE, hH, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg,
      hA, Nat.reduceLT, Nat.reduceAdd, hq0, if_false])
    all_goals first
      | grind
      | (by_cases hl : q + 1 < H
         · obtain ⟨g1, g2⟩ := hnx' hl
           simp only [g1, g2, show ¬ q + 1 = H by omega, if_false]; grind
         · simp only [show q + 1 = H by omega, if_true]; grind)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, hA, Nat.reduceLT]; grind)
  · simp only [eval_mul3, eval_c, eval_not, Mrk.sg, Mrk.wl, hA, Nat.reduceLT]; grind

end cases

end MrkLocal

end ZkFormal.Near.Render
