import ZkFormal.NearV3.Candidates.MerkleRender.Local

/-!
# Generalized honest Merkle cases (n < BabyBear modulus)

Port of the original case proofs, widening only the inverse bound.

## MrkLocal2 — node ends (`caseSame`, `caseNext`, `caseTop`)
-/

namespace ZkFormal.NearV3.Candidates.MerkleRender

open ZkFormal.Near.Render
open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkLocal
open SortLocal (ofNat0 ofNat1)
open MrkGen

section cases
variable {tr : Trace Fp} {pub : List Fp} {H q : Nat} {n : Nat} {lv : List (List MNode)}
  (hH : tr.height T_MRK = H)
include hH

set_option maxHeartbeats 4000000 in
/-- The end of a node followed by the next node of its level. -/
theorem caseSame {j i p : Nat} {h : Bool} (hok : RecOk n (j, i, h, p)) (hpe : h = true → p = 63)
    (hs : i + 1 < size n j) (hq0 : q ≠ 0) (hql : q + 1 < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK q col = Fp.ofNat (nodeCell n lv (j, i, h, p) col))
    (hB : ∀ col, col < 58 → tr.cell T_MRK (q + 1) col =
      Fp.ofNat (nodeCell n lv (j, i + 1, decide (2 * (i + 1) + 1 < size n (j - 1)), 0) col))
    (hn1 : 1 ≤ n) (hnP : n < ZkFormal.Algebra.P)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK q pub = 0 := by
  have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hql
  have hql' : ¬ q + 1 = H := by omega
  obtain ⟨hj1, hjn, hi, hh, hp64, hp0⟩ := hok
  simp only at hj1 hjn hi hh hp64 hp0
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
    simp only [eval_mul3, eval_c, eval_not, hc1, hc2]
    simp only [nodeCell, Mrk.sg, Mrk.wl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv,
      Mrk.mj, Mrk.pw, Mrk.pr, Mrk.wn, Mrk.wf, Mrk.sf, Mrk.sl, Mrk.cId, Mrk.cLen, Mrk.mi, Mrk.gM, Mrk.gO,
      Mrk.oId, Mrk.oLen, Mrk.reg, Mrk.rt, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false,
      true_and, false_and, if_false, if_true]
    cases h with
    | true => simp only [hpe rfl, if_true, ofNat1]; grind
    | false => simp only [Bool.false_eq_true, if_false, ofNat0]; grind

set_option maxHeartbeats 4000000 in
/-- The end of the last node of a level followed by the first node of the next level. -/
theorem caseNext {j i p : Nat} {h : Bool} (hok : RecOk n (j, i, h, p)) (hpe : h = true → p = 63)
    (hs : i + 1 = size n j) (hs1 : size n j ≠ 1) (hq0 : q ≠ 0) (hql : q + 1 < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK q col = Fp.ofNat (nodeCell n lv (j, i, h, p) col))
    (hB : ∀ col, col < 58 → tr.cell T_MRK (q + 1) col =
      Fp.ofNat (nodeCell n lv (j + 1, 0, decide (1 < size n j), 0) col))
    (hn1 : 1 ≤ n) (hnP : n < ZkFormal.Algebra.P)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK q pub = 0 := by
  have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hql
  have hql' : ¬ q + 1 = H := by omega
  obtain ⟨hj1, hjn, hi, hh, hp64, hp0⟩ := hok
  simp only at hj1 hjn hi hh hp64 hp0
  have hsz : size n j = (size n (j - 1) + 1) / 2 := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; rfl
  have hinv : size n j ≠ 1 → (Fp.ofNat (size n j) - 1) * Fp.ofNat (invP (size n j - 1)) = 1 := fun h =>
    inv_fact (by have := size_pos n hn1 j; omega) (by have := size_le n j; omega)
  have hqb : qBase n (j + 1) = qBase n j + size n (j - 1) / 2 := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; rfl
  have hsz' : size n (j + 1) = (size n j + 1) / 2 := rfl
  have hinv' : size n (j + 1) ≠ 1 → (Fp.ofNat (size n (j + 1)) - 1) * Fp.ofNat (invP (size n (j + 1) - 1)) = 1 :=
    fun h => inv_fact (by have := size_pos n hn1 (j + 1); omega) (by have := size_le n (j + 1); omega)
  simp only [Mrk.constraints, Mrk.nodeConst, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (((⟨x, hx, rfl⟩ | h) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Nat.add_sub_cancel, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Nat.add_sub_cancel, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [eval_bool, eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_smul, eval_mid, eval_pub, eval_isFirst, eval_isLast, eval_isTransition, Mrk.actE, Mrk.nActE,
      Mrk.endE, Mrk.nPubE, hH, hn', hA, hB, hq0, hql', Nat.add_sub_cancel, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      natCast_eq, nodeCell, rootCell, msgId, Nat.reduceEqDiff, if_true, if_false, and_true, true_and, and_false,
      false_and, and_self, ofNat_add', ofNat_mul']; (repeat' split); all_goals (first | omega |
      ((try simp only [ofNat0, ofNat1]); grind [ofNat0, ofNat1])))
  · have hc1 := hA Mrk.sg (by decide)
    have hc2 := hA Mrk.wl (by decide)
    simp only [eval_mul3, eval_c, eval_not, hc1, hc2]
    simp only [nodeCell, Mrk.sg, Mrk.wl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv,
      Mrk.mj, Mrk.pw, Mrk.pr, Mrk.wn, Mrk.wf, Mrk.sf, Mrk.sl, Mrk.cId, Mrk.cLen, Mrk.mi, Mrk.gM, Mrk.gO,
      Mrk.oId, Mrk.oLen, Mrk.reg, Mrk.rt, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false,
      true_and, false_and, if_false, if_true]
    cases h with
    | true => simp only [hpe rfl, if_true, ofNat1]; grind
    | false => simp only [Bool.false_eq_true, if_false, ofNat0]; grind

set_option maxHeartbeats 4000000 in
/-- The last row of the top node, followed by padding. -/
theorem caseTop {j i p : Nat} {h : Bool} (hok : RecOk n (j, i, h, p)) (hpe : h = true → p = 63)
    (hs : i + 1 = size n j) (hs1 : size n j = 1) (hq0 : q ≠ 0) (hql : q + 1 < H)
    (hA : ∀ col, col < 58 → tr.cell T_MRK q col = Fp.ofNat (nodeCell n lv (j, i, h, p) col))
    (hB : ∀ col, col < 58 → tr.cell T_MRK (q + 1) col = Fp.ofNat 0)
    (hn1 : 1 ≤ n) (hnP : n < ZkFormal.Algebra.P)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK q pub = 0 := by
  have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hql
  have hql' : ¬ q + 1 = H := by omega
  obtain ⟨hj1, hjn, hi, hh, hp64, hp0⟩ := hok
  simp only at hj1 hjn hi hh hp64 hp0
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
    simp only [eval_mul3, eval_c, eval_not, hc1, hc2]
    simp only [nodeCell, Mrk.sg, Mrk.wl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv,
      Mrk.mj, Mrk.pw, Mrk.pr, Mrk.wn, Mrk.wf, Mrk.sf, Mrk.sl, Mrk.cId, Mrk.cLen, Mrk.mi, Mrk.gM, Mrk.gO,
      Mrk.oId, Mrk.oLen, Mrk.reg, Mrk.rt, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false,
      true_and, false_and, if_false, if_true]
    cases h with
    | true => simp only [hpe rfl, if_true, ofNat1]; grind
    | false => simp only [Bool.false_eq_true, if_false, ofNat0]; grind

end cases

end MrkLocal

end ZkFormal.NearV3.Candidates.MerkleRender
