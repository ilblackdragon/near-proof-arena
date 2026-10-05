import ZkFormal.Near.Render.Proof.AcctFacts
import ZkFormal.Near.Render.Proof.SortLocal

/-!
# ZkFormal.Near.Render.Proof.AcctLocal — `AcctLocalStmt` (given `TouchedLe`)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace AcctLocal
open SortLocal (ofNat0 ofNat1)

variable {I : Info} (ok : AcctOk I)

theorem kOf_mem {q : Nat} (h : q < 16 * I.touched.length) : AcctGen.kOf I q ∈ I.touched := by
  simp only [AcctGen.kOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q / 16 < I.touched.length by omega),
    Option.getD_some]
  exact List.getElem_mem _

theorem dsum_succ (v : List Nat) (i : Nat) :
    AcctGen.dsumOf v (i + 1) = AcctGen.dsumOf v i + (255 - v.getD (i + 1) 0) := by
  simp [AcctGen.dsumOf, List.range_succ, List.sum_append, Nat.add_assoc]

theorem dsum_zero (v : List Nat) : AcctGen.dsumOf v 0 = 255 - v.getD 0 0 := by
  simp [AcctGen.dsumOf]

theorem dsum_le (v : List Nat) : ∀ i, AcctGen.dsumOf v i ≤ 255 * (i + 1)
  | 0 => by rw [dsum_zero]; omega
  | i + 1 => by rw [dsum_succ]; have := dsum_le v i; omega

theorem dsum_pos (v : List Nat) (hb : ∀ j, j < 16 → v.getD j 0 ≠ 255 → v.getD j 0 < 255) :
    ∀ i j, j ≤ i → j < 16 → v.getD j 0 ≠ 255 → 0 < AcctGen.dsumOf v i
  | 0, j, hj, hj16, hne => by
    rw [dsum_zero]; have := hb j hj16 hne; rw [show j = 0 by omega] at this; omega
  | i + 1, j, hj, hj16, hne => by
    rw [dsum_succ]
    by_cases h : j = i + 1
    · subst h; have := hb _ hj16 hne; omega
    · have := dsum_pos v hb i j (by omega) hj16 hne; omega

section rows
variable {tr : Trace Fp} {pub : List Fp} {H : Nat} (hH : tr.height T_ACCT = H)
  (hHS : 16 * I.touched.length ≤ H)
  (hcell : ∀ q col, q < H → col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col))
include ok hH hHS hcell

theorem bools {q : Nat} (hq : q < H) {x : Nat}
    (hx : x ∈ [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS]) :
    (Dsl.bool (c x)).eval tr T_ACCT q pub = 0 := by
  simp only [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hc : ∀ col, col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col) :=
    fun col h => hcell q col hq h
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_bool, eval_c, hc, Nat.reduceLT, AcctGen.cell, AcctGen.actCell] <;>
  repeat' split
  all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem simple {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ Expr.mul (c Acct.af) (Dsl.not (c Acct.act)), .mul (c Acct.al) (Dsl.not (c Acct.act)),
      .mul .isFirst (Dsl.not (c Acct.af)), .mul .isLast (.mul (c Acct.act) (Dsl.not (c Acct.al))),
      .mul (c Acct.af) (c Acct.i), .mul (c Acct.al) (sub (c Acct.i) (k 15)),
      .mul (c Acct.af) (Dsl.not (c Acct.lo8)), .mul (c Acct.al) (c Acct.lo8),
      .mul (Dsl.not (c Acct.lo8)) (c Acct.st), sub (c Acct.gS) (.mul (c Acct.act) (c Acct.lo8)) ]) :
    e.eval tr T_ACCT q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col) :=
    fun col h => hcell q col hq h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
    Acct.act, Acct.af, Acct.al, Acct.i, Acct.lo8, Acct.st, Acct.gS, hc, Nat.reduceLT, AcctGen.cell,
    AcctGen.actCell, natCast_eq] <;>
  repeat' split
  all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem nextc {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c Acct.act) (Dsl.not (c Acct.al)) (Dsl.not (n Acct.act)),
      mul3 (c Acct.act) (Dsl.not (c Acct.al)) (n Acct.af),
      mul3 (c Acct.act) (Dsl.not (c Acct.al)) (sub (n Acct.kk) (c Acct.kk)),
      mul3 (c Acct.act) (Dsl.not (c Acct.al)) (sub (n Acct.tlast) (c Acct.tlast)),
      mul3 (c Acct.act) (Dsl.not (c Acct.al)) (sub (n Acct.i) (.add (c Acct.i) (k 1))),
      mul3 (c Acct.al) (n Acct.act) (Dsl.not (n Acct.af)),
      mul3 .isTransition (Dsl.not (c Acct.act)) (n Acct.act),
      .mul (mul3 (c Acct.act) (Dsl.not (c Acct.al)) (n Acct.lo8)) (Dsl.not (c Acct.lo8)),
      .mul (mul3 (c Acct.act) (c Acct.lo8) (Dsl.not (n Acct.lo8))) (sub (c Acct.i) (k 7)) ]) :
    e.eval tr T_ACCT q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col) :=
    fun col h => hcell q col hq h
  have hc0 : ∀ col, col < 16 → tr.cell T_ACCT 0 col = Fp.ofNat (AcctGen.cell I 0 col) :=
    fun col h => hcell 0 col (by omega) h
  have hi : q % 16 ≠ 15 → Fp.ofNat ((q + 1) % 16) = Fp.ofNat (q % 16) + 1 := by
    intro h; rw [show (q + 1) % 16 = q % 16 + 1 by omega, ← ofNat_add']; rfl
  have hk : q % 16 ≠ 15 → AcctGen.kOf I (q + 1) = AcctGen.kOf I q := by
    intro h; simp only [AcctGen.kOf]; rw [show (q + 1) / 16 = q / 16 by omega]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases hl : q + 1 < H
  · have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hl
    have hc' : ∀ col, col < 16 → tr.cell T_ACCT (q + 1) col = Fp.ofNat (AcctGen.cell I (q + 1) col) :=
      fun col h => hcell _ col hl h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Acct.act, Acct.af, Acct.al, Acct.i, Acct.kk, Acct.tlast, Acct.lo8,
      hc, hc', Nat.reduceLT, AcctGen.cell, AcctGen.actCell, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])
  · have hn' : (q + 1) % H = 0 := by rw [show q + 1 = H by omega]; exact Nat.mod_self H
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Acct.act, Acct.af, Acct.al, Acct.i, Acct.kk, Acct.tlast, Acct.lo8,
      hc, hc0, Nat.reduceLT, AcctGen.cell, AcctGen.actCell, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem dsum0 {q : Nat} (hq : q < H) :
    (Expr.mul (c Acct.af) (sub (c Acct.dsum) (sub (k 255) (c Acct.amt)))).eval tr T_ACCT q pub = 0 := by
  simp only [eval_mul, eval_c, eval_sub, eval_k, hcell q _ hq (by decide : Acct.af < 16),
    hcell q _ hq (by decide : Acct.dsum < 16), hcell q _ hq (by decide : Acct.amt < 16)]
  simp only [AcctGen.cell, Acct.af, Acct.dsum, Acct.amt, AcctGen.actCell]
  by_cases ha : q < 16 * I.touched.length
  · by_cases h0 : q % 16 = 0
    · simp only [ha, h0, if_true, ofNat1, dsum_zero]
      have hb := (ok.pre _ (kOf_mem ha)).2.1
      have hv : (I.vpre.getD (AcctGen.kOf I q) []).getD 0 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : (I.vpre.getD (AcctGen.kOf I q) [])[0]? with
        | none => simp
        | some x => exact hb x (List.mem_of_getElem? h)
      have hN := congrArg Fp.ofNat (show 255 - (I.vpre.getD (AcctGen.kOf I q) []).getD 0 0 +
        (I.vpre.getD (AcctGen.kOf I q) []).getD 0 0 = 255 by omega)
      rw [← ofNat_add'] at hN
      simp only [natCast_eq]; grind
    · simp only [ha, h0, if_true, if_false, ofNat0]; grind
  · simp only [ha, if_false, ofNat0]; grind

theorem dsumStep {q : Nat} (hq : q < H) :
    (mul3 (c Acct.act) (Dsl.not (c Acct.al)) (sub (n Acct.dsum) (.add (c Acct.dsum) (sub (k 255) (n Acct.amt))))).eval
      tr T_ACCT q pub = 0 := by
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, hH,
    hcell q _ hq (by decide : Acct.act < 16), hcell q _ hq (by decide : Acct.al < 16),
    hcell q _ hq (by decide : Acct.dsum < 16)]
  by_cases ha : q < 16 * I.touched.length
  · by_cases h15 : q % 16 = 15
    · simp only [AcctGen.cell, Acct.act, Acct.al, AcctGen.actCell, ha, h15, if_true, ofNat1]; grind
    · have hl : q + 1 < 16 * I.touched.length := by omega
      rw [Nat.mod_eq_of_lt (show q + 1 < H by omega), hcell _ _ (by omega) (by decide : Acct.dsum < 16),
        hcell _ _ (by omega) (by decide : Acct.amt < 16)]
      simp only [AcctGen.cell, Acct.act, Acct.al, Acct.dsum, Acct.amt, AcctGen.actCell, ha, hl, h15,
        if_true, if_false, ofNat1, ofNat0]
      have hk : AcctGen.kOf I (q + 1) = AcctGen.kOf I q := by
        simp only [AcctGen.kOf]; rw [show (q + 1) / 16 = q / 16 by omega]
      rw [hk, show (q + 1) % 16 = q % 16 + 1 by omega, dsum_succ]
      have hb := (ok.pre _ (kOf_mem ha)).2.1
      have hv : (I.vpre.getD (AcctGen.kOf I q) []).getD (q % 16 + 1) 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : (I.vpre.getD (AcctGen.kOf I q) [])[q % 16 + 1]? with
        | none => simp
        | some x => exact hb x (List.mem_of_getElem? h)
      have hN := congrArg Fp.ofNat (show 255 - (I.vpre.getD (AcctGen.kOf I q) []).getD (q % 16 + 1) 0 +
        (I.vpre.getD (AcctGen.kOf I q) []).getD (q % 16 + 1) 0 = 255 by omega)
      rw [← ofNat_add'] at hN
      rw [← ofNat_add']
      simp only [natCast_eq]; grind
  · simp only [AcctGen.cell, Acct.act, ha, if_false, ofNat0]; grind

theorem dsumInv {q : Nat} (hq : q < H) :
    (Expr.mul (c Acct.al) (sub (.mul (c Acct.dsum) (c Acct.inv)) (k 1))).eval tr T_ACCT q pub = 0 := by
  simp only [eval_mul, eval_c, eval_sub, eval_k, hcell q _ hq (by decide : Acct.al < 16),
    hcell q _ hq (by decide : Acct.dsum < 16), hcell q _ hq (by decide : Acct.inv < 16)]
  simp only [AcctGen.cell, Acct.al, Acct.dsum, Acct.inv, AcctGen.actCell]
  by_cases ha : q < 16 * I.touched.length
  · by_cases h15 : q % 16 = 15
    · simp only [ha, h15, if_true, ofNat1]
      obtain ⟨hlen, hb, j, hj, hne⟩ := ok.pre _ (kOf_mem ha)
      have hbj : ∀ j, j < 16 → (I.vpre.getD (AcctGen.kOf I q) []).getD j 0 ≠ 255 →
          (I.vpre.getD (AcctGen.kOf I q) []).getD j 0 < 255 := by
        intro j _ hne
        rw [List.getD_eq_getElem?_getD] at hne ⊢
        cases h : (I.vpre.getD (AcctGen.kOf I q) [])[j]? with
        | none => simp
        | some x => rw [h] at hne; have := hb x (List.mem_of_getElem? h); simp at hne ⊢; omega
      have hpos := dsum_pos _ hbj 15 j (by omega) hj hne
      have hle := dsum_le (I.vpre.getD (AcctGen.kOf I q) []) 15
      generalize AcctGen.dsumOf (I.vpre.getD (AcctGen.kOf I q) []) 15 = d at hpos hle
      have hne0 : Fp.ofNat d ≠ 0 := by
        intro h0
        have := congrArg Fp.toNat h0
        rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [show ZkFormal.Algebra.P = 2013265921 from rfl]; omega)] at this
        exact absurd this (by rw [Fp.toNat_zero]; omega)
      simp only [invP, Fp.ofNat_toNat, natCast_eq, ofNat1]
      rw [Fp.mul_inv_cancel hne0]; grind
    · simp only [ha, h15, if_true, if_false, ofNat0]; grind
  · simp only [ha, if_false, ofNat0]; grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ Acct.constraints) :
    e.eval tr T_ACCT q pub = 0 := by
  simp only [Acct.constraints] at he
  rcases List.mem_append.1 he with he | he
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact bools ok hH hHS hcell hq hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact dsum0 ok hH hHS hcell hq
    · exact dsumStep ok hH hHS hcell hq
    · exact dsumInv ok hH hHS hcell hq

end rows

end AcctLocal

end ZkFormal.Near.Render

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- `AcctLocalStmt` under the missing `Good` field `TouchedLe` (R-L6e-1). -/
def AcctLocalStmt' : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → TouchedLe e →
    TableLocal Acct.table (render c.1 e) T_ACCT (publicOf c)

open AcctLocal in
theorem acctLocal' : AcctLocalStmt' := by
  intro c e hg htl
  have ok := acctOk hg htl
  have hp : partOf (bundle c.1 e) T_ACCT =
      mkTab (2 ^ logOf (16 * (mkInfo c.1 e).touched.length)) Acct.width (AcctGen.cell (mkInfo c.1 e)) := rfl
  obtain ⟨hlog, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have hcell' : ∀ q col, q < 2 ^ logOf (16 * (mkInfo c.1 e).touched.length) → col < 16 →
      (render c.1 e).cell T_ACCT q col = Fp.ofNat (AcctGen.cell (mkInfo c.1 e) q col) :=
    fun q col hq hc => hcell q col hq hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) (by have := ok.len_le; show _ ≤ 2 ^ 12; omega)
  · intro r hr e he
    rw [hH] at hr
    exact constr ok hH (le_pow_logOf _) hcell' hr he
  · intro r hr i hi b hb
    rw [hH] at hr
    have key : ∀ x ∈ [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS],
        (Dsl.c x).eval (render c.1 e) T_ACCT r (publicOf c) = 0 ∨ (Dsl.c x).eval (render c.1 e) T_ACCT r (publicOf c) = 1 :=
      fun x hx => bool_cases (by
        have := bools ok hH (le_pow_logOf _) hcell' (pub := publicOf c) hr hx
        simpa only [eval_bool] using this)
    simp only [Acct.table, Acct.interactions, Acct.vbytes, send, recv, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    exact key _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

/-- **`AcctLocalStmt`**, given that `Good` bounds the touched nodes (R-L6e-1). -/
theorem acctLocal_of (h : ∀ (c : Claim) (e : Ext), Good c e → TouchedLe e) : AcctLocalStmt :=
  fun c e hg => acctLocal' c e hg (h c.1 e hg)

end ZkFormal.Near.Render
