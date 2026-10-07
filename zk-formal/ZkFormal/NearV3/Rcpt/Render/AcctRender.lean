import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import ZkFormal.Near.Render.Proof.AcctLocal

/-!
# ZkFormal.NearV3.Rcpt.Render.AcctRender — completeness of the `acctV3` table

Honest rows (`acctV3Rows as`): v1's lane layout (`Near/Render/Acct.lean`) for the records `as`
(view values `AcctV`): record `as[s]` on rows `16s … 16s+15`, lane `i`: amount byte `i` pre
and post, locked byte `i`, storage byte `i` (`i < 8`), code-hash bytes `2i, 2i+1`, the running
`Σ (255 − amount_j)` and its inverse on lane 15; zero padding to `2^logOf (16·|as|)` rows.
The constraint proofs are v1's (`Near/Render/Proof/AcctLocal.lean`) with the table index
generalised.  Given `AcctV3Ok as`:
* `acctV3_render_local`: `TableLocal AcctV3.table`;
* `acctV3_render_traffic`: traffic `acctV3Traffic as` (via the extraction's segment traffic).
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- What the honest `acctV3` table needs. -/
structure AcctV3Ok (as : List AcctV) : Prop where
  len_pos : 1 ≤ as.length
  rows : 16 * as.length ≤ 2 ^ AcctV3.maxLog
  pre : ∀ a ∈ as, a.pre.length = 72 ∧ (∀ b ∈ a.pre, b < 256) ∧ ∃ j, j < 16 ∧ a.pre.getD j 0 ≠ 255
  post : ∀ a ∈ as, a.post.length = 16 ∧ ∀ b ∈ a.post, b < ZkFormal.Algebra.P
  canon : ∀ a ∈ as, a.k < ZkFormal.Algebra.P ∧ a.tlast < ZkFormal.Algebra.P

namespace AcctV3Gen

def ent (as : List AcctV) (q : Nat) : AcctV := as.getD (q / 16) default

/-- Active cells (row `q < 16·|as|`), lane `i = q % 16`. -/
def actCell (as : List AcctV) (q : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if q % 16 = 0 then 1 else 0
  | 2 => if q % 16 = 15 then 1 else 0
  | 3 => (ent as q).k
  | 4 => q % 16
  | 5 => (ent as q).tlast
  | 6 => (ent as q).pre.getD (q % 16) 0
  | 7 => (ent as q).post.getD (q % 16) 0
  | 8 => (ent as q).pre.getD (16 + q % 16) 0
  | 9 => if q % 16 < 8 then (ent as q).pre.getD (64 + q % 16) 0 else 0
  | 10 => (ent as q).pre.getD (32 + 2 * (q % 16)) 0
  | 11 => (ent as q).pre.getD (33 + 2 * (q % 16)) 0
  | 12 => if q % 16 < 8 then 1 else 0
  | 13 => AcctGen.dsumOf (ent as q).pre (q % 16)
  | 14 => if q % 16 = 15 then invP (AcctGen.dsumOf (ent as q).pre 15) else 0
  | 15 => if q % 16 < 8 then 1 else 0
  | _ => 0

def cell (as : List AcctV) (q col : Nat) : Nat := if q < 16 * as.length then actCell as q col else 0

end AcctV3Gen

/-- The honest `acctV3` rows. -/
def acctV3Rows (as : List AcctV) : Array Row :=
  mkTab (2 ^ logOf (16 * as.length)) AcctV3.width (AcctV3Gen.cell as)

namespace AcctV3Local
open SortLocal (ofNat0 ofNat1)

variable {as : List AcctV} (ok : AcctV3Ok as)

theorem ent_mem {q : Nat} (h : q < 16 * as.length) : AcctV3Gen.ent as q ∈ as := by
  simp only [AcctV3Gen.ent, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show q / 16 < as.length by omega), Option.getD_some]
  exact List.getElem_mem _

section rows
variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat} (hH : tr.height tt = H)
  (hHS : 16 * as.length ≤ H)
  (hcell : ∀ q col, q < H → col < 16 → tr.cell tt q col = Fp.ofNat (AcctV3Gen.cell as q col))
include ok hH hHS hcell

theorem bools {q : Nat} (hq : q < H) {x : Nat}
    (hx : x ∈ [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS]) :
    (Dsl.bool (c x)).eval tr tt q pub = 0 := by
  simp only [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hc : ∀ col, col < 16 → tr.cell tt q col = Fp.ofNat (AcctV3Gen.cell as q col) :=
    fun col h => hcell q col hq h
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_bool, eval_c, hc, Nat.reduceLT, AcctV3Gen.cell, AcctV3Gen.actCell] <;>
  repeat' split
  all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem simple {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ Expr.mul (c Acct.af) (Dsl.not (c Acct.act)), .mul (c Acct.al) (Dsl.not (c Acct.act)),
      .mul .isFirst (Dsl.not (c Acct.af)), .mul .isLast (.mul (c Acct.act) (Dsl.not (c Acct.al))),
      .mul (c Acct.af) (c Acct.i), .mul (c Acct.al) (sub (c Acct.i) (k 15)),
      .mul (c Acct.af) (Dsl.not (c Acct.lo8)), .mul (c Acct.al) (c Acct.lo8),
      .mul (Dsl.not (c Acct.lo8)) (c Acct.st), sub (c Acct.gS) (.mul (c Acct.act) (c Acct.lo8)) ]) :
    e.eval tr tt q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 16 → tr.cell tt q col = Fp.ofNat (AcctV3Gen.cell as q col) :=
    fun col h => hcell q col hq h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
    Acct.act, Acct.af, Acct.al, Acct.i, Acct.lo8, Acct.st, Acct.gS, hc, Nat.reduceLT, AcctV3Gen.cell,
    AcctV3Gen.actCell, natCast_eq] <;>
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
    e.eval tr tt q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 16 → tr.cell tt q col = Fp.ofNat (AcctV3Gen.cell as q col) :=
    fun col h => hcell q col hq h
  have hc0 : ∀ col, col < 16 → tr.cell tt 0 col = Fp.ofNat (AcctV3Gen.cell as 0 col) :=
    fun col h => hcell 0 col (by omega) h
  have hi : q % 16 ≠ 15 → Fp.ofNat ((q + 1) % 16) = Fp.ofNat (q % 16) + 1 := by
    intro h; rw [show (q + 1) % 16 = q % 16 + 1 by omega, ← ofNat_add']; rfl
  have hk : q % 16 ≠ 15 → AcctV3Gen.ent as (q + 1) = AcctV3Gen.ent as q := by
    intro h; simp only [AcctV3Gen.ent]; rw [show (q + 1) / 16 = q / 16 by omega]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases hl : q + 1 < H
  · have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hl
    have hc' : ∀ col, col < 16 → tr.cell tt (q + 1) col = Fp.ofNat (AcctV3Gen.cell as (q + 1) col) :=
      fun col h => hcell _ col hl h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Acct.act, Acct.af, Acct.al, Acct.i, Acct.kk, Acct.tlast, Acct.lo8,
      hc, hc', Nat.reduceLT, AcctV3Gen.cell, AcctV3Gen.actCell, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])
  · have hn' : (q + 1) % H = 0 := by rw [show q + 1 = H by omega]; exact Nat.mod_self H
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Acct.act, Acct.af, Acct.al, Acct.i, Acct.kk, Acct.tlast, Acct.lo8,
      hc, hc0, Nat.reduceLT, AcctV3Gen.cell, AcctV3Gen.actCell, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem dsum0 {q : Nat} (hq : q < H) :
    (Expr.mul (c Acct.af) (sub (c Acct.dsum) (sub (k 255) (c Acct.amt)))).eval tr tt q pub = 0 := by
  simp only [eval_mul, eval_c, eval_sub, eval_k, hcell q _ hq (by decide : Acct.af < 16),
    hcell q _ hq (by decide : Acct.dsum < 16), hcell q _ hq (by decide : Acct.amt < 16)]
  simp only [AcctV3Gen.cell, Acct.af, Acct.dsum, Acct.amt, AcctV3Gen.actCell]
  by_cases ha : q < 16 * as.length
  · by_cases h0 : q % 16 = 0
    · simp only [ha, h0, if_true, ofNat1, AcctLocal.dsum_zero]
      have hb := (ok.pre _ (ent_mem ha)).2.1
      have hv : ((AcctV3Gen.ent as q).pre).getD 0 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : ((AcctV3Gen.ent as q).pre)[0]? with
        | none => simp
        | some x => exact hb x (List.mem_of_getElem? h)
      have hN := congrArg Fp.ofNat (show 255 - ((AcctV3Gen.ent as q).pre).getD 0 0 +
        ((AcctV3Gen.ent as q).pre).getD 0 0 = 255 by omega)
      rw [← ofNat_add'] at hN
      simp only [natCast_eq]; grind
    · simp only [ha, h0, if_true, if_false, ofNat0]; grind
  · simp only [ha, if_false, ofNat0]; grind

theorem dsumStep {q : Nat} (hq : q < H) :
    (mul3 (c Acct.act) (Dsl.not (c Acct.al)) (sub (n Acct.dsum) (.add (c Acct.dsum) (sub (k 255) (n Acct.amt))))).eval
      tr tt q pub = 0 := by
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, hH,
    hcell q _ hq (by decide : Acct.act < 16), hcell q _ hq (by decide : Acct.al < 16),
    hcell q _ hq (by decide : Acct.dsum < 16)]
  by_cases ha : q < 16 * as.length
  · by_cases h15 : q % 16 = 15
    · simp only [AcctV3Gen.cell, Acct.act, Acct.al, AcctV3Gen.actCell, ha, h15, if_true, ofNat1]; grind
    · have hl : q + 1 < 16 * as.length := by omega
      rw [Nat.mod_eq_of_lt (show q + 1 < H by omega), hcell _ _ (by omega) (by decide : Acct.dsum < 16),
        hcell _ _ (by omega) (by decide : Acct.amt < 16)]
      simp only [AcctV3Gen.cell, Acct.act, Acct.al, Acct.dsum, Acct.amt, AcctV3Gen.actCell, ha, hl, h15,
        if_true, if_false, ofNat1, ofNat0]
      have hk : AcctV3Gen.ent as (q + 1) = AcctV3Gen.ent as q := by
        simp only [AcctV3Gen.ent]; rw [show (q + 1) / 16 = q / 16 by omega]
      rw [hk, show (q + 1) % 16 = q % 16 + 1 by omega, AcctLocal.dsum_succ]
      have hb := (ok.pre _ (ent_mem ha)).2.1
      have hv : ((AcctV3Gen.ent as q).pre).getD (q % 16 + 1) 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : ((AcctV3Gen.ent as q).pre)[q % 16 + 1]? with
        | none => simp
        | some x => exact hb x (List.mem_of_getElem? h)
      have hN := congrArg Fp.ofNat (show 255 - ((AcctV3Gen.ent as q).pre).getD (q % 16 + 1) 0 +
        ((AcctV3Gen.ent as q).pre).getD (q % 16 + 1) 0 = 255 by omega)
      rw [← ofNat_add'] at hN
      rw [← ofNat_add']
      simp only [natCast_eq]; grind
  · simp only [AcctV3Gen.cell, Acct.act, ha, if_false, ofNat0]; grind

theorem dsumInv {q : Nat} (hq : q < H) :
    (Expr.mul (c Acct.al) (sub (.mul (c Acct.dsum) (c Acct.inv)) (k 1))).eval tr tt q pub = 0 := by
  simp only [eval_mul, eval_c, eval_sub, eval_k, hcell q _ hq (by decide : Acct.al < 16),
    hcell q _ hq (by decide : Acct.dsum < 16), hcell q _ hq (by decide : Acct.inv < 16)]
  simp only [AcctV3Gen.cell, Acct.al, Acct.dsum, Acct.inv, AcctV3Gen.actCell]
  by_cases ha : q < 16 * as.length
  · by_cases h15 : q % 16 = 15
    · simp only [ha, h15, if_true, ofNat1]
      obtain ⟨hlen, hb, j, hj, hne⟩ := ok.pre _ (ent_mem ha)
      have hbj : ∀ j, j < 16 → ((AcctV3Gen.ent as q).pre).getD j 0 ≠ 255 →
          ((AcctV3Gen.ent as q).pre).getD j 0 < 255 := by
        intro j _ hne
        rw [List.getD_eq_getElem?_getD] at hne ⊢
        cases h : ((AcctV3Gen.ent as q).pre)[j]? with
        | none => simp
        | some x => rw [h] at hne; have := hb x (List.mem_of_getElem? h); simp at hne ⊢; omega
      have hpos := AcctLocal.dsum_pos _ hbj 15 j (by omega) hj hne
      have hle := AcctLocal.dsum_le ((AcctV3Gen.ent as q).pre) 15
      generalize AcctGen.dsumOf ((AcctV3Gen.ent as q).pre) 15 = d at hpos hle
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
    e.eval tr tt q pub = 0 := by
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
end AcctV3Local

open AcctV3Local in
/-- **The honest `acctV3` table is locally legal.** -/
theorem acctV3_render_local (as : List AcctV) (ok : AcctV3Ok as) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (16 * as.length))
    (hcell : ∀ r x, r < tr.height t → x < AcctV3.width → tr.cell t r x = Fp.ofNat (AcctV3Gen.cell as r x)) :
    TableLocal AcctV3.table tr t pub := by
  have hHS : 16 * as.length ≤ tr.height t := by simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hcell' : ∀ q col, q < tr.height t → col < 16 → tr.cell t q col = Fp.ofNat (AcctV3Gen.cell as q col) :=
    fun q col hq hc => hcell q col hq hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) ok.rows
  · intro r hr e he
    exact constr ok rfl hHS hcell' hr he
  · intro r hr i hi b hb
    have key : ∀ x ∈ [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.gS],
        (Dsl.c x).eval tr t r pub = 0 ∨ (Dsl.c x).eval tr t r pub = 1 :=
      fun x hx => bool_cases (by
        have := bools ok rfl hHS hcell' (pub := pub) hr hx
        simpa only [eval_bool] using this)
    simp only [AcctV3.table, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, send, recv, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    exact key _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

namespace AcctV3TrafficR
open SortLocal (ofNat0 ofNat1)

section
variable {as : List AcctV} (ok : AcctV3Ok as) {tr : Trace Fp} {t : Nat} {pub : List Fp}
  (hHS : 16 * as.length ≤ tr.height t)
  (hcell : ∀ r x, r < tr.height t → x < AcctV3.width → tr.cell t r x = Fp.ofNat (AcctV3Gen.cell as r x))
include ok hHS hcell

theorem cA {q : Nat} (hq : q < 16 * as.length) {x : Nat} (hx : x < 16) :
    tr.cell t q x = Fp.ofNat (AcctV3Gen.actCell as q x) := by
  rw [hcell q x (by omega) hx]; simp [AcctV3Gen.cell, hq]

theorem cP {q : Nat} (hqH : q < tr.height t) (hq : ¬ q < 16 * as.length) {x : Nat} (hx : x < 16) :
    tr.cell t q x = 0 := by
  rw [hcell q x hqH hx]; simp [AcctV3Gen.cell, hq]; rfl

theorem isSeg {s : Nat} (hs : s < as.length) :
    IsSeg (AcctV3Proof.isOne tr t Acct.act) (AcctV3Proof.isOne tr t Acct.af) (AcctV3Proof.isOne tr t Acct.al)
      (16 * s) 16 := by
  have c := fun {q} (hq : q < 16 * as.length) {x} (hx : x < 16) => cA ok hHS hcell hq hx
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [AcctV3Proof.isOne, c (q := 16 * s) (by omega) (x := Acct.af) (by decide)]
    simp [AcctV3Gen.actCell, Acct.af, ofNat1]
  · simp only [AcctV3Proof.isOne, c (q := 16 * s + 16 - 1) (by omega) (x := Acct.al) (by decide)]
    simp [AcctV3Gen.actCell, Acct.al, show (16 * s + 16 - 1) % 16 = 15 by omega, ofNat1]
  · intro r h1 h2
    simp only [AcctV3Proof.isOne, c (q := r) (by omega) (x := Acct.act) (by decide)]
    simp [AcctV3Gen.actCell, Acct.act, ofNat1]
  · intro r h1 h2
    simp only [AcctV3Proof.isOne, c (q := r) (by omega) (x := Acct.af) (by decide)]
    simp [AcctV3Gen.actCell, Acct.af, show ¬ r % 16 = 0 by omega, ofNat0]
  · intro r h1 h2
    simp only [AcctV3Proof.isOne, c (q := r) (by omega) (x := Acct.al) (by decide)]
    simp [AcctV3Gen.actCell, Acct.al, show ¬ r % 16 = 15 by omega, ofNat0]

theorem ofSeg {s : Nat} (hs : s < as.length) :
    AcctV3Proof.acctOfSeg tr t (16 * s) = as.getD s default := by
  have c := fun {q} (hq : q < 16 * as.length) {x} (hx : x < 16) => cA ok hHS hcell hq hx
  have hmem : as.getD s default ∈ as := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some]
    exact List.getElem_mem _
  have he : ∀ j, j < 16 → AcctV3Gen.ent as (16 * s + j) = as.getD s default := fun j hj => by
    simp only [AcctV3Gen.ent]; rw [show (16 * s + j) / 16 = s by omega]
  obtain ⟨hpl, hpb, -⟩ := ok.pre _ hmem
  obtain ⟨hql, hqb⟩ := ok.post _ hmem
  obtain ⟨hk, htl⟩ := ok.canon _ hmem
  have hb : ∀ p, (as.getD s default).pre.getD p 0 < ZkFormal.Algebra.P := fun p => by
    rw [List.getD_eq_getElem?_getD]
    cases h : (as.getD s default).pre[p]? with
    | none => simp; decide
    | some x => have := hpb x (List.mem_of_getElem? h); simp; unfold ZkFormal.Algebra.P; omega
  have hb' : ∀ p, (as.getD s default).post.getD p 0 < ZkFormal.Algebra.P := fun p => by
    rw [List.getD_eq_getElem?_getD]
    cases h : (as.getD s default).post[p]? with
    | none => simp; decide
    | some x => have := hqb x (List.mem_of_getElem? h); simpa using this
  -- the cells of lane j as naturals
  have cN : ∀ j x, j < 16 → x < 16 →
      AcctV3Proof.cN tr t (16 * s + j) x = AcctV3Gen.actCell as (16 * s + j) x % ZkFormal.Algebra.P := by
    intro j x hj hx
    simp only [AcctV3Proof.cN, c (q := 16 * s + j) (by omega) hx, Fp.toNat_ofNat]
  have cN0 : ∀ x, x < 16 → AcctV3Proof.cN tr t (16 * s) x = AcctV3Gen.actCell as (16 * s) x % ZkFormal.Algebra.P :=
    fun x hx => by have := cN 0 x (by decide) hx; simpa using this
  have he0 : AcctV3Gen.ent as (16 * s) = as.getD s default := by have := he 0 (by decide); simpa using this
  generalize ha : as.getD s default = a at he he0 hpl hql hk htl hb hb' hmem
  obtain ⟨ak, atl, apre, apost⟩ := a
  simp only [AcctV3Proof.acctOfSeg, AcctV.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cN0 Acct.kk (by decide)]; simp only [AcctV3Gen.actCell, Acct.kk, he0]; exact Nat.mod_eq_of_lt hk
  · rw [cN0 Acct.tlast (by decide)]; simp only [AcctV3Gen.actCell, Acct.tlast, he0]
    exact Nat.mod_eq_of_lt htl
  · apply List.ext_getElem (by simpa using hpl.symm)
    intro p h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, AcctV3Proof.preAt, AcctV3Proof.valAt]
    have gp : apre[p] = apre.getD p 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [gp]
    by_cases p1 : p < 16
    · rw [if_pos p1, cN p _ p1 (by decide)]
      simp only [AcctV3Gen.actCell, Acct.amt, he p p1, show (16 * s + p) % 16 = p by omega]
      exact Nat.mod_eq_of_lt (hb p)
    · rw [if_neg p1]
      by_cases p2 : p < 32
      · rw [if_pos p2, cN (p - 16) _ (by omega) (by decide)]
        simp only [AcctV3Gen.actCell, Acct.lk, he (p - 16) (by omega),
          show (16 * s + (p - 16)) % 16 = p - 16 by omega, show 16 + (p - 16) = p by omega]
        exact Nat.mod_eq_of_lt (hb p)
      · rw [if_neg p2]
        by_cases p3 : p < 64
        · rw [if_pos p3]
          by_cases p4 : (p - 32) % 2 = 0
          · rw [if_pos p4, cN ((p - 32) / 2) _ (by omega) (by decide)]
            simp only [AcctV3Gen.actCell, Acct.ch0, he ((p - 32) / 2) (by omega),
              show (16 * s + (p - 32) / 2) % 16 = (p - 32) / 2 by omega, show 32 + 2 * ((p - 32) / 2) = p by omega]
            exact Nat.mod_eq_of_lt (hb p)
          · rw [if_neg p4, cN ((p - 32) / 2) _ (by omega) (by decide)]
            simp only [AcctV3Gen.actCell, Acct.ch1, he ((p - 32) / 2) (by omega),
              show (16 * s + (p - 32) / 2) % 16 = (p - 32) / 2 by omega, show 33 + 2 * ((p - 32) / 2) = p by omega]
            exact Nat.mod_eq_of_lt (hb p)
        · rw [if_neg p3, cN (p - 64) _ (by omega) (by decide)]
          simp only [AcctV3Gen.actCell, Acct.st, he (p - 64) (by omega),
            show (16 * s + (p - 64)) % 16 = p - 64 by omega, if_pos (show p - 64 < 8 by omega),
            show 64 + (p - 64) = p by omega]
          exact Nat.mod_eq_of_lt (hb p)
  · apply List.ext_getElem (by simpa using hql.symm)
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [cN j _ h1 (by decide)]
    have gp : apost[j] = apost.getD j 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [gp]
    simp only [AcctV3Gen.actCell, Acct.post, he j h1, show (16 * s + j) % 16 = j by omega]
    exact Nat.mod_eq_of_lt (hb' j)

end
end AcctV3TrafficR

open AcctV3TrafficR in
/-- **The honest `acctV3` table has the traffic of `as`.** -/
theorem acctV3_render_traffic (as : List AcctV) (ok : AcctV3Ok as) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (16 * as.length))
    (hcell : ∀ r x, r < tr.height t → x < AcctV3.width → tr.cell t r x = Fp.ofNat (AcctV3Gen.cell as r x)) :
    TableTraffic AcctV3.interactions tr t pub (acctV3Traffic as) := by
  have hHS : 16 * as.length ≤ tr.height t := by simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hL := acctV3_render_local as ok tr t pub hlog hcell
  have hpad : ∀ b sd q, q < tr.height t → ¬ q < 16 * as.length →
      rowTraffic AcctV3.interactions tr t q pub b sd = [] := by
    intro b sd q hq hn
    have ha := cP ok hHS hcell hq hn (x := Acct.act) (by decide)
    have hf := cP ok hHS hcell hq hn (x := Acct.af) (by decide)
    have hg := cP ok hHS hcell hq hn (x := Acct.gS) (by decide)
    simp only [rowTraffic, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, AcctV3Proof.multNat1, eval_c, ha, hf, hg]
    simp
  have hall : ∀ sd b, ((List.range (tr.height t)).flatMap fun r => rowTraffic AcctV3.interactions tr t r pub b sd).Perm
      ((if sd then acctV3Sends as b else acctRecvs as b).map Msg.toFp) := by
    intro sd b
    rw [range_split hHS, List.flatMap_append,
      Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq'', rfl⟩ := List.mem_map.1 hq
        exact hpad b sd _ (by have := List.mem_range.1 hq''; omega) (by omega)),
      List.append_nil, range_flatMap_chunks]
    have hseg : ∀ s ∈ List.range as.length,
        ((List.range 16).flatMap fun i => rowTraffic AcctV3.interactions tr t (16 * s + i) pub b sd).Perm
          ((if sd then acctV3Sends [as.getD s default] b else acctRecvs [as.getD s default] b).map Msg.toFp) := by
      intro s hs
      have hs' := List.mem_range.1 hs
      have := AcctV3Proof.segTraffic hL (isSeg ok hHS hcell hs') (by omega) b sd
      rw [List.range'_eq_map_range, List.flatMap_map, ofSeg ok hHS hcell hs'] at this
      exact this
    refine (perm_flatMap_congr hseg).trans (List.Perm.of_eq ?_)
    rw [← List.map_flatMap]
    congr 1
    cases sd
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← flatMap_getD default as (fun a => acctRecvs [a] b), ← AcctV3Proof.acctRecvs_flat]
    · simp only [↓reduceIte]
      rw [← flatMap_getD default as (fun a => acctV3Sends [a] b), ← AcctV3Proof.acctV3Sends_flat]
  exact traffic_of (fun b => hall true b) (fun b => hall false b)

end ZkFormal.NearV3.Render
