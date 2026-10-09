import ZkFormal.NearV3.Rcpt.Extract.V.Chars

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Key (v1 `RcptKey`) — `KEYNIB` row facts of `rcptV3`

(Row facts only so far; the per-receipt `KEYNIB` traffic with the access-key walk is open.)

Symbols `0, 0` on the first two `VL` rows (`kz`), the two nibbles of each
receiver character on the `V` rows (slot A: high, slot B: low), `END` on the
first `RID` row: the view's `keySyms`.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem flatMap_pair_get (f g : Nat → Nat) : ∀ (l : List Nat) (k : Nat), k < l.length →
    (l.flatMap fun x => [f x, g x]).getD (2 * k) 0 = f (l.getD k 0) ∧
    (l.flatMap fun x => [f x, g x]).getD (2 * k + 1) 0 = g (l.getD k 0) := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons x l ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      have := ih k (by simpa using hk)
      simp only [List.flatMap_cons, List.getD_cons_succ]
      rw [show 2 * (k + 1) = (2 * k) + 2 by omega, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by omega]
      simpa [List.getD_eq_getElem?_getD] using this

theorem rowT_key (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true =
    gt (C tr tt q gKA) [wE.eval tr tt q pub, C tr tt q tA, C tr tt q symA, C tr tt q lastA] ++
    gt (C tr tt q gKB) [wE.eval tr tt q pub, C tr tt q tB, C tr tt q symB, (0 : Nat)] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem key_row {q : Nat} (hq : q < tr.height tt) :
    tr.cell tt q gKA = tr.cell tt q sV + tr.cell tt q kz + tr.cell tt q sRID * tr.cell tt q fs +
      tr.cell tt q ee * (tr.cell tt q sT0 + tr.cell tt q sSL * tr.cell tt q fs + tr.cell tt q sS +
        tr.cell tt q sKT + tr.cell tt q sPK + tr.cell tt q sGP * tr.cell tt q fs) ∧
    (tr.cell tt q sV = 1 → tr.cell tt q tA = 2 + 2 * tr.cell tt q idx ∧
      tr.cell tt q symA = hiE.eval tr tt q pub ∧ tr.cell tt q lastA = 0) ∧
    (tr.cell tt q kz = 1 → tr.cell tt q tA = tr.cell tt q idx ∧ tr.cell tt q symA = 0 ∧
      tr.cell tt q lastA = 0 ∧ tr.cell tt q sVL = 1) ∧
    (tr.cell tt q sRID = 1 → tr.cell tt q fs = 1 → tr.cell tt q tA = 2 + 2 * tr.cell tt q RcptV3.Lv ∧
      tr.cell tt q symA = (SYM_END : Nat) ∧ tr.cell tt q lastA = 1) ∧
    (tr.cell tt q sVL = 1 → tr.cell tt q fs = 1 → tr.cell tt q kz = 1) := by
  have c1 := con hL hq (e := sub (c gKA) (sum [c sV, c kz, .mul (c sRID) (c fs),
      .mul (c ee) (sum [c sT0, .mul (c sSL) (c fs), c sS, c sKT, c sPK, .mul (c sGP) (c fs)])]))
    (mem_ky (by simp [cKey]))
  have c2 := con hL hq (e := .mul (c sV) (sub (c tA) (.add (k 2) (two (c idx))))) (mem_ky (by simp [cKey]))
  have c3 := con hL hq (e := .mul (c sV) (sub (c symA) hiE)) (mem_ky (by simp [cKey]))
  have c4 := con hL hq (e := .mul (c sV) (c lastA)) (mem_ky (by simp [cKey]))
  have c5 := con hL hq (e := .mul (c kz) (sub (c tA) (c idx))) (mem_ky (by simp [cKey]))
  have c6 := con hL hq (e := .mul (c kz) (c symA)) (mem_ky (by simp [cKey]))
  have c7 := con hL hq (e := .mul (c kz) (c lastA)) (mem_ky (by simp [cKey]))
  have c8 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c tA) (.add (k 2) (two (c RcptV3.Lv)))))
    (mem_ky (by simp [cKey]))
  have c9 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c symA) (k SYM_END))) (mem_ky (by simp [cKey]))
  have c10 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c lastA) (k 1))) (mem_ky (by simp [cKey]))
  have c11 := con hL hq (e := .mul (c kz) (Dsl.not (c sVL))) (mem_ky (by simp [cKey]))
  have c12 := con hL hq (e := mul3 (c sVL) (c fs) (Dsl.not (c kz))) (mem_ky (by simp [cKey]))
  simp only [two, eval_mul, eval_mul3, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_not, eval_sum_cons,
    eval_sum_nil] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  refine ⟨by grind, fun h => ?_, fun h => ?_, fun h h' => ?_, fun h h' => ?_⟩
  · rw [h] at c2 c3 c4; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at c5 c6 c7 c11; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at c8 c9 c10; exact ⟨by grind, by grind, by grind⟩
  · rw [h, h'] at c12; grind

theorem kz_next {q : Nat} (hq : q + 1 < tr.height tt) (h1 : tr.cell tt q sVL = 1)
    (he : tr.cell tt q fe = 0) : tr.cell tt (q + 1) kz = tr.cell tt q fs := by
  have c := con hL (by omega : q < _) (e := mul3 (c sVL) (Dsl.not (c fe)) (sub (n kz) (c fs)))
    (mem_ky (by simp [cKey]))
  simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at c
  rw [h1, he] at c; grind

theorem kz_zero {q : Nat} (hq : q < tr.height tt) (h0 : tr.cell tt q sVL = 0) :
    tr.cell tt q kz = 0 := by
  have c := con hL hq (e := .mul (c kz) (Dsl.not (c sVL))) (mem_ky (by simp [cKey]))
  simp only [eval_mul, eval_c, eval_not] at c
  rw [h0] at c; grind

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem kz_row (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell tt (s + j) kz = if 4 + Lp ≤ j ∧ j < 6 + Lp then 1 else 0 := by
  have hfin := lay.fin
  have hm : (sVL, 4 + Lp, 4) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have F : RFld tr tt s (s + (4 + Lp)) 4 sVL := lay.flds _ hm
  by_cases hin : 4 + Lp ≤ j ∧ j < 8 + Lp
  · obtain ⟨k, rfl⟩ : ∃ k, j = 4 + Lp + k := ⟨j - (4 + Lp), by omega⟩
    have hk : k < 4 := by omega
    rw [show s + (4 + Lp + k) = s + (4 + Lp) + k by omega]
    cases k with
    | zero =>
      rw [if_pos (by omega)]
      exact (key_row hL (by omega)).2.2.2.2 (by simpa using F.fld.st 0 (by omega))
        (by simpa using F.fld.fs 0 (by omega))
    | succ k =>
      rw [show s + (4 + Lp) + (k + 1) = s + (4 + Lp) + k + 1 by omega,
        kz_next hL (by omega) (F.fld.st k (by omega)) (by rw [F.fld.fe k (by omega), if_neg (by omega)]),
        F.fld.fs k (by omega)]
      by_cases hk0 : k = 0
      · subst hk0; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hk0, if_neg (by omega)]
  · rw [if_neg (by omega)]
    exact kz_zero hL (by omega) (st_row hL lay hm j hj (by omega))

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Slot B on a receiver row: the low nibble of the character. -/
theorem keyB_V {q : Nat} (hq : q < tr.height tt) (h1 : tr.cell tt q sV = 1) :
    tr.cell tt q tB = 3 + 2 * tr.cell tt q idx ∧ tr.cell tt q symB = loE.eval tr tt q pub := by
  have c1 := con hL hq (e := .mul (c sV) (sub (c tB) (.add (k 3) (two (c idx))))) (mem_ky (by simp [cKey]))
  have c2 := con hL hq (e := .mul (c sV) (sub (c symB) loE)) (mem_ky (by simp [cKey]))
  simp only [two, eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_k] at c1 c2
  rw [h1] at c1 c2; exact ⟨by grind, by grind⟩

/-- **Access-key walk symbols** (rows of a gas-refund system receipt, `ee = 1`). -/
theorem akey_row {q : Nat} (hq : q < tr.height tt) (he : tr.cell tt q ee = 1) :
    (tr.cell tt q sT0 = 1 → tr.cell tt q tA = 0 ∧ tr.cell tt q symA = 0 ∧ tr.cell tt q lastA = 0 ∧
      tr.cell tt q tB = 1 ∧ tr.cell tt q symB = 2) ∧
    (tr.cell tt q sSL = 1 → tr.cell tt q fs = 1 → tr.cell tt q tA = 2 + 2 * tr.cell tt q RcptV3.Ls ∧
      tr.cell tt q symA = 0 ∧ tr.cell tt q lastA = 0 ∧ tr.cell tt q tB = 3 + 2 * tr.cell tt q RcptV3.Ls ∧
      tr.cell tt q symB = 2) ∧
    (tr.cell tt q sS = 1 → tr.cell tt q tA = 2 + 2 * tr.cell tt q idx ∧ tr.cell tt q symA = hiE.eval tr tt q pub ∧
      tr.cell tt q lastA = 0 ∧ tr.cell tt q tB = 3 + 2 * tr.cell tt q idx ∧ tr.cell tt q symB = loE.eval tr tt q pub) ∧
    (tr.cell tt q sKT = 1 → tr.cell tt q tA = 4 + 2 * tr.cell tt q RcptV3.Ls ∧ tr.cell tt q symA = 0 ∧
      tr.cell tt q lastA = 0 ∧ tr.cell tt q tB = 5 + 2 * tr.cell tt q RcptV3.Ls ∧ tr.cell tt q symB = tr.cell tt q b) ∧
    (tr.cell tt q sPK = 1 → tr.cell tt q tA = 6 + 2 * tr.cell tt q RcptV3.Ls + 2 * tr.cell tt q idx ∧
      tr.cell tt q symA = hiPK.eval tr tt q pub ∧ tr.cell tt q lastA = 0 ∧
      tr.cell tt q tB = 7 + 2 * tr.cell tt q RcptV3.Ls + 2 * tr.cell tt q idx ∧
      tr.cell tt q symB = loPK.eval tr tt q pub ∧
      tr.cell tt q b = 16 * hiPK.eval tr tt q pub + loPK.eval tr tt q pub) ∧
    (tr.cell tt q sGP = 1 → tr.cell tt q fs = 1 →
      tr.cell tt q tA = 70 + 2 * tr.cell tt q RcptV3.Ls + 64 * tr.cell tt q RcptV3.kt ∧
      tr.cell tt q symA = (SYM_END : Nat) ∧ tr.cell tt q lastA = 1) := by
  have m : ∀ e ∈ cKey, e.eval tr tt q pub = 0 := fun e he' => con hL hq (mem_ky he')
  have T1 := m (mul3 (c ee) (c sT0) (c tA)) (by simp [cKey])
  have T2 := m (mul3 (c ee) (c sT0) (c symA)) (by simp [cKey])
  have T3 := m (mul3 (c ee) (c sT0) (c lastA)) (by simp [cKey])
  have T4 := m (mul3 (c ee) (c sT0) (sub (c tB) (k 1))) (by simp [cKey])
  have T5 := m (mul3 (c ee) (c sT0) (sub (c symB) (k 2))) (by simp [cKey])
  have L1 := m (.mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tA) (.add (k 2) (two (c RcptV3.Ls))))) (by simp [cKey])
  have L2 := m (.mul (mul3 (c ee) (c sSL) (c fs)) (c symA)) (by simp [cKey])
  have L3 := m (.mul (mul3 (c ee) (c sSL) (c fs)) (c lastA)) (by simp [cKey])
  have L4 := m (.mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tB) (.add (k 3) (two (c RcptV3.Ls))))) (by simp [cKey])
  have L5 := m (.mul (mul3 (c ee) (c sSL) (c fs)) (sub (c symB) (k 2))) (by simp [cKey])
  have S1 := m (mul3 (c ee) (c sS) (sub (c tA) (.add (k 2) (two (c idx))))) (by simp [cKey])
  have S2 := m (mul3 (c ee) (c sS) (sub (c symA) hiE)) (by simp [cKey])
  have S3 := m (mul3 (c ee) (c sS) (c lastA)) (by simp [cKey])
  have S4 := m (mul3 (c ee) (c sS) (sub (c tB) (.add (k 3) (two (c idx))))) (by simp [cKey])
  have S5 := m (mul3 (c ee) (c sS) (sub (c symB) loE)) (by simp [cKey])
  have K1 := m (mul3 (c ee) (c sKT) (sub (c tA) (.add (k 4) (two (c RcptV3.Ls))))) (by simp [cKey])
  have K2 := m (mul3 (c ee) (c sKT) (c symA)) (by simp [cKey])
  have K3 := m (mul3 (c ee) (c sKT) (c lastA)) (by simp [cKey])
  have K4 := m (mul3 (c ee) (c sKT) (sub (c tB) (.add (k 5) (two (c RcptV3.Ls))))) (by simp [cKey])
  have K5 := m (mul3 (c ee) (c sKT) (sub (c symB) (c b))) (by simp [cKey])
  have P1 := m (mul3 (c ee) (c sPK) (sub (c tA) (sum [k 6, two (c RcptV3.Ls), two (c idx)]))) (by simp [cKey])
  have P2 := m (mul3 (c ee) (c sPK) (sub (c symA) hiPK)) (by simp [cKey])
  have P3 := m (mul3 (c ee) (c sPK) (c lastA)) (by simp [cKey])
  have P4 := m (mul3 (c ee) (c sPK) (sub (c tB) (sum [k 7, two (c RcptV3.Ls), two (c idx)]))) (by simp [cKey])
  have P5 := m (mul3 (c ee) (c sPK) (sub (c symB) loPK)) (by simp [cKey])
  have P6 := m (mul3 (c ee) (c sPK) (sub (c b) (.add (smul 16 hiPK) loPK))) (by simp [cKey])
  have G1 := m (.mul (mul3 (c ee) (c sGP) (c fs)) (sub (c tA) (sum [k 70, two (c RcptV3.Ls), smul 64 (c RcptV3.kt)])))
    (by simp [cKey])
  have G2 := m (.mul (mul3 (c ee) (c sGP) (c fs)) (sub (c symA) (k SYM_END))) (by simp [cKey])
  have G3 := m (.mul (mul3 (c ee) (c sGP) (c fs)) (sub (c lastA) (k 1))) (by simp [cKey])
  simp only [two, eval_mul, eval_mul3, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_sum_cons,
    eval_sum_nil, he] at T1 T2 T3 T4 T5 L1 L2 L3 L4 L5 S1 S2 S3 S4 S5 K1 K2 K3 K4 K5 P1 P2 P3 P4 P5 P6 G1 G2 G3
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · rw [h] at T1 T2 T3 T4 T5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at L1 L2 L3 L4 L5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at S1 S2 S3 S4 S5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at K1 K2 K3 K4 K5; exact ⟨by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at P1 P2 P3 P4 P5 P6; exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at G1 G2 G3; exact ⟨by grind, by grind, by grind⟩

end ZkFormal.NearV3.RcptV3Proof
