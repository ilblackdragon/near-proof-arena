import ZkFormal.Near.Extract.RcptChars

/-!
# ZkFormal.Near.Extract.RcptKey — `KEYNIB` messages of a receipt

Symbols `0, 0` on the first two `VL` rows (`kz`), the two nibbles of each
receiver character on the `V` rows (slot A: high, slot B: low), `END` on the
first `RID` row: the view's `keySyms`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

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

theorem rowT_key (q : Nat) : rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true =
    gt (C tr q gKA) [C tr q Rcpt.r, C tr q tA, C tr q symA, C tr q lastA] ++
    gt (C tr q sV) [C tr q Rcpt.r, (3 : Nat) + (2 : Nat) * C tr q idx, loE.eval tr T_RCPT q pub, (0 : Nat)] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS]

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem key_row {q : Nat} (hq : q < tr.height T_RCPT) :
    tr.cell T_RCPT q gKA = tr.cell T_RCPT q sV + tr.cell T_RCPT q kz + tr.cell T_RCPT q sRID * tr.cell T_RCPT q fs ∧
    (tr.cell T_RCPT q sV = 1 → tr.cell T_RCPT q tA = 2 + 2 * tr.cell T_RCPT q idx ∧
      tr.cell T_RCPT q symA = hiE.eval tr T_RCPT q pub ∧ tr.cell T_RCPT q lastA = 0) ∧
    (tr.cell T_RCPT q kz = 1 → tr.cell T_RCPT q tA = tr.cell T_RCPT q idx ∧ tr.cell T_RCPT q symA = 0 ∧
      tr.cell T_RCPT q lastA = 0 ∧ tr.cell T_RCPT q sVL = 1) ∧
    (tr.cell T_RCPT q sRID = 1 → tr.cell T_RCPT q fs = 1 → tr.cell T_RCPT q tA = 2 + 2 * tr.cell T_RCPT q Rcpt.Lv ∧
      tr.cell T_RCPT q symA = (SYM_END : Nat) ∧ tr.cell T_RCPT q lastA = 1) ∧
    (tr.cell T_RCPT q sVL = 1 → tr.cell T_RCPT q fs = 1 → tr.cell T_RCPT q kz = 1) := by
  have c1 := con hL hq (e := sub (c gKA) (sum [c sV, c kz, .mul (c sRID) (c fs)])) (mem_ky (by simp [cKey]))
  have c2 := con hL hq (e := .mul (c sV) (sub (c tA) (.add (k 2) (smul 2 (c idx))))) (mem_ky (by simp [cKey]))
  have c3 := con hL hq (e := .mul (c sV) (sub (c symA) hiE)) (mem_ky (by simp [cKey]))
  have c4 := con hL hq (e := .mul (c sV) (c lastA)) (mem_ky (by simp [cKey]))
  have c5 := con hL hq (e := .mul (c kz) (sub (c tA) (c idx))) (mem_ky (by simp [cKey]))
  have c6 := con hL hq (e := .mul (c kz) (c symA)) (mem_ky (by simp [cKey]))
  have c7 := con hL hq (e := .mul (c kz) (c lastA)) (mem_ky (by simp [cKey]))
  have c8 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c tA) (.add (k 2) (smul 2 (c Rcpt.Lv)))))
    (mem_ky (by simp [cKey]))
  have c9 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c symA) (k SYM_END))) (mem_ky (by simp [cKey]))
  have c10 := con hL hq (e := mul3 (c sRID) (c fs) (sub (c lastA) (k 1))) (mem_ky (by simp [cKey]))
  have c11 := con hL hq (e := .mul (c kz) (Dsl.not (c sVL))) (mem_ky (by simp [cKey]))
  have c12 := con hL hq (e := mul3 (c sVL) (c fs) (Dsl.not (c kz))) (mem_ky (by simp [cKey]))
  simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_not, eval_sum_cons,
    eval_sum_nil] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  refine ⟨by grind, fun h => ?_, fun h => ?_, fun h h' => ?_, fun h h' => ?_⟩
  · rw [h] at c2 c3 c4; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at c5 c6 c7 c11; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h, h'] at c8 c9 c10; exact ⟨by grind, by grind, by grind⟩
  · rw [h, h'] at c12; grind

theorem kz_next {q : Nat} (hq : q + 1 < tr.height T_RCPT) (h1 : tr.cell T_RCPT q sVL = 1)
    (he : tr.cell T_RCPT q fe = 0) : tr.cell T_RCPT (q + 1) kz = tr.cell T_RCPT q fs := by
  have c := con hL (by omega : q < _) (e := mul3 (c sVL) (Dsl.not (c fe)) (sub (n kz) (c fs)))
    (mem_ky (by simp [cKey]))
  simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at c
  rw [h1, he] at c; grind

theorem kz_zero {q : Nat} (hq : q < tr.height T_RCPT) (h0 : tr.cell T_RCPT q sVL = 0) :
    tr.cell T_RCPT q kz = 0 := by
  have c := con hL hq (e := .mul (c kz) (Dsl.not (c sVL))) (mem_ky (by simp [cKey]))
  simp only [eval_mul, eval_c, eval_not] at c
  rw [h0] at c; grind

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
include lay

theorem kz_row (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell T_RCPT (s + j) kz = if 4 + Lp ≤ j ∧ j < 6 + Lp then 1 else 0 := by
  have hfin := lay.fin
  have hm : (sVL, 4 + Lp, 4) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have F : RFld tr s (s + (4 + Lp)) 4 sVL := lay.flds _ hm
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

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem fm_len (l : List Nat) : (l.flatMap fun ch => [ch / 16, ch % 16]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih]; simp only [List.length_cons, List.length_nil]; omega

theorem keySyms_eq (x : RcptV) :
    x.keySyms = 0 :: 0 :: ((x.v.flatMap fun ch => [ch / 16, ch % 16]) ++ [SYM_END]) := by
  simp [RcptV.keySyms]

theorem keySyms_len (x : RcptV) : x.keySyms.length = 2 * x.v.length + 3 := by
  rw [keySyms_eq]; simp only [List.length_cons, List.length_append, fm_len, List.length_nil]; try omega

theorem getD_append_left' (l l' : List Nat) (n : Nat) (hn : n < l.length) : (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

theorem keySyms_get (x : RcptV) :
    x.keySyms.getD 0 0 = 0 ∧ x.keySyms.getD 1 0 = 0 ∧
    (∀ k, k < x.v.length → x.keySyms.getD (2 + 2 * k) 0 = x.v.getD k 0 / 16 ∧
      x.keySyms.getD (2 + 2 * k + 1) 0 = x.v.getD k 0 % 16) ∧
    x.keySyms.getD (2 * x.v.length + 2) 0 = SYM_END := by
  have hl := fm_len x.v
  rw [keySyms_eq]
  refine ⟨rfl, rfl, fun k hk => ?_, ?_⟩
  · have := flatMap_pair_get (· / 16) (· % 16) x.v k hk
    rw [show 2 + 2 * k = 2 * k + 1 + 1 by omega, show 2 * k + 1 + 1 + 1 = (2 * k + 1) + 1 + 1 by omega,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
      getD_append_left' _ _ _ (by omega), getD_append_left' _ _ _ (by omega)]
    exact this
  · rw [show 2 * x.v.length + 2 = 2 * x.v.length + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq hl), hl]

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
include lay

/-- **The `KEYNIB` messages of a receipt.** -/
theorem rcpt_key {rN : Nat} (hrN : tr.cell T_RCPT s Rcpt.r = (rN : Fp)) :
    (List.range' s (total h Lp Lv Ls kt)).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true) =
      ((List.range (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).keySyms.length).map fun t =>
        ([rN, t, (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).keySyms.getD t 0,
          if t + 1 = (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).keySyms.length then 1 else 0] : Msg)).map Msg.toFp := by
  have hfin := lay.fin
  have hT := total_pos h Lp Lv Ls kt
  have mV : (sV, 8 + Lp, Lv) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mR : (sRID, 8 + Lp + Lv, 32) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mVL : (sVL, 4 + Lp, 4) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have FV : RFld tr s (s + (8 + Lp)) Lv sV := lay.flds _ mV
  have FR : RFld tr s (s + (8 + Lp + Lv)) 32 sRID := lay.flds _ mR
  have FVL : RFld tr s (s + (4 + Lp)) 4 sVL := lay.flds _ mVL
  have hle := plan_le h Lp Lv Ls kt _ mR
  simp only at hle
  have hvl : (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).v.length = Lv := by simp [rcptOf, colAt_len]
  -- outside the window nothing is sent
  rw [flatMap_window _ s _ (4 + Lp) (5 + Lv) (by omega) (fun j hj hout => by
    have hsv := st_row hL lay mV j hj (by omega)
    have hkz : tr.cell T_RCPT (s + j) kz = 0 := by rw [kz_row hL lay j hj, if_neg (by omega)]
    have hrf : tr.cell T_RCPT (s + j) sRID * tr.cell T_RCPT (s + j) fs = 0 := by
      by_cases hin : 8 + Lp + Lv ≤ j ∧ j < 40 + Lp + Lv
      · have := FR.fld.fs (j - (8 + Lp + Lv)) (by omega)
        rw [show s + (8 + Lp + Lv) + (j - (8 + Lp + Lv)) = s + j by omega, if_neg (by omega)] at this
        rw [this]; grind
      · rw [st_row hL lay mR j hj (by omega)]; grind
    have hg : tr.cell T_RCPT (s + j) gKA = 0 := by
      rw [(key_row hL (q := s + j) (by omega)).1, hsv, hkz, hrf]; grind
    rw [rowT_key]; simp only [C]; rw [gt_zero hg, gt_zero hsv]; rfl)]
  -- the window: VL rows 0..3, V rows, RID row 0
  have e : List.range' (s + (4 + Lp)) (5 + Lv) = List.range' (s + (4 + Lp)) 2 ++
      (List.range' (s + (4 + Lp) + 2) 2 ++ (List.range' (s + (8 + Lp)) Lv ++ [s + (8 + Lp + Lv)])) := by
    rw [show s + (8 + Lp) = s + (4 + Lp) + 2 + 2 by omega,
      show [s + (8 + Lp + Lv)] = List.range' (s + (4 + Lp) + 2 + 2 + Lv) 1 by simp; omega,
      List.range'_append_1, List.range'_append_1, List.range'_append_1]
    congr 1; omega
  rw [e, List.flatMap_append, List.flatMap_append, List.flatMap_append]
  have hst := fun (X off L : Nat) (hm : (X, off, L) ∈ plan h Lp Lv Ls kt) (j : Nat) (hj : j < total h Lp Lv Ls kt) =>
    cell_state hL lay hm j hj
  -- VL rows 0, 1
  have eA : (List.range' (s + (4 + Lp)) 2).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true) =
      [Msg.toFp [rN, 0, 0, 0], Msg.toFp [rN, 1, 0, 0]] := by
    rw [flatMap_range'_single _ (fun k => Msg.toFp [rN, k, 0, 0]) _ 2 (fun k hk => ?_)]
    · rfl
    · have hz : tr.cell T_RCPT (s + (4 + Lp) + k) kz = 1 := by
        rw [show s + (4 + Lp) + k = s + (4 + Lp + k) by omega, kz_row hL lay _ (by omega), if_pos (by omega)]
      have hsv : tr.cell T_RCPT (s + (4 + Lp) + k) sV = 0 := by
        rw [show s + (4 + Lp) + k = s + (4 + Lp + k) by omega]; exact st_row hL lay mV _ (by omega) (by omega)
      have hsr : tr.cell T_RCPT (s + (4 + Lp) + k) sRID = 0 := by
        rw [show s + (4 + Lp) + k = s + (4 + Lp + k) by omega]; exact st_row hL lay mR _ (by omega) (by omega)
      have K := key_row hL (q := s + (4 + Lp) + k) (by omega)
      obtain ⟨t1, t2, t3, -⟩ := K.2.2.1 hz
      have hg : tr.cell T_RCPT (s + (4 + Lp) + k) gKA = 1 := by rw [K.1, hsv, hz, hsr]; grind
      rw [rowT_key]; simp only [C]; rw [gt_one hg, gt_zero hsv, t1, t2, t3, FVL.fld.idx k (by omega),
        FVL.consts k (by omega) _ rC, hrN]
      simp only [Msg.toFp, List.map_cons, List.map_nil, List.append_nil, List.cons.injEq, and_true]
      exact ⟨rfl, rfl, rfl, rfl⟩
  -- VL rows 2, 3
  have eB : (List.range' (s + (4 + Lp) + 2) 2).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true) = [] := by
    apply flatMap_range'_nil; intro k hk
    have q1 : s + (4 + Lp) + 2 + k = s + (6 + Lp + k) := by omega
    have hz : tr.cell T_RCPT (s + (4 + Lp) + 2 + k) kz = 0 := by rw [q1, kz_row hL lay _ (by omega), if_neg (by omega)]
    have hsv : tr.cell T_RCPT (s + (4 + Lp) + 2 + k) sV = 0 := by rw [q1]; exact st_row hL lay mV _ (by omega) (by omega)
    have hsr : tr.cell T_RCPT (s + (4 + Lp) + 2 + k) sRID = 0 := by rw [q1]; exact st_row hL lay mR _ (by omega) (by omega)
    have hg : tr.cell T_RCPT (s + (4 + Lp) + 2 + k) gKA = 0 := by
      rw [(key_row hL (q := s + (4 + Lp) + 2 + k) (by omega)).1, hsv, hz, hsr]; grind
    rw [rowT_key]; simp only [C]; rw [gt_zero hg, gt_zero hsv]; rfl
  -- V rows
  have eC : (List.range' (s + (8 + Lp)) Lv).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true) =
      (List.range Lv).flatMap (fun k => [Msg.toFp [rN, 2 + 2 * k, (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).v.getD k 0 / 16, 0],
        Msg.toFp [rN, 2 + 2 * k + 1, (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).v.getD k 0 % 16, 0]]) := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr'; intro k hk; rw [List.mem_range] at hk
    have q1 : s + (8 + Lp) + k = s + (8 + Lp + k) := by omega
    have h1 : tr.cell T_RCPT (s + (8 + Lp) + k) sV = 1 := FV.fld.st k hk
    have hz : tr.cell T_RCPT (s + (8 + Lp) + k) kz = 0 := by rw [q1, kz_row hL lay _ (by omega), if_neg (by omega)]
    have hsr : tr.cell T_RCPT (s + (8 + Lp) + k) sRID = 0 := by rw [q1]; exact st_row hL lay mR _ (by omega) (by omega)
    have K := key_row hL (q := s + (8 + Lp) + k) (by omega)
    obtain ⟨t1, t2, t3⟩ := K.2.1 h1
    have hg : tr.cell T_RCPT (s + (8 + Lp) + k) gKA = 1 := by rw [K.1, h1, hz, hsr]; grind
    obtain ⟨cv1, clo, -, chi, clo'⟩ := char_val hL (q := s + (8 + Lp) + k) (by omega) (X := sV) (by simp) h1
    have hvk : (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).v.getD k 0 = 16 * hiV tr (s + (8 + Lp) + k) + loV tr (s + (8 + Lp) + k) := by
      simp only [rcptOf]; rw [colAt_get _ _ _ _ _ hk, cv1]
    rw [rowT_key]; simp only [C]
    rw [gt_one hg, gt_one h1, t1, t2, t3, chi, clo', FV.fld.idx k hk, FV.consts k hk _ rC, hrN, hvk,
      show (16 * hiV tr (s + (8 + Lp) + k) + loV tr (s + (8 + Lp) + k)) / 16 = hiV tr (s + (8 + Lp) + k) by omega,
      show (16 * hiV tr (s + (8 + Lp) + k) + loV tr (s + (8 + Lp) + k)) % 16 = loV tr (s + (8 + Lp) + k) by omega]
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq,
      and_true]
    refine ⟨⟨rfl, ?_, rfl, rfl⟩, ⟨rfl, ?_, rfl, rfl⟩⟩
    · rw [← natCast_eq, natCast_add, natCast_mul]; rfl
    · rw [← natCast_eq, natCast_add, natCast_add, natCast_mul]; grind
  -- RID row 0
  have eD : ([s + (8 + Lp + Lv)] : List Nat).flatMap (fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_KEYNIB true) =
      [Msg.toFp [rN, 2 * Lv + 2, SYM_END, 1]] := by
    have h1 : tr.cell T_RCPT (s + (8 + Lp + Lv)) sRID = 1 := by simpa using FR.fld.st 0 (by omega)
    have hfs : tr.cell T_RCPT (s + (8 + Lp + Lv)) fs = 1 := by simpa using FR.fld.fs 0 (by omega)
    have hz : tr.cell T_RCPT (s + (8 + Lp + Lv)) kz = 0 := by rw [kz_row hL lay _ (by omega), if_neg (by omega)]
    have hsv : tr.cell T_RCPT (s + (8 + Lp + Lv)) sV = 0 := st_row hL lay mV _ (by omega) (by omega)
    have K := key_row hL (q := s + (8 + Lp + Lv)) (by omega)
    obtain ⟨t1, t2, t3⟩ := K.2.2.2.1 h1 hfs
    have hg : tr.cell T_RCPT (s + (8 + Lp + Lv)) gKA = 1 := by rw [K.1, hsv, hz, h1, hfs]; grind
    have hLv := FR.consts 0 (by omega) _ LvC
    have hr0 := FR.consts 0 (by omega) _ rC
    simp only [Nat.add_zero] at hLv hr0
    rw [List.flatMap_singleton, rowT_key]; simp only [C]
    rw [gt_one hg, gt_zero hsv, t1, t2, t3, hLv, lay.cLv, hr0, hrN]
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.append_nil, List.cons.injEq, and_true]
    refine ⟨rfl, ?_, rfl, rfl⟩
    rw [← natCast_eq, natCast_add, natCast_mul]; grind
  rw [eA, eB, eC, eD]
  -- the view side
  have hlen := keySyms_len (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩)
  obtain ⟨g0, g1, gk, gend⟩ := keySyms_get (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩)
  rw [hvl] at hlen gk gend
  rw [hlen]
  have rr : List.range (2 * Lv + 3) = [0, 1] ++ (List.range' 2 (2 * Lv) ++ [2 * Lv + 2]) := by
    rw [List.range_eq_range', show [0, 1] = List.range' 0 2 from rfl,
      show [2 * Lv + 2] = List.range' (2 + 2 * Lv) 1 by simp; omega, List.range'_append_1, List.range'_append_1]
    congr 1; omega
  rw [rr, range'_flatMap_pairs]
  simp only [List.map_append, List.map_flatMap, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_nil, List.flatMap_cons, List.flatMap_nil]
  rw [g0, g1, gend]
  have e0 : ¬ (0 + 1 = 2 * Lv + 3) := by omega
  have e1 : ¬ (1 + 1 = 2 * Lv + 3) := by omega
  have e2 : 2 * Lv + 2 + 1 = 2 * Lv + 3 := by omega
  simp only [e0, e1, e2, ↓reduceIte]
  congr 3
  apply flatMap_congr'; intro k hk; rw [List.mem_range] at hk
  rw [(gk k hk).1, (gk k hk).2, if_neg (by omega), if_neg (by omega)]
