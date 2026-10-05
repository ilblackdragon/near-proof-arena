import ZkFormal.Near.Extract.RcptKey

/-!
# ZkFormal.Near.Extract.RcptDig — `DIGEST` receives of a receipt

The refund-id window (first `XRI` row), the `H(PEO)` window (first `XLH` row),
and, on the receipt's last row when it ends the batch (`lastR`), the `RC` and
`RF` commitments.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem rowT_dig (q : Nat) : rowTraffic Rcpt.interactions tr T_RCPT q pub B_DIGEST false =
    gt (C tr q gDg) ([C tr q dI, C tr q dL] ++ regsAt tr q) ++
    gt (C tr q lastR) ([(K_RC : Fp), C tr q oEnd] ++ pubsAt pub PV_RC 32) ++
    gt (C tr q lastR) ([(K_RF : Fp), C tr q o2End] ++ pubsAt pub PV_RFC 32) := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS]

/-- A single non-empty row. -/
theorem flatMap_point {α : Type} (f : Nat → List α) (s T a : Nat) (ha : a < T) :
    (List.range' s T).flatMap (fun q => if q = s + a then f q else []) = f (s + a) := by
  rw [flatMap_window _ s T a 1 (by omega) (fun j hj hout => by rw [if_neg (by omega)])]
  simp

theorem peo_len (x : RcptV) : x.peo.length = 37 + 32 * hN x.hr + x.v.length + x.burnt.length - 16 +
    (if x.hr then x.rfid.length else 0) - 32 * hN x.hr := by
  cases hh : x.hr <;> simp [RcptV.peo, RcptV.borshN, G_LEn, u32r, hh, hN] <;> omega

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem dig_row {q : Nat} (hq : q < tr.height T_RCPT) :
    tr.cell T_RCPT q gDg = tr.cell T_RCPT q fs * (tr.cell T_RCPT q sXRI + tr.cell T_RCPT q sXLH) ∧
    (tr.cell T_RCPT q fs = 1 → tr.cell T_RCPT q sXRI = 1 →
      tr.cell T_RCPT q dI = (K_RID : Nat) + (16 : Nat) * tr.cell T_RCPT q Rcpt.r ∧ tr.cell T_RCPT q dL = (48 : Nat)) ∧
    (tr.cell T_RCPT q fs = 1 → tr.cell T_RCPT q sXLH = 1 →
      tr.cell T_RCPT q dI = (K_PEO : Nat) + (16 : Nat) * tr.cell T_RCPT q Rcpt.r ∧
      tr.cell T_RCPT q dL = (37 : Nat) + ((32 : Nat) * tr.cell T_RCPT q Rcpt.hr + tr.cell T_RCPT q Rcpt.Lv)) := by
  have c1 := con hL hq (e := sub (c gDg) (.mul (c fs) (.add (c sXRI) (c sXLH)))) (mem_en (by simp [cEnd]))
  have c2 := con hL hq (e := mul3 (c fs) (c sXRI) (sub (c dI) (mid K_RID (c Rcpt.r)))) (mem_en (by simp [cEnd]))
  have c3 := con hL hq (e := mul3 (c fs) (c sXRI) (sub (c dL) (k 48))) (mem_en (by simp [cEnd]))
  have c4 := con hL hq (e := mul3 (c fs) (c sXLH) (sub (c dI) (mid K_PEO (c Rcpt.r)))) (mem_en (by simp [cEnd]))
  have c5 := con hL hq (e := mul3 (c fs) (c sXLH) (sub (c dL) (sum [k 37, smul 32 (c Rcpt.hr), c Rcpt.Lv])))
    (mem_en (by simp [cEnd]))
  simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_k, eval_mid, eval_smul, eval_sum_cons,
    eval_sum_nil] at c1 c2 c3 c4 c5
  refine ⟨by grind, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [h1, h2] at c2 c3; exact ⟨by grind, by grind⟩
  · rw [h1, h2] at c4 c5; exact ⟨by grind, by grind⟩

/-- A state absent from the receipt's plan is off on its rows. -/
theorem st_absent {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) {X : Nat}
    (hX : X ∈ states) (habs : X ∉ (plan h Lp Lv Ls kt).map (·.1)) (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell T_RCPT (s + j) X = 0 := by
  have hfin := lay.fin
  obtain ⟨f, hf, h1, h2⟩ := plan_cover h Lp Lv Ls kt j hj
  have hst := (lay.flds f hf).fld.st (j - f.2.1) (by omega)
  rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at hst
  exact (oneHot hL (by omega) (plan_states h Lp Lv Ls kt f hf).1 hst).2 X hX
    (fun e => habs (e ▸ List.mem_map_of_mem hf))

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- The register window of a 32-row register field is its bytes. -/
theorem regs_window {s r0 X : Nat} (hH : r0 + 32 ≤ tr.height T_RCPT) (F : RFld tr s r0 32 X)
    (hX : X ∈ regStates) (hne : X ≠ sCL) : regsAt tr r0 = (colAt tr r0 32 b).map Fp.ofNat := by
  apply List.ext_getElem (by simp [regsAt, colAt])
  intro k h1 h2
  simp only [regsAt, colAt, List.getElem_map, List.getElem_range, cv, fpN]
  rw [fld_bytes hL hH F.fld hX hne (by omega) k (by simpa [regsAt] using h1)]

omit hL in
theorem peo_length (tr : Trace Fp) (y : RS) :
    (rcptOf tr y).peo.length = 37 + 32 * hN y.h + y.Lv := by
  cases hh : y.h <;> simp [RcptV.peo, RcptV.borshN, G_LEn, u32r, hh, hN, rcptOf, colAt_len] <;> omega

/-- **The `DIGEST` receives of a receipt.** -/
theorem rcpt_dig {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) {rN : Nat}
    (hrN : tr.cell T_RCPT s Rcpt.r = (rN : Fp)) :
    ((List.range' s (total h Lp Lv Ls kt)).flatMap fun q =>
      rowTraffic Rcpt.interactions tr T_RCPT q pub B_DIGEST false).Perm
      (((if h then [digMsg (msgId K_RID rN) 48 (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).rfid] else []) ++
        [digMsg (msgId K_PEO rN) (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peo.length
          (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peoh]).map Msg.toFp ++
       (if tr.cell T_RCPT (s + total h Lp Lv Ls kt) act = 1 then [] else
         [[(K_RC : Fp), tr.cell T_RCPT s oEnd] ++ pubsAt pub PV_RC 32,
          [(K_RF : Fp), tr.cell T_RCPT s o2End] ++ pubsAt pub PV_RFC 32])) := by
  have hfin := lay.fin
  have hT := total_pos h Lp Lv Ls kt
  have mP : (sXLH, 144 + 32 * hN h + Vt Lp Lv Ls kt, 32) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hleP := plan_le h Lp Lv Ls kt _ mP
  simp only at hleP
  have FP : RFld tr s (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) 32 sXLH := lay.flds _ mP
  -- the gated register window
  have gP : ∀ j, j < total h Lp Lv Ls kt → gt (C tr (s + j) gDg) ([C tr (s + j) dI, C tr (s + j) dL] ++ regsAt tr (s + j)) =
      (if h = true ∧ j = 127 + Vt Lp Lv Ls kt then
        [Msg.toFp (digMsg (msgId K_RID rN) 48 (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).rfid)] else []) ++
      (if j = 144 + 32 * hN h + Vt Lp Lv Ls kt then
        [Msg.toFp (digMsg (msgId K_PEO rN) (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peo.length
          (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peoh)] else []) := by
    intro j hj
    have D := dig_row hL (q := s + j) (by omega)
    -- the states XRI, XLH on row j
    have hXLH : tr.cell T_RCPT (s + j) sXLH =
        if 144 + 32 * hN h + Vt Lp Lv Ls kt ≤ j ∧ j < 144 + 32 * hN h + Vt Lp Lv Ls kt + 32 then 1 else 0 :=
      cell_state hL lay mP j hj
    have hXRI : tr.cell T_RCPT (s + j) sXRI =
        if h = true ∧ 127 + Vt Lp Lv Ls kt ≤ j ∧ j < 127 + Vt Lp Lv Ls kt + 32 then 1 else 0 := by
      cases h
      · rw [st_absent hL lay (X := sXRI) (by simp [states]) (by simp [plan]; decide) j hj]; simp
      · rw [cell_state hL lay (X := sXRI) (off := 127 + Vt Lp Lv Ls kt) (L := 32) (by simp [plan]) j hj]; simp
    by_cases jP : j = 144 + 32 * hN h + Vt Lp Lv Ls kt
    · subst jP
      have hfs : tr.cell T_RCPT (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) fs = 1 := by
        simpa using FP.fld.fs 0 (by omega)
      have h1 : tr.cell T_RCPT (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) sXLH = 1 := by
        rw [hXLH, if_pos (by omega)]
      have h0 : tr.cell T_RCPT (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) sXRI = 0 := by
        rw [hXRI, if_neg (by cases h <;> simp [hN] <;> omega)]
      have hg : tr.cell T_RCPT (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) gDg = 1 := by rw [D.1, hfs, h1, h0]; grind
      obtain ⟨d1, d2⟩ := D.2.2 hfs h1
      have hr0 := FP.consts 0 (by omega) _ rC
      have hh0 := FP.consts 0 (by omega) _ hrC
      have hv0 := FP.consts 0 (by omega) _ LvC
      simp only [Nat.add_zero] at hr0 hh0 hv0
      simp only [C]
      rw [gt_one hg, if_neg (by cases h <;> simp [hN] <;> omega), if_pos trivial, List.nil_append,
        regs_window hL (by omega) FP (by decide) (by decide), d1, d2, hr0, hh0, hv0, hrN, lay.hr, lay.cLv,
        peo_length]
      simp only [digMsg, Msg.toFp, List.map_append, List.map_cons, List.map_nil, rcptOf, List.cons_append,
        List.nil_append, List.cons.injEq, List.singleton_append, and_true]
      refine ⟨by rw [← natCast_eq, msgId]; grind, ?_⟩
      rw [← natCast_eq, ← hN_cast]; grind
    · by_cases jR : h = true ∧ j = 127 + Vt Lp Lv Ls kt
      · obtain ⟨hh, rfl⟩ := jR
        subst hh
        have mR : (sXRI, 127 + Vt Lp Lv Ls kt, 32) ∈ plan true Lp Lv Ls kt := by simp [plan]
        have FR : RFld tr s (s + (127 + Vt Lp Lv Ls kt)) 32 sXRI := lay.flds _ mR
        have hfs : tr.cell T_RCPT (s + (127 + Vt Lp Lv Ls kt)) fs = 1 := by simpa using FR.fld.fs 0 (by omega)
        have h1 : tr.cell T_RCPT (s + (127 + Vt Lp Lv Ls kt)) sXRI = 1 := by rw [hXRI, if_pos ⟨rfl, by omega, by omega⟩]
        have h0 : tr.cell T_RCPT (s + (127 + Vt Lp Lv Ls kt)) sXLH = 0 := by rw [hXLH, if_neg (by simp [hN] <;> omega)]
        have hg : tr.cell T_RCPT (s + (127 + Vt Lp Lv Ls kt)) gDg = 1 := by rw [D.1, hfs, h1, h0]; grind
        obtain ⟨d1, d2⟩ := D.2.1 hfs h1
        have hr0 := FR.consts 0 (by omega) _ rC
        simp only [Nat.add_zero] at hr0
        simp only [C]
        rw [gt_one hg, regs_window hL (by omega) FR (by decide) (by decide), d1, d2, hr0, hrN]
        simp only [jP, true_and, ↓reduceIte, List.append_nil]
        simp only [digMsg, Msg.toFp, List.map_append, List.map_cons, List.map_nil, rcptOf, ↓reduceIte,
          List.cons_append, List.nil_append, List.cons.injEq, and_true]
        exact ⟨by rw [← natCast_eq, msgId]; grind, rfl⟩
      · have hg : tr.cell T_RCPT (s + j) gDg = 0 := by
          rw [D.1, hXRI, hXLH]
          by_cases inP : 144 + 32 * hN h + Vt Lp Lv Ls kt ≤ j ∧ j < 144 + 32 * hN h + Vt Lp Lv Ls kt + 32
          · have := FP.fld.fs (j - (144 + 32 * hN h + Vt Lp Lv Ls kt)) (by omega)
            rw [show s + (144 + 32 * hN h + Vt Lp Lv Ls kt) + (j - (144 + 32 * hN h + Vt Lp Lv Ls kt)) = s + j by
              omega, if_neg (by omega)] at this
            rw [this]; grind
          · rw [if_neg inP]
            by_cases inR : h = true ∧ 127 + Vt Lp Lv Ls kt ≤ j ∧ j < 127 + Vt Lp Lv Ls kt + 32
            · obtain ⟨hh, i1, i2⟩ := inR
              subst hh
              have jne : j ≠ 127 + Vt Lp Lv Ls kt := fun e => jR ⟨rfl, e⟩
              have FR : RFld tr s (s + (127 + Vt Lp Lv Ls kt)) 32 sXRI := lay.flds (sXRI, 127 + Vt Lp Lv Ls kt, 32) (by simp [plan])
              have := FR.fld.fs (j - (127 + Vt Lp Lv Ls kt)) (by omega)
              rw [show s + (127 + Vt Lp Lv Ls kt) + (j - (127 + Vt Lp Lv Ls kt)) = s + j by omega,
                if_neg (by omega)] at this
              rw [this]; grind
            · rw [if_neg inR]; grind
        simp only [C]
        rw [gt_zero hg, if_neg jR, if_neg jP]; rfl
  -- the gated commitments on the last row
  have gC : ∀ j, j < total h Lp Lv Ls kt →
      gt (C tr (s + j) lastR) ([(K_RC : Fp), C tr (s + j) oEnd] ++ pubsAt pub PV_RC 32) ++
      gt (C tr (s + j) lastR) ([(K_RF : Fp), C tr (s + j) o2End] ++ pubsAt pub PV_RFC 32) =
      if j = total h Lp Lv Ls kt - 1 then
        (if tr.cell T_RCPT (s + total h Lp Lv Ls kt) act = 1 then [] else
         [[(K_RC : Fp), tr.cell T_RCPT s oEnd] ++ pubsAt pub PV_RC 32,
          [(K_RF : Fp), tr.cell T_RCPT s o2End] ++ pubsAt pub PV_RFC 32]) else [] := by
    intro j hj
    have hl := lastR_eq hL (r := s + j) (by omega)
    rw [rl_row hL lay j hj] at hl
    simp only [C]
    by_cases e : j = total h Lp Lv Ls kt - 1
    · rw [if_pos e]
      rw [if_pos (by omega)] at hl
      rw [show s + j + 1 = s + total h Lp Lv Ls kt by omega] at hl
      obtain ⟨f, hf, h1, h2⟩ := plan_cover h Lp Lv Ls kt j hj
      have K := (lay.flds f hf).consts (j - f.2.1) (by omega)
      rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at K
      rw [K oEnd oEndC, K o2End o2EndC]
      rcases isBool hL (r := s + total h Lp Lv Ls kt) (by omega) (x := act) (by simp [boolCols]) with ha | ha
      · rw [ha] at hl
        rw [if_neg (by rw [ha]; exact fp_zero_ne_one), gt_one (by rw [hl]; grind), gt_one (by rw [hl]; grind)]; rfl
      · rw [ha] at hl
        rw [if_pos ha, gt_zero (by rw [hl]; grind), gt_zero (by rw [hl]; grind)]; rfl
    · rw [if_neg e]
      rw [if_neg (by omega)] at hl
      rw [gt_zero (by rw [hl]; grind), gt_zero (by rw [hl]; grind)]; rfl
  -- assemble
  rw [flatMap_congr' (G := fun q =>
      ((if h = true ∧ q = s + (127 + Vt Lp Lv Ls kt) then
        [Msg.toFp (digMsg (msgId K_RID rN) 48 (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).rfid)] else []) ++
      (if q = s + (144 + 32 * hN h + Vt Lp Lv Ls kt) then
        [Msg.toFp (digMsg (msgId K_PEO rN) (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peo.length
          (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).peoh)] else [])) ++
      (if q = s + (total h Lp Lv Ls kt - 1) then
        (if tr.cell T_RCPT (s + total h Lp Lv Ls kt) act = 1 then [] else
         [[(K_RC : Fp), tr.cell T_RCPT s oEnd] ++ pubsAt pub PV_RC 32,
          [(K_RF : Fp), tr.cell T_RCPT s o2End] ++ pubsAt pub PV_RFC 32]) else []))
    (fun q hq => by
      obtain ⟨j, rfl, hj⟩ : ∃ j, q = s + j ∧ j < total h Lp Lv Ls kt := by
        simp [List.mem_range'] at hq; exact ⟨q - s, by omega, by omega⟩
      rw [rowT_dig, List.append_assoc, gP j hj, gC j hj]
      congr 1
      · congr 1
        · by_cases hh : h = true
          · simp [hh]
          · simp [hh]
        · simp
      · simp)]
  refine (flatMap_append_perm _ _ _).trans ?_
  rw [flatMap_point _ s _ (total h Lp Lv Ls kt - 1) (by omega)]
  refine List.Perm.append_right _ ?_
  refine (flatMap_append_perm _ _ _).trans (List.Perm.of_eq ?_)
  rw [flatMap_point _ s _ (144 + 32 * hN h + Vt Lp Lv Ls kt) (by omega)]
  simp only [List.map_append, List.map_cons, List.map_nil]
  congr 1
  cases h
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte, flatMap_nil_fun, List.map_nil]
  · simp only [true_and, ↓reduceIte, List.map_cons, List.map_nil]
    exact flatMap_point _ s _ (127 + Vt Lp Lv Ls kt) (by simp [total, Vt] at hT ⊢ <;> omega)

end ZkFormal.Near.RcptProof
