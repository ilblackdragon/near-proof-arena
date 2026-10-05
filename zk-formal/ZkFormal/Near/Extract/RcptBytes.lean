import ZkFormal.Near.Extract.RcptFB2

/-!
# ZkFormal.Near.Extract.RcptBytes — the `BYTES` messages of one receipt

The view's encodings split into the chunks the fields emit (`rc_split`,
`rf_split`, `peo_split`, `leaf_split`, `rid_split`), and the receipt's rows
emit exactly these chunks (`rcpt_bytes`, up to permutation).
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- The `BYTES` messages of receipt `r` in the view (without the claim header). -/
def rcptBytesV (pub : List Fp) (x : RcptV) (oN o2N r : Nat) : List Msg :=
  emitAt K_RC oN x.enc ++ (if x.hr then emitAt K_RF o2N x.encRefund else []) ++
    emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
    (if x.hr then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0) else [])

section split
variable (tr : Trace Fp) (y : RS)

theorem rc_split (oN : Nat) :
    emitAt K_RC oN (rcptOf tr y).enc =
      emitAt K_RC oN (u32r y.Lp) ++ emitAt K_RC (oN + 4) (colAt tr (y.s + 4) y.Lp b) ++
      emitAt K_RC (oN + (4 + y.Lp)) (u32r y.Lv) ++
      emitAt K_RC (oN + (8 + y.Lp)) (colAt tr (y.s + (8 + y.Lp)) y.Lv b) ++
      emitAt K_RC (oN + (8 + y.Lp + y.Lv)) (colAt tr (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt K_RC (oN + (40 + y.Lp + y.Lv)) [0] ++ emitAt K_RC (oN + (41 + y.Lp + y.Lv)) (u32r y.Ls) ++
      emitAt K_RC (oN + (45 + y.Lp + y.Lv)) (colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt K_RC (oN + (45 + y.Lp + y.Lv + y.Ls)) [y.kt] ++
      emitAt K_RC (oN + (46 + y.Lp + y.Lv + y.Ls)) (colAt tr (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b) ++
      emitAt K_RC (oN + (78 + Vt y.Lp y.Lv y.Ls y.kt)) (colAt tr (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b) ++
      emitAt K_RC (oN + (94 + Vt y.Lp y.Lv y.Ls y.kt)) tailN ++
      emitAt K_RC (oN + (107 + Vt y.Lp y.Lv y.Ls y.kt)) (colAt tr (y.s + (107 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b) := by
  have hc := emitAt_chunks K_RC
    [(oN, u32r y.Lp), (oN + 4, colAt tr (y.s + 4) y.Lp b), (oN + (4 + y.Lp), u32r y.Lv),
     (oN + (8 + y.Lp), colAt tr (y.s + (8 + y.Lp)) y.Lv b),
     (oN + (8 + y.Lp + y.Lv), colAt tr (y.s + (8 + y.Lp + y.Lv)) 32 b), (oN + (40 + y.Lp + y.Lv), [0]),
     (oN + (41 + y.Lp + y.Lv), u32r y.Ls), (oN + (45 + y.Lp + y.Lv), colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (oN + (45 + y.Lp + y.Lv + y.Ls), [y.kt]),
     (oN + (46 + y.Lp + y.Lv + y.Ls), colAt tr (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b),
     (oN + (78 + Vt y.Lp y.Lv y.Ls y.kt), colAt tr (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b),
     (oN + (94 + Vt y.Lp y.Lv y.Ls y.kt), tailN),
     (oN + (107 + Vt y.Lp y.Lv y.Ls y.kt), colAt tr (y.s + (107 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b)] oN
    (by simp [Consec2, colAt_len, u32r, tailN, Vt]; omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1
  simp [RcptV.enc, rcptOf, RcptV.borshN, colAt_len, List.append_assoc]

theorem leaf_split (r : Nat) :
    emitAt (msgId K_LEAF r) 0 (rcptOf tr y).leaf =
      emitAt (msgId K_LEAF r) 0 [2, 0, 0, 0] ++ emitAt (msgId K_LEAF r) 4 (colAt tr (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt (msgId K_LEAF r) 36 (colAt tr (y.s + (144 + 32 * hN y.h + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) := by
  have hc := emitAt_chunks (msgId K_LEAF r)
    [(0, [2, 0, 0, 0]), (4, colAt tr (y.s + (8 + y.Lp + y.Lv)) 32 b),
     (36, colAt tr (y.s + (144 + 32 * hN y.h + Vt y.Lp y.Lv y.Ls y.kt)) 32 b)] 0
    (by simp [Consec2, colAt_len])
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1 <;> simp [RcptV.leaf, rcptOf, List.append_assoc]

theorem peo_split (r : Nat) :
    emitAt (msgId K_PEO r) 0 (rcptOf tr y).peo =
      emitAt (msgId K_PEO r) 0 (u32r (hN y.h)) ++
      (if y.h then emitAt (msgId K_PEO r) 4 (colAt tr (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) else []) ++
      emitAt (msgId K_PEO r) (4 + 32 * hN y.h) G_LEn ++
      emitAt (msgId K_PEO r) (12 + 32 * hN y.h) (colAt tr (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 burnt) ++
      emitAt (msgId K_PEO r) (28 + 32 * hN y.h) (u32r y.Lv) ++
      emitAt (msgId K_PEO r) (32 + 32 * hN y.h) (colAt tr (y.s + (8 + y.Lp)) y.Lv b) ++
      emitAt (msgId K_PEO r) (32 + 32 * hN y.h + y.Lv) [2, 0, 0, 0, 0] := by
  obtain ⟨s, h, Lp, Lv, Ls, kt⟩ := y
  cases h
  · have hc := emitAt_chunks (msgId K_PEO r)
      [(0, u32r (hN false)), (4 + 32 * hN false, G_LEn),
       (12 + 32 * hN false, colAt tr (s + (78 + Vt Lp Lv Ls kt)) 16 burnt), (28 + 32 * hN false, u32r Lv),
       (32 + 32 * hN false, colAt tr (s + (8 + Lp)) Lv b), (32 + 32 * hN false + Lv, [2, 0, 0, 0, 0])] 0
      (by simp [Consec2, colAt_len, u32r, G_LEn, hN])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    simp only [List.append_assoc]
    rw [← hc]
    congr 1
    simp [RcptV.peo, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hN]
  · have hc := emitAt_chunks (msgId K_PEO r)
      [(0, u32r (hN true)), (4, colAt tr (s + (127 + Vt Lp Lv Ls kt)) 32 b), (4 + 32 * hN true, G_LEn),
       (12 + 32 * hN true, colAt tr (s + (78 + Vt Lp Lv Ls kt)) 16 burnt), (28 + 32 * hN true, u32r Lv),
       (32 + 32 * hN true, colAt tr (s + (8 + Lp)) Lv b), (32 + 32 * hN true + Lv, [2, 0, 0, 0, 0])] 0
      (by simp [Consec2, colAt_len, u32r, G_LEn, hN])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    simp only [↓reduceIte]
    simp only [List.append_assoc]
    rw [← hc]
    congr 1
    simp [RcptV.peo, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hN]

theorem rf_split (o2N : Nat) (hh : y.h = true) :
    emitAt K_RF o2N (rcptOf tr y).encRefund =
      emitAt K_RF o2N ([6, 0, 0, 0] ++ systemN) ++ emitAt K_RF (o2N + 10) (u32r y.Ls) ++
      emitAt K_RF (o2N + 14) (colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt K_RF (o2N + (14 + y.Ls)) (colAt tr (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) ++
      emitAt K_RF (o2N + (46 + y.Ls)) [0] ++ emitAt K_RF (o2N + (47 + y.Ls)) (u32r y.Ls) ++
      emitAt K_RF (o2N + (51 + y.Ls)) (colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt K_RF (o2N + (51 + 2 * y.Ls)) [y.kt] ++
      emitAt K_RF (o2N + (52 + 2 * y.Ls)) (colAt tr (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b) ++
      emitAt K_RF (o2N + (84 + 2 * y.Ls + 32 * y.kt)) (List.replicate 16 0) ++
      emitAt K_RF (o2N + (100 + 2 * y.Ls + 32 * y.kt)) tailN ++
      emitAt K_RF (o2N + (113 + 2 * y.Ls + 32 * y.kt)) (colAt tr (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 ramt) := by
  have hc := emitAt_chunks K_RF
    [(o2N, [6, 0, 0, 0] ++ systemN), (o2N + 10, u32r y.Ls), (o2N + 14, colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (o2N + (14 + y.Ls), colAt tr (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b), (o2N + (46 + y.Ls), [0]),
     (o2N + (47 + y.Ls), u32r y.Ls), (o2N + (51 + y.Ls), colAt tr (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (o2N + (51 + 2 * y.Ls), [y.kt]),
     (o2N + (52 + 2 * y.Ls), colAt tr (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b),
     (o2N + (84 + 2 * y.Ls + 32 * y.kt), List.replicate 16 0), (o2N + (100 + 2 * y.Ls + 32 * y.kt), tailN),
     (o2N + (113 + 2 * y.Ls + 32 * y.kt), colAt tr (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 ramt)] o2N
    (by simp [Consec2, colAt_len, u32r, tailN, systemN]; omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1
  simp [RcptV.encRefund, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hh]

theorem rid_split (r : Nat) (hh : y.h = true) :
    emitAt (msgId K_RID r) 0 ((rcptOf tr y).rid ++ pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0) =
      emitAt (msgId K_RID r) 0 (colAt tr (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt (msgId K_RID r) 32 (pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0) := by
  rw [List.append_assoc, emitAt_append]
  simp [rcptOf, colAt_len]

end split

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem rowT_bytes (q : Nat) :
    rowTraffic Rcpt.interactions tr T_RCPT q pub B_BYTES true = (List.range 3).flatMap (slotT tr q) := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS]

/-- Row segments of the fields of a receipt. -/
def planSegs (s : Nat) (h : Bool) (Lp Lv Ls kt : Nat) : List (Nat × Nat) :=
  (plan h Lp Lv Ls kt).map fun f => (s + f.2.1, f.2.2)

theorem plan_consec (s : Nat) (h : Bool) (Lp Lv Ls kt : Nat) :
    Consec s (planSegs s h Lp Lv Ls kt) ∧ segEnd s (planSegs s h Lp Lv Ls kt) = s + total h Lp Lv Ls kt := by
  cases h <;> simp [planSegs, plan, Consec, segEnd, total, Vt, hN] <;> omega

theorem range'_plan (s : Nat) (h : Bool) (Lp Lv Ls kt : Nat) :
    List.range' s (total h Lp Lv Ls kt) = (planSegs s h Lp Lv Ls kt).flatMap fun p => List.range' p.1 p.2 := by
  obtain ⟨hc, he⟩ := plan_consec s h Lp Lv Ls kt
  have := range'_segs _ s hc
  rw [he, Nat.add_sub_cancel_left] at this
  exact this

theorem rcptOf_hr (y : RS) : (rcptOf tr y).hr = y.h := rfl

/-- **The `BYTES` messages of a receipt.** -/
theorem rcpt_bytes (hL : TableLocal Rcpt.table tr T_RCPT pub) {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat}
    (lay : Layout tr s h Lp Lv Ls kt) {oN o2N rN : Nat}
    (ho : tr.cell T_RCPT s o = (oN : Fp)) (ho2 : tr.cell T_RCPT s o2 = (o2N : Fp))
    (hrN : tr.cell T_RCPT s Rcpt.r = (rN : Fp)) :
    ((List.range' s (total h Lp Lv Ls kt)).flatMap fun q =>
      rowTraffic Rcpt.interactions tr T_RCPT q pub B_BYTES true).Perm
      ((rcptBytesV pub (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩) oN o2N rN).map Msg.toFp) := by
  rw [flatMap_congr' (G := fun q => (List.range 3).flatMap (slotT tr q)) (fun q _ => rowT_bytes q),
    range'_plan, List.flatMap_assoc]
  rw [show ((planSegs s h Lp Lv Ls kt).flatMap fun p =>
      (List.range' p.1 p.2).flatMap fun q => (List.range 3).flatMap (slotT tr q)) =
      (planSegs s h Lp Lv Ls kt).flatMap (fun p => fieldRows tr p.1 p.2) from rfl]
  rw [List.perm_iff_count]; intro m
  unfold rcptBytesV
  rw [rcptOf_hr]
  cases h
  · simp only [planSegs, plan, List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.count_append,
      List.nil_append]
    rw [(fb_PL hL lay ho ho2 hrN).count_eq, (fb_P hL lay ho ho2 hrN).count_eq, (fb_VL hL lay ho ho2 hrN).count_eq,
      (fb_V hL lay ho ho2 hrN).count_eq, (fb_RID hL lay ho ho2 hrN).count_eq, (fb_T0 hL lay ho ho2 hrN).count_eq,
      (fb_SL hL lay ho ho2 hrN).count_eq, (fb_S hL lay ho ho2 hrN).count_eq, (fb_KT hL lay ho ho2 hrN).count_eq,
      (fb_PK hL lay ho ho2 hrN).count_eq, (fb_GP hL lay ho ho2 hrN).count_eq, (fb_TL hL lay ho ho2 hrN).count_eq,
      (fb_DEP hL lay ho ho2 hrN).count_eq, (fb_XP0 hL lay ho ho2 hrN).count_eq, (fb_XG hL lay ho ho2 hrN).count_eq,
      (fb_XST hL lay ho ho2 hrN).count_eq, (fb_XL0 hL lay ho ho2 hrN).count_eq,
      (fb_XLH hL lay ho ho2 hrN).count_eq]
    rw [rc_split, peo_split, leaf_split]
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_nil, List.count_append, List.count_nil,
      List.append_nil, List.nil_append]
    omega
  · simp only [planSegs, plan, List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, ↓reduceIte, List.count_append,
      List.nil_append]
    rw [(fb_PL hL lay ho ho2 hrN).count_eq, (fb_P hL lay ho ho2 hrN).count_eq, (fb_VL hL lay ho ho2 hrN).count_eq,
      (fb_V hL lay ho ho2 hrN).count_eq, (fb_RID hL lay ho ho2 hrN).count_eq, (fb_T0 hL lay ho ho2 hrN).count_eq,
      (fb_SL hL lay ho ho2 hrN).count_eq, (fb_S hL lay ho ho2 hrN).count_eq, (fb_KT hL lay ho ho2 hrN).count_eq,
      (fb_PK hL lay ho ho2 hrN).count_eq, (fb_GP hL lay ho ho2 hrN).count_eq, (fb_TL hL lay ho ho2 hrN).count_eq,
      (fb_DEP hL lay ho ho2 hrN).count_eq, (fb_XP0 hL lay ho ho2 hrN).count_eq,
      (fb_XRI hL lay ho ho2 hrN rfl).count_eq, (fb_XG hL lay ho ho2 hrN).count_eq,
      (fb_XST hL lay ho ho2 hrN).count_eq, (fb_XL0 hL lay ho ho2 hrN).count_eq,
      (fb_XLH hL lay ho ho2 hrN).count_eq, (fb_XRH hL lay ho ho2 hrN rfl).count_eq,
      (fb_XRF hL lay ho ho2 hrN rfl).count_eq, (fb_XRZ hL lay ho ho2 hrN rfl).count_eq]
    rw [rc_split, rf_split _ _ _ rfl, peo_split, leaf_split, rid_split _ _ _ rfl]
    simp only [↓reduceIte, List.map_append, List.map_nil, List.count_append, List.count_nil,
      List.append_nil, List.nil_append]
    omega

end ZkFormal.Near.RcptProof
