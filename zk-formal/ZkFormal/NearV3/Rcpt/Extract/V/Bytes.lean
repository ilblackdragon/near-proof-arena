import ZkFormal.NearV3.Rcpt.Extract.V.FB2

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Bytes (v1 `RcptBytes`) — the `BYTES` messages of one receipt

The view's encodings split into the chunks the fields emit (`rc_split`,
`rf_split`, `peo_split`, `leaf_split`, `rid_split`), and the receipt's rows
emit exactly these chunks (`rcpt_bytes`, up to permutation).
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.Rcpt (bitsX bitsXn pubs ks leE G_LE S_LE conv ovf SS hiE loE sepE sepN hexE hexN sq lb' DE DEn pE surE aftE)
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The `BYTES` messages of receipt `r` in the view (without the claim header). -/
def rcptBytesV (pub : List Fp) (x : RcptE) (jN oN o2N r : Nat) : List Msg :=
  emitAt (msgId K_RC jN) oN x.enc ++ (if x.hr then emitAt K_RF o2N x.encRefund else []) ++
    emitAt (msgId K_PEO r) 0 x.peo ++ emitAt (msgId K_LEAF r) 0 x.leaf ++
    (if x.hr then emitAt (msgId K_RID r) 0 (x.rid ++ pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0) else [])

section split
variable (tr : Trace Fp) (y : RS)

theorem rc_split (jN oN : Nat) :
    emitAt (msgId K_RC jN) oN (rcptOf tr tt y).enc =
      emitAt (msgId K_RC jN) oN (u32r y.Lp) ++ emitAt (msgId K_RC jN) (oN + 4) (colAt tr tt (y.s + 4) y.Lp b) ++
      emitAt (msgId K_RC jN) (oN + (4 + y.Lp)) (u32r y.Lv) ++
      emitAt (msgId K_RC jN) (oN + (8 + y.Lp)) (colAt tr tt (y.s + (8 + y.Lp)) y.Lv b) ++
      emitAt (msgId K_RC jN) (oN + (8 + y.Lp + y.Lv)) (colAt tr tt (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt (msgId K_RC jN) (oN + (40 + y.Lp + y.Lv)) [0] ++ emitAt (msgId K_RC jN) (oN + (41 + y.Lp + y.Lv)) (u32r y.Ls) ++
      emitAt (msgId K_RC jN) (oN + (45 + y.Lp + y.Lv)) (colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt (msgId K_RC jN) (oN + (45 + y.Lp + y.Lv + y.Ls)) [y.kt] ++
      emitAt (msgId K_RC jN) (oN + (46 + y.Lp + y.Lv + y.Ls)) (colAt tr tt (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b) ++
      emitAt (msgId K_RC jN) (oN + (78 + Vt y.Lp y.Lv y.Ls y.kt)) (colAt tr tt (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b) ++
      emitAt (msgId K_RC jN) (oN + (94 + Vt y.Lp y.Lv y.Ls y.kt)) tailN ++
      emitAt (msgId K_RC jN) (oN + (107 + Vt y.Lp y.Lv y.Ls y.kt)) (colAt tr tt (y.s + (107 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b) := by
  have hc := emitAt_chunks (msgId K_RC jN)
    [(oN, u32r y.Lp), (oN + 4, colAt tr tt (y.s + 4) y.Lp b), (oN + (4 + y.Lp), u32r y.Lv),
     (oN + (8 + y.Lp), colAt tr tt (y.s + (8 + y.Lp)) y.Lv b),
     (oN + (8 + y.Lp + y.Lv), colAt tr tt (y.s + (8 + y.Lp + y.Lv)) 32 b), (oN + (40 + y.Lp + y.Lv), [0]),
     (oN + (41 + y.Lp + y.Lv), u32r y.Ls), (oN + (45 + y.Lp + y.Lv), colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (oN + (45 + y.Lp + y.Lv + y.Ls), [y.kt]),
     (oN + (46 + y.Lp + y.Lv + y.Ls), colAt tr tt (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b),
     (oN + (78 + Vt y.Lp y.Lv y.Ls y.kt), colAt tr tt (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b),
     (oN + (94 + Vt y.Lp y.Lv y.Ls y.kt), tailN),
     (oN + (107 + Vt y.Lp y.Lv y.Ls y.kt), colAt tr tt (y.s + (107 + Vt y.Lp y.Lv y.Ls y.kt)) 16 b)] oN
    (by simp [Consec2, colAt_len, u32r, tailN, Vt]; omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1
  simp [RcptV.enc, rcptOf, RcptV.borshN, colAt_len, List.append_assoc]

theorem leaf_split (r : Nat) :
    emitAt (msgId K_LEAF r) 0 (rcptOf tr tt y).leaf =
      emitAt (msgId K_LEAF r) 0 [2, 0, 0, 0] ++ emitAt (msgId K_LEAF r) 4 (colAt tr tt (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt (msgId K_LEAF r) 36 (colAt tr tt (y.s + (144 + 32 * hN y.h + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) := by
  have hc := emitAt_chunks (msgId K_LEAF r)
    [(0, [2, 0, 0, 0]), (4, colAt tr tt (y.s + (8 + y.Lp + y.Lv)) 32 b),
     (36, colAt tr tt (y.s + (144 + 32 * hN y.h + Vt y.Lp y.Lv y.Ls y.kt)) 32 b)] 0
    (by simp [Consec2, colAt_len])
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1 <;> simp [RcptV.leaf, rcptOf, List.append_assoc]

theorem peo_split (r : Nat) :
    emitAt (msgId K_PEO r) 0 (rcptOf tr tt y).peo =
      emitAt (msgId K_PEO r) 0 (u32r (hN y.h)) ++
      (if y.h then emitAt (msgId K_PEO r) 4 (colAt tr tt (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) else []) ++
      emitAt (msgId K_PEO r) (4 + 32 * hN y.h) G_LEn ++
      emitAt (msgId K_PEO r) (12 + 32 * hN y.h) (colAt tr tt (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 burnt) ++
      emitAt (msgId K_PEO r) (28 + 32 * hN y.h) (u32r y.Lv) ++
      emitAt (msgId K_PEO r) (32 + 32 * hN y.h) (colAt tr tt (y.s + (8 + y.Lp)) y.Lv b) ++
      emitAt (msgId K_PEO r) (32 + 32 * hN y.h + y.Lv) [2, 0, 0, 0, 0] := by
  obtain ⟨s, h, Lp, Lv, Ls, kt⟩ := y
  cases h
  · have hc := emitAt_chunks (msgId K_PEO r)
      [(0, u32r (hN false)), (4 + 32 * hN false, G_LEn),
       (12 + 32 * hN false, colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 burnt), (28 + 32 * hN false, u32r Lv),
       (32 + 32 * hN false, colAt tr tt (s + (8 + Lp)) Lv b), (32 + 32 * hN false + Lv, [2, 0, 0, 0, 0])] 0
      (by simp [Consec2, colAt_len, u32r, G_LEn, hN])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    simp only [List.append_assoc]
    rw [← hc]
    congr 1
    simp [RcptV.peo, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hN]
  · have hc := emitAt_chunks (msgId K_PEO r)
      [(0, u32r (hN true)), (4, colAt tr tt (s + (127 + Vt Lp Lv Ls kt)) 32 b), (4 + 32 * hN true, G_LEn),
       (12 + 32 * hN true, colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 burnt), (28 + 32 * hN true, u32r Lv),
       (32 + 32 * hN true, colAt tr tt (s + (8 + Lp)) Lv b), (32 + 32 * hN true + Lv, [2, 0, 0, 0, 0])] 0
      (by simp [Consec2, colAt_len, u32r, G_LEn, hN])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    simp only [↓reduceIte]
    simp only [List.append_assoc]
    rw [← hc]
    congr 1
    simp [RcptV.peo, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hN]

theorem rf_split (o2N : Nat) (hh : y.h = true) :
    emitAt K_RF o2N (rcptOf tr tt y).encRefund =
      emitAt K_RF o2N ([6, 0, 0, 0] ++ systemN) ++ emitAt K_RF (o2N + 10) (u32r y.Ls) ++
      emitAt K_RF (o2N + 14) (colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt K_RF (o2N + (14 + y.Ls)) (colAt tr tt (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b) ++
      emitAt K_RF (o2N + (46 + y.Ls)) [0] ++ emitAt K_RF (o2N + (47 + y.Ls)) (u32r y.Ls) ++
      emitAt K_RF (o2N + (51 + y.Ls)) (colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b) ++
      emitAt K_RF (o2N + (51 + 2 * y.Ls)) [y.kt] ++
      emitAt K_RF (o2N + (52 + 2 * y.Ls)) (colAt tr tt (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b) ++
      emitAt K_RF (o2N + (84 + 2 * y.Ls + 32 * y.kt)) (List.replicate 16 0) ++
      emitAt K_RF (o2N + (100 + 2 * y.Ls + 32 * y.kt)) tailN ++
      emitAt K_RF (o2N + (113 + 2 * y.Ls + 32 * y.kt)) (colAt tr tt (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 ramt) := by
  have hc := emitAt_chunks K_RF
    [(o2N, [6, 0, 0, 0] ++ systemN), (o2N + 10, u32r y.Ls), (o2N + 14, colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (o2N + (14 + y.Ls), colAt tr tt (y.s + (127 + Vt y.Lp y.Lv y.Ls y.kt)) 32 b), (o2N + (46 + y.Ls), [0]),
     (o2N + (47 + y.Ls), u32r y.Ls), (o2N + (51 + y.Ls), colAt tr tt (y.s + (45 + y.Lp + y.Lv)) y.Ls b),
     (o2N + (51 + 2 * y.Ls), [y.kt]),
     (o2N + (52 + 2 * y.Ls), colAt tr tt (y.s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b),
     (o2N + (84 + 2 * y.Ls + 32 * y.kt), List.replicate 16 0), (o2N + (100 + 2 * y.Ls + 32 * y.kt), tailN),
     (o2N + (113 + 2 * y.Ls + 32 * y.kt), colAt tr tt (y.s + (78 + Vt y.Lp y.Lv y.Ls y.kt)) 16 ramt)] o2N
    (by simp [Consec2, colAt_len, u32r, tailN, systemN]; omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
  simp only [List.append_assoc]
  rw [← hc]
  congr 1
  simp [RcptV.encRefund, rcptOf, RcptV.borshN, colAt_len, List.append_assoc, hh]

theorem rid_split (r : Nat) (hh : y.h = true) :
    emitAt (msgId K_RID r) 0 ((rcptOf tr tt y).rid ++ pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0) =
      emitAt (msgId K_RID r) 0 (colAt tr tt (y.s + (8 + y.Lp + y.Lv)) 32 b) ++
      emitAt (msgId K_RID r) 32 (pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0) := by
  rw [List.append_assoc, emitAt_append]
  simp [rcptOf, colAt_len]

end split

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.Rcpt (bitsX bitsXn pubs ks leE G_LE S_LE conv ovf SS hiE loE sepE sepN hexE hexN sq lb' DE DEn pE surE aftE)
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rowT_bytes (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_BYTES true = (List.range 3).flatMap (slotT tr tt q) := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]

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

theorem rcptOf_hr (y : RS) : (rcptOf tr tt y).hr = y.h := rfl

/-- **The `BYTES` messages of a receipt.** -/
theorem rcpt_bytes (hL : TableLocal RcptV3.table tr tt pub) {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat}
    (lay : Layout tr tt s h Lp Lv Ls kt) {oN o2N rN : Nat}
    (ho : tr.cell tt s o = (oN : Fp)) (ho2 : tr.cell tt s o2 = (o2N : Fp))
    (hrN : tr.cell tt s RcptV3.r = (rN : Fp)) {jN : Nat}
    (hj : ∀ q, s ≤ q → q < s + total h Lp Lv Ls kt → tr.cell tt q j = (jN : Fp)) :
    ((List.range' s (total h Lp Lv Ls kt)).flatMap fun q =>
      rowTraffic RcptV3.interactions tr tt q pub B_BYTES true).Perm
      ((rcptBytesV pub (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩) jN oN o2N rN).map Msg.toFp) := by
  rw [flatMap_congr' (G := fun q => (List.range 3).flatMap (slotT tr tt q)) (fun q _ => rowT_bytes q),
    range'_plan, List.flatMap_assoc]
  rw [show ((planSegs s h Lp Lv Ls kt).flatMap fun p =>
      (List.range' p.1 p.2).flatMap fun q => (List.range 3).flatMap (slotT tr tt q)) =
      (planSegs s h Lp Lv Ls kt).flatMap (fun p => fieldRows tr tt p.1 p.2) from rfl]
  rw [List.perm_iff_count]; intro m
  unfold rcptBytesV
  rw [rcptOf_hr]
  cases h
  · simp only [planSegs, plan, List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.count_append,
      List.nil_append]
    rw [(fb_PL hL lay ho ho2 hrN hj).count_eq, (fb_P hL lay ho ho2 hrN hj).count_eq, (fb_VL hL lay ho ho2 hrN hj).count_eq,
      (fb_V hL lay ho ho2 hrN hj).count_eq, (fb_RID hL lay ho ho2 hrN hj).count_eq, (fb_T0 hL lay ho ho2 hrN hj).count_eq,
      (fb_SL hL lay ho ho2 hrN hj).count_eq, (fb_S hL lay ho ho2 hrN hj).count_eq, (fb_KT hL lay ho ho2 hrN hj).count_eq,
      (fb_PK hL lay ho ho2 hrN hj).count_eq, (fb_GP hL lay ho ho2 hrN hj).count_eq, (fb_TL hL lay ho ho2 hrN hj).count_eq,
      (fb_DEP hL lay ho ho2 hrN hj).count_eq, (fb_XP0 hL lay ho ho2 hrN hj).count_eq, (fb_XG hL lay ho ho2 hrN hj).count_eq,
      (fb_XST hL lay ho ho2 hrN hj).count_eq, (fb_XL0 hL lay ho ho2 hrN hj).count_eq,
      (fb_XLH hL lay ho ho2 hrN hj).count_eq]
    rw [rc_split, peo_split, leaf_split]
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_nil, List.count_append, List.count_nil,
      List.append_nil, List.nil_append]
    omega
  · simp only [planSegs, plan, List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, ↓reduceIte, List.count_append,
      List.nil_append]
    rw [(fb_PL hL lay ho ho2 hrN hj).count_eq, (fb_P hL lay ho ho2 hrN hj).count_eq, (fb_VL hL lay ho ho2 hrN hj).count_eq,
      (fb_V hL lay ho ho2 hrN hj).count_eq, (fb_RID hL lay ho ho2 hrN hj).count_eq, (fb_T0 hL lay ho ho2 hrN hj).count_eq,
      (fb_SL hL lay ho ho2 hrN hj).count_eq, (fb_S hL lay ho ho2 hrN hj).count_eq, (fb_KT hL lay ho ho2 hrN hj).count_eq,
      (fb_PK hL lay ho ho2 hrN hj).count_eq, (fb_GP hL lay ho ho2 hrN hj).count_eq, (fb_TL hL lay ho ho2 hrN hj).count_eq,
      (fb_DEP hL lay ho ho2 hrN hj).count_eq, (fb_XP0 hL lay ho ho2 hrN hj).count_eq,
      (fb_XRI hL lay ho ho2 hrN hj rfl).count_eq, (fb_XG hL lay ho ho2 hrN hj).count_eq,
      (fb_XST hL lay ho ho2 hrN hj).count_eq, (fb_XL0 hL lay ho ho2 hrN hj).count_eq,
      (fb_XLH hL lay ho ho2 hrN hj).count_eq, (fb_XRH hL lay ho ho2 hrN hj rfl).count_eq,
      (fb_XRF hL lay ho ho2 hrN hj rfl).count_eq, (fb_XRZ hL lay ho ho2 hrN hj rfl).count_eq]
    rw [rc_split, rf_split _ _ _ rfl, peo_split, leaf_split, rid_split _ _ _ rfl]
    simp only [↓reduceIte, List.map_append, List.map_nil, List.count_append, List.count_nil,
      List.append_nil, List.nil_append]
    omega

end ZkFormal.NearV3.RcptV3Proof
