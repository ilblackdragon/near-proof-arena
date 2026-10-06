import ZkFormal.NearV3.Rcpt.Extract.V.Gates

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Bus (v1 `RcptBus`) — `FINAL`, `MPOS`, `MEM`, `RIDS` messages of a receipt

Each of these buses is used by one field of the receipt (`PL` row 0, `DEP`,
`RID`); the other rows send nothing on it (`flatMap_window`).
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.Rcpt (bitsX bitsXn pubs ks leE G_LE S_LE conv ovf SS hiE loE sepE sepN hexE hexN sq lb' DE DEn pE surE aftE)
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Rows outside a window contribute nothing. -/
theorem flatMap_window {α : Type} (f : Nat → List α) (s T a L : Nat) (hle : a + L ≤ T)
    (hz : ∀ j, j < T → (j < a ∨ a + L ≤ j) → f (s + j) = []) :
    (List.range' s T).flatMap f = (List.range' (s + a) L).flatMap f := by
  have e : List.range' s T = List.range' s a ++ (List.range' (s + a) L ++ List.range' (s + a + L) (T - a - L)) := by
    rw [List.range'_append_1, List.range'_append_1]; congr 1; omega
  rw [e, List.flatMap_append, List.flatMap_append,
    flatMap_range'_nil f s a (fun j hj => hz j (by omega) (Or.inl hj)),
    flatMap_range'_nil f (s + a + L) (T - a - L) (fun j hj => by
      rw [show s + a + L + j = s + (a + L + j) by omega]; exact hz _ (by omega) (Or.inr (by omega)))]
  simp

theorem gt_zero {x : Fp} (h : x = 0) (m : List Fp) : gt x m = [] := by simp [gt, h]
theorem gt_one {x : Fp} (h : x = 1) (m : List Fp) : gt x m = [m] := by simp [gt, h]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem rf_row {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
    (hrf : tr.cell tt s rf = 1) (j : Nat) (hj : j < total h Lp Lv Ls kt) :
    tr.cell tt (s + j) rf = if j = 0 then 1 else 0 := by
  have hfin := lay.fin
  split
  · rename_i h0; subst h0; simpa using hrf
  · rename_i h0
    refine bool01 hL (by omega) (by simp [boolCols]) (fun h1 => ?_)
    obtain ⟨hpl, hfs⟩ := (bounds hL (r := s + j) (by omega)).2.1 h1
    rw [cell_state hL lay (X := sPL) (off := 0) (L := 4) (by simp [plan]) j hj] at hpl
    have hj4 : j < 4 := by
      by_cases hh : 0 ≤ j ∧ j < 0 + 4
      · omega
      · rw [if_neg hh] at hpl; exact absurd hpl fp_zero_ne_one
    have F := (lay.flds (sPL, 0, 4) (by simp [plan])).fld
    have := F.fs j hj4
    rw [show s + (sPL, 0, 4).2.1 + j = s + j by simp, hfs, if_neg h0] at this
    exact fp_one_ne_zero this

/-- A state cell on a receipt row, as a field indicator. -/
theorem st_row {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
    {X off L : Nat} (hm : (X, off, L) ∈ plan h Lp Lv Ls kt) (j : Nat) (hj : j < total h Lp Lv Ls kt)
    (hout : j < off ∨ off + L ≤ j) : tr.cell tt (s + j) X = 0 := by
  rw [cell_state hL lay hm j hj, if_neg (by omega)]

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.Rcpt (bitsX bitsXn pubs ks leE G_LE S_LE conv ovf SS hiE loE sepE sepN hexE hexN sq lb' DE DEn pE surE aftE)
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rowT_memR (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_MEM false =
    gt (C tr tt q sDEP) [C tr tt q kslot, C tr tt q tprev, C tr tt q idx, C tr tt q bef, C tr tt q lk, C tr tt q st] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]
theorem rowT_memS (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_MEM true =
    gt (C tr tt q sDEP) [C tr tt q kslot, C tr tt q RcptV3.r + (1 : Nat), C tr tt q idx, aftE.eval tr tt q pub,
      C tr tt q lk, C tr tt q st] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]
theorem rowT_rids (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_RIDS true =
    gt (C tr tt q sRID) [C tr tt q RcptV3.r, C tr tt q idx, C tr tt q b] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]
theorem rowT_final (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_FINAL false =
    gt (C tr tt q gF) [C tr tt q RcptV3.r + (W_AK : Nat) * C tr tt q sT0, (0 : Nat), C tr tt q fkF, C tr tt q kF] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]
theorem rowT_mpos (q : Nat) : rowTraffic RcptV3.interactions tr tt q pub B_MPOS true =
    gt (C tr tt q rf) [(0 : Nat), C tr tt q RcptV3.r, (K_LEAF : Nat) + (16 : Nat) * C tr tt q RcptV3.r, (68 : Nat)] := by
  rw [rowT]; simp [B_BYTES, B_DIGEST, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, B_RCL, B_SREC, B_AKC, B_BND]

theorem fpN (a : Fp) : Fp.ofNat a.toNat = a := Fp.ofNat_toNat a

section
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) {rN : Nat}
  (hrN : tr.cell tt s RcptV3.r = (rN : Fp))
include lay hrN

theorem rcpt_memR :
    (List.range' s (total h Lp Lv Ls kt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM false) =
      ((List.range 16).map fun i => ([(rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).kslot, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).tprev, i,
        (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).bef.getD i 0, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).lk.getD i 0,
        (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).st.getD i 0] : Msg)).map Msg.toFp := by
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have F : RFld tr tt s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP := lay.flds _ hm
  rw [flatMap_window _ s _ (107 + Vt Lp Lv Ls kt) 16 (by simpa using hle) (fun j hj hout => by
    rw [rowT_memR]; exact gt_zero (st_row hL lay hm j hj hout) _)]
  rw [flatMap_range'_single _ (fun i => ([(rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).kslot,
      (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).tprev, i, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).bef.getD i 0,
      (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).lk.getD i 0, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).st.getD i 0] : Msg) |>.map Fp.ofNat)
    _ 16 (fun i hi => ?_), List.map_map]
  · rfl
  · rw [rowT_memR]; simp only [C]; rw [gt_one (F.fld.st i hi)]
    simp only [rcptOf, colAt_get _ _ _ _ _ _ hi, Msg.toFp, List.map_cons, List.map_nil, C, cv, fpN]
    rw [F.consts i hi kslot (by simp [rconsts]), F.consts i hi tprev (by simp [rconsts]), F.fld.idx i hi]
    simp [natCast_eq]

theorem rcpt_memS :
    (List.range' s (total h Lp Lv Ls kt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM true) =
      ((List.range 16).map fun i => ([(rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).kslot, rN + 1, i,
        (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).aft.getD i 0, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).lk.getD i 0,
        (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).st.getD i 0] : Msg)).map Msg.toFp := by
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have hfin := lay.fin
  have F : RFld tr tt s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP := lay.flds _ hm
  rw [flatMap_window _ s _ (107 + Vt Lp Lv Ls kt) 16 (by simpa using hle) (fun j hj hout => by
    rw [rowT_memS]; exact gt_zero (st_row hL lay hm j hj hout) _)]
  rw [flatMap_range'_single _ (fun i => ([(rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).kslot, rN + 1, i,
      (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).aft.getD i 0,
      (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).lk.getD i 0, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).st.getD i 0] : Msg) |>.map Fp.ofNat)
    _ 16 (fun i hi => ?_), List.map_map]
  · rfl
  · rw [rowT_memS]; simp only [C]; rw [gt_one (F.fld.st i hi)]
    have hb := eval_bits tr tt (s + (107 + Vt Lp Lv Ls kt) + i) pub ZkFormal.Near.Rcpt.xb 0 8 (fun j hj =>
      isBool hL (by simp at hle; omega) (by
        unfold boolCols; simp only [List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨0 + j, List.mem_range.mpr (by omega), rfl⟩))))
    simp only [aftE, bitsX] at hb ⊢
    rw [hb]
    simp only [rcptOf, colAt_get _ _ _ _ _ _ hi, Msg.toFp, List.map_cons, List.map_nil, C, cv, fpN,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
    rw [F.consts i hi kslot (by simp [rconsts]), F.consts i hi RcptV3.r (by simp [rconsts]), F.fld.idx i hi, hrN]
    simp [natCast_eq]
    rfl

theorem rcpt_rids :
    (List.range' s (total h Lp Lv Ls kt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RIDS true) =
      ((List.range 32).map fun i => ([rN, i, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).rid.getD i 0] : Msg)).map Msg.toFp := by
  have hm : (sRID, 8 + Lp + Lv, 32) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have F : RFld tr tt s (s + (8 + Lp + Lv)) 32 sRID := lay.flds _ hm
  rw [flatMap_window _ s _ (8 + Lp + Lv) 32 (by simpa using hle) (fun j hj hout => by
    rw [rowT_rids]; exact gt_zero (st_row hL lay hm j hj hout) _)]
  rw [flatMap_range'_single _ (fun i => ([rN, i, (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).rid.getD i 0] : Msg) |>.map Fp.ofNat)
    _ 32 (fun i hi => ?_), List.map_map]
  · rfl
  · rw [rowT_rids]; simp only [C]; rw [gt_one (F.fld.st i hi)]
    simp only [rcptOf, colAt_get _ _ _ _ _ _ hi, Msg.toFp, List.map_cons, List.map_nil, C, cv, fpN]
    rw [F.consts i hi RcptV3.r (by simp [rconsts]), F.fld.idx i hi, hrN]
    simp [natCast_eq]

/-- The `T0` row of a receipt. -/
def t0Off (Lp Lv : Nat) : Nat := 40 + Lp + Lv

theorem gF_row (hrf : tr.cell tt s rf = 1) (i : Nat) (hi : i < total h Lp Lv Ls kt) :
    tr.cell tt (s + i) gF = (if i = 0 then 1 else 0) +
      tr.cell tt s ee * (if i = t0Off Lp Lv then 1 else 0) := by
  have hfin := lay.fin
  have hm : (sT0, 40 + Lp + Lv, 1) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hg := con hL (r := s + i) (by omega) (e := sub (c gF) (.add (c rf) (.mul (c ee) (c sT0))))
    (mem_ky (by simp [cKey]))
  simp only [eval_sub, eval_add, eval_mul, eval_c] at hg
  have h1 := rf_row hL lay hrf i hi
  have h2 := cell_state hL lay hm i hi
  have hee : tr.cell tt (s + i) ee = tr.cell tt s ee := by
    have := lay_const hL lay i hi ee (by simp [rconsts]); exact this
  rw [h1, h2, hee] at hg
  have e : (if 40 + Lp + Lv ≤ i ∧ i < 40 + Lp + Lv + 1 then (1 : Fp) else 0) =
      if i = t0Off Lp Lv then 1 else 0 := by
    unfold t0Off; by_cases hh : i = 40 + Lp + Lv
    · rw [if_pos (by omega), if_pos hh]
    · rw [if_neg (by omega), if_neg hh]
  rw [e] at hg; grind

theorem rcpt_mpos (hrf : tr.cell tt s rf = 1) :
    (List.range' s (total h Lp Lv Ls kt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MPOS true) =
      [Msg.toFp [0, rN, msgId K_LEAF rN, 68]] := by
  have hT := total_pos h Lp Lv Ls kt
  rw [flatMap_window _ s _ 0 1 (by omega) (fun j hj hout => by
    rw [rowT_mpos]; exact gt_zero (by show tr.cell tt (s + j) rf = 0; rw [rf_row hL lay hrf j hj, if_neg (by omega)]) _)]
  simp only [List.range'_one, List.flatMap_singleton, Nat.add_zero, rowT_mpos, C]; rw [gt_one hrf]
  simp [Msg.toFp, C, hrN, natCast_eq, msgId]

end

end ZkFormal.NearV3.RcptV3Proof
