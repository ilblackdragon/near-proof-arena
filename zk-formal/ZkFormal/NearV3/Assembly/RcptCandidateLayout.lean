import ZkFormal.NearV3.Assembly.RcptCandidateSegs
import ZkFormal.NearV3.Rcpt.Extract.V.Layout
-- Source Layout.lean SHA256: eb1dd21f4273c3d2a80a17ff11e46be32ccf0a321b426549d062b135487be4cd.
-- Migrates control proofs only; original Fld/RFld/Layout data types are reused.
namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- A receipt field from its first row. -/
theorem rfld {s r0 X : Nat} (hr0 : r0 < tr.height tt) (hX : X ∈ states) (hne : X ≠ sCL)
    (h1 : tr.cell tt r0 X = 1) (hi : tr.cell tt r0 idx = 0) (hfs : tr.cell tt r0 fs = 1)
    (hc : ∀ x ∈ rconsts, tr.cell tt r0 x = tr.cell tt s x) :
    ∃ L, r0 + L < tr.height tt ∧ RFld tr tt s r0 L X := by
  obtain ⟨L, hLH, F⟩ := fld_from hL hr0 hX h1 hi hfs
  refine ⟨L, hLH, F, fun j hj x hx => ?_⟩
  rw [fld_consts hL (by omega) F hX hne j hj x hx, hc x hx]

/-- `rl = 0` on the rows of a field in a state other than `XRZ`, `XLH`. -/
theorem fld_rl0 {r0 L X : Nat} (hH : r0 + L ≤ tr.height tt) (F : Fld tr tt r0 L X) (hX : X ∈ states)
    (h1 : X ≠ sXRZ) (h2 : X ≠ sXLH) : ∀ j, j < L → tr.cell tt (r0 + j) rl = 0 := by
  intro j hj
  rw [rl_at hL (by omega) hX (F.st j hj), if_neg h1, if_neg h2]; grind

/-- From one receipt field to the next. -/
theorem rnext {s r0 L X X' : Nat} {g : Expr} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X)
    (hX : X ∈ states) (hX' : X' ∈ states) (hne : X ≠ sCL) (hne' : X' ≠ sCL)
    (hrl : tr.cell tt (r0 + (L - 1)) rl = 0)
    (hs : (X, X', g) ∈ RcptV3.succ) (hg : g.eval tr tt (r0 + (L - 1)) pub = 1) :
    ∃ L', r0 + L + L' < tr.height tt ∧ RFld tr tt s (r0 + L) L' X' := by
  have hp := F.fld.pos
  obtain ⟨hq, h1, hi, hfs⟩ := fld_next hL hH F.fld hrl hs hg
  have hc : tr.cell tt (r0 + (L - 1)) sCL = 0 :=
    (oneHot hL (by omega) hX (F.fld.st (L - 1) (by omega))).2 sCL (by simp [states]) (Ne.symm hne)
  have K := consts_next hL (q := r0 + (L - 1)) (by omega) (F.fld.act (L - 1) (by omega)) hc hrl
  rw [show r0 + (L - 1) + 1 = r0 + L by omega] at K
  obtain ⟨L', h', F'⟩ := rfld hL (s := s) hq hX' hne' h1 hi hfs (fun x hx => by
    rw [K x hx, F.consts (L - 1) (by omega) x hx])
  exact ⟨L', by omega, F'⟩

omit hL in
theorem cst {s r0 L X : Nat} (F : RFld tr tt s r0 L X) {x : Nat} (hx : x ∈ rconsts) (j : Nat) (hj : j < L) :
    tr.cell tt (r0 + j) x = tr.cell tt s x := F.consts j hj x hx

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem hrC : RcptV3.hr ∈ rconsts := by simp [rconsts]
theorem LpC : RcptV3.Lp ∈ rconsts := by simp [rconsts]
theorem LvC : RcptV3.Lv ∈ rconsts := by simp [rconsts]
theorem LsC : RcptV3.Ls ∈ rconsts := by simp [rconsts]
theorem ktC : RcptV3.kt ∈ rconsts := by simp [rconsts]

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- A variable field length `L` with last index `x − 1` (`x` a receipt constant). -/
theorem var_len {s r0 L X x : Nat} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X)
    (hx : (X, sub (c x) (k 1)) ∈ lastIdx) (hxc : x ∈ rconsts) :
    tr.cell tt s x = (L : Fp) := by
  have hp := F.fld.pos
  have e := fld_len hL hH F.fld hx
  simp only [eval_sub, eval_c, eval_k] at e
  rw [cst F hxc (L - 1) (by omega)] at e
  have : (L : Fp) = (((L - 1 : Nat) : Nat) : Fp) + 1 := by
    rw [show (1 : Fp) = ((1 : Nat) : Fp) from rfl, ← natCast_add, Nat.sub_add_cancel hp]
  rw [this, e]; grind

/-- The end of a field in a state other than `XRZ`, `XLH`: `rl = 0`. -/
theorem end_rl0 {s r0 L X : Nat} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : X ∈ states)
    (h1 : X ≠ sXRZ) (h2 : X ≠ sXLH) : tr.cell tt (r0 + (L - 1)) rl = 0 :=
  fld_rl0 hL hH F.fld hX h1 h2 (L - 1) (by have := F.fld.pos; omega)

/-- `rl` at the end of the `XLH` field. -/
theorem xlh_rl {s r0 L : Nat} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L sXLH) :
    tr.cell tt (r0 + (L - 1)) rl = 1 - tr.cell tt s RcptV3.hr := by
  have hp := F.fld.pos
  rw [rl_at hL (by omega) (by simp [states]) (F.fld.st (L - 1) (by omega)), F.fld.fe (L - 1) (by omega),
    if_pos (by omega), if_neg (by decide), if_pos rfl, cst F hrC (L - 1) (by omega)]
  grind

/-- `rl` at the end of the `XRZ` field. -/
theorem xrz_rl {s r0 L : Nat} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L sXRZ) :
    tr.cell tt (r0 + (L - 1)) rl = 1 := by
  have hp := F.fld.pos
  rw [rl_at hL (by omega) (by simp [states]) (F.fld.st (L - 1) (by omega)), F.fld.fe (L - 1) (by omega),
    if_pos (by omega), if_pos rfl, if_neg (by decide)]
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The fields up to `XP0` (common to both shapes). -/
theorem prefix_of {s : Nat} (hs : s < tr.height tt) (hrf : tr.cell tt s rf = 1) :
    ∃ Lp Lv Ls kt : Nat, tr.cell tt s RcptV3.Lp = (Lp : Fp) ∧ tr.cell tt s RcptV3.Lv = (Lv : Fp) ∧
      tr.cell tt s RcptV3.Ls = (Ls : Fp) ∧ tr.cell tt s RcptV3.kt = (kt : Fp) ∧ kt ≤ 1 ∧
      1 ≤ Lp ∧ 1 ≤ Lv ∧ 1 ≤ Ls ∧
      s + 127 + Vt Lp Lv Ls kt < tr.height tt ∧
      RFld tr tt s s 4 sPL ∧ RFld tr tt s (s + 4) Lp sP ∧ RFld tr tt s (s + (4 + Lp)) 4 sVL ∧
      RFld tr tt s (s + (8 + Lp)) Lv sV ∧ RFld tr tt s (s + (8 + Lp + Lv)) 32 sRID ∧
      RFld tr tt s (s + (40 + Lp + Lv)) 1 sT0 ∧ RFld tr tt s (s + (41 + Lp + Lv)) 4 sSL ∧
      RFld tr tt s (s + (45 + Lp + Lv)) Ls sS ∧ RFld tr tt s (s + (45 + Lp + Lv + Ls)) 1 sKT ∧
      RFld tr tt s (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) sPK ∧
      RFld tr tt s (s + (78 + Vt Lp Lv Ls kt)) 16 sGP ∧ RFld tr tt s (s + (94 + Vt Lp Lv Ls kt)) 13 sTL ∧
      RFld tr tt s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP ∧ RFld tr tt s (s + (123 + Vt Lp Lv Ls kt)) 4 sXP0 := by
  obtain ⟨hPL, hfs⟩ := (bounds hL hs).2.1 hrf
  have hidx := rf_idx hL hs hrf
  -- PL
  obtain ⟨L1, H1, F1⟩ := rfld hL (s := s) hs (X := sPL) (by simp [states]) (by decide) hPL hidx hfs
    (fun _ _ => rfl)
  have e1 := fld_len_k hL (by omega) F1.fld (m := 3) (by simp [lastIdx]) (by decide)
  subst e1
  -- P
  obtain ⟨Lp, H2, F2⟩ := rnext hL (by omega) F1 (X' := sP) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F1 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have cLp := var_len hL (by omega) F2 (by simp [lastIdx]) LpC
  have pLp := F2.fld.pos
  -- VL
  obtain ⟨L3, H3, F3⟩ := rnext hL (by omega) F2 (X' := sVL) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F2 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e3 := fld_len_k hL (by omega) F3.fld (m := 3) (by simp [lastIdx]) (by decide)
  subst e3
  -- V
  obtain ⟨Lv, H4, F4⟩ := rnext hL (by omega) F3 (X' := sV) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F3 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have cLv := var_len hL (by omega) F4 (by simp [lastIdx]) LvC
  have pLv := F4.fld.pos
  -- RID
  obtain ⟨L5, H5, F5⟩ := rnext hL (by omega) F4 (X' := sRID) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F4 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e5 := fld_len_k hL (by omega) F5.fld (m := 31) (by simp [lastIdx]) (by decide)
  subst e5
  -- T0
  obtain ⟨L6, H6, F6⟩ := rnext hL (by omega) F5 (X' := sT0) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F5 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e6 := fld_len_k hL (by omega) F6.fld (m := 0) (by simp [lastIdx]) (by decide)
  subst e6
  -- SL
  obtain ⟨L7, H7, F7⟩ := rnext hL (by omega) F6 (X' := sSL) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F6 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e7 := fld_len_k hL (by omega) F7.fld (m := 3) (by simp [lastIdx]) (by decide)
  subst e7
  -- S
  obtain ⟨Ls, H8, F8⟩ := rnext hL (by omega) F7 (X' := sS) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F7 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have cLs := var_len hL (by omega) F8 (by simp [lastIdx]) LsC
  have pLs := F8.fld.pos
  -- KT
  obtain ⟨L9, H9, F9⟩ := rnext hL (by omega) F8 (X' := sKT) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F8 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e9 := fld_len_k hL (by omega) F9.fld (m := 0) (by simp [lastIdx]) (by decide)
  subst e9
  -- PK
  obtain ⟨L10, H10, F10⟩ := rnext hL (by omega) F9 (X' := sPK) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F9 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have hP := hP hL
  obtain ⟨kt, ckt, hkt, e10⟩ : ∃ kt : Nat, tr.cell tt s RcptV3.kt = (kt : Fp) ∧ kt ≤ 1 ∧ L10 = 32 + 32 * kt := by
    have e := fld_len hL (by omega) F10.fld (e := .add (k 31) (smul 32 (c RcptV3.kt))) (by simp [lastIdx])
    have p10 := F10.fld.pos
    simp only [eval_add, eval_k, eval_smul, eval_c] at e
    rw [cst F10 ktC (L10 - 1) (by omega)] at e
    rcases isBool hL hs (x := RcptV3.kt) (by simp [boolCols]) with h | h
    · refine ⟨0, by rw [h]; rfl, by omega, ?_⟩
      rw [h, show ((31 : Nat) : Fp) + ((32 : Nat) : Fp) * 0 = ((31 : Nat) : Fp) by grind] at e
      have := ofNat_inj (a := L10 - 1) (b := 31) (by omega) (by decide) e
      omega
    · refine ⟨1, by rw [h]; rfl, by omega, ?_⟩
      rw [h, show ((31 : Nat) : Fp) + ((32 : Nat) : Fp) * 1 = ((63 : Nat) : Fp) by
        rw [show ((63 : Nat) : Fp) = ((31 + 32 * 1 : Nat) : Fp) from rfl, natCast_add, natCast_mul]; rfl] at e
      have := ofNat_inj (a := L10 - 1) (b := 63) (by omega) (by decide) e
      omega
  subst e10
  -- GP
  obtain ⟨L11, H11, F11⟩ := rnext hL (by omega) F10 (X' := sGP) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F10 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e11 := fld_len_k hL (by omega) F11.fld (m := 15) (by simp [lastIdx]) (by decide)
  subst e11
  -- TL
  obtain ⟨L12, H12, F12⟩ := rnext hL (by omega) F11 (X' := sTL) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F11 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e12 := fld_len_k hL (by omega) F12.fld (m := 12) (by simp [lastIdx]) (by decide)
  subst e12
  -- DEP
  obtain ⟨L13, H13, F13⟩ := rnext hL (by omega) F12 (X' := sDEP) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F12 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e13 := fld_len_k hL (by omega) F13.fld (m := 15) (by simp [lastIdx]) (by decide)
  subst e13
  -- XP0
  obtain ⟨L14, H14, F14⟩ := rnext hL (by omega) F13 (X' := sXP0) (g := k 1) (by simp [states]) (by simp [states])
    (by decide) (by decide) (end_rl0 hL (by omega) F13 (by simp [states]) (by decide) (by decide))
    (by simp [RcptV3.succ]) rfl
  have e14 := fld_len_k hL (by omega) F14.fld (m := 3) (by simp [lastIdx]) (by decide)
  subst e14
  have cv : ∀ {a b L X : Nat}, a = b → RFld tr tt s a L X → RFld tr tt s b L X := fun h F => h ▸ F
  refine ⟨Lp, Lv, Ls, kt, cLp, cLv, cLs, ckt, hkt, pLp, pLv, pLs, ?_, by simpa using F1, F2,
    cv (by omega) F3, cv (by omega) F4, cv (by omega) F5, cv (by omega) F6, cv (by omega) F7,
    cv (by omega) F8, cv (by omega) F9, cv (by omega) F10, cv (by unfold Vt; omega) F11,
    cv (by unfold Vt; omega) F12, cv (by unfold Vt; omega) F13, cv (by unfold Vt; omega) F14⟩
  unfold Vt; omega


end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- **Receipt layout.** -/
theorem layout_of {s : Nat} (hs : s < tr.height tt) (hrf : tr.cell tt s rf = 1) :
    ∃ h Lp Lv Ls kt, Layout tr tt s h Lp Lv Ls kt := by
  obtain ⟨Lp, Lv, Ls, kt, cLp, cLv, cLs, ckt, hkt, pLp, pLv, pLs, hH, F1, F2, F3, F4, F5, F6, F7, F8, F9,
    F10, F11, F12, F13, F14⟩ := prefix_of hL hs hrf
  have cv : ∀ {a b L X : Nat}, a = b → RFld tr tt s a L X → RFld tr tt s b L X := fun h F => h ▸ F
  generalize hV : Vt Lp Lv Ls kt = V at *
  have r14 := end_rl0 hL (by omega) F14 (by simp [states]) (by decide) (by decide)
  rcases isBool hL hs (x := RcptV3.hr) (by simp [boolCols]) with h0 | h1
  · -- no refund
    obtain ⟨L15, H15, F15⟩ := rnext hL (by omega) F14 (X' := sXG) (g := Dsl.not (c RcptV3.hr)) (by simp [states])
      (by simp [states]) (by decide) (by decide) r14 (by simp [RcptV3.succ])
      (by simp only [eval_not, eval_c]; rw [cst F14 hrC _ (by omega), h0]; grind)
    have e15 := fld_len_k hL (by omega) F15.fld (m := 7) (by simp [lastIdx]) (by decide)
    subst e15
    obtain ⟨L16, H16, F16⟩ := rnext hL (by omega) F15 (X' := sXST) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F15 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e16 := fld_len_k hL (by omega) F16.fld (m := 4) (by simp [lastIdx]) (by decide)
    subst e16
    obtain ⟨L17, H17, F17⟩ := rnext hL (by omega) F16 (X' := sXL0) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F16 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e17 := fld_len_k hL (by omega) F17.fld (m := 3) (by simp [lastIdx]) (by decide)
    subst e17
    obtain ⟨L18, H18, F18⟩ := rnext hL (by omega) F17 (X' := sXLH) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F17 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e18 := fld_len_k hL (by omega) F18.fld (m := 31) (by simp [lastIdx]) (by decide)
    subst e18
    have r18 := xlh_rl hL (by omega) F18
    rw [h0] at r18
    refine ⟨false, Lp, Lv, Ls, kt, ⟨fun f hf => ?_, by rw [h0]; rfl, cLp, cLv, cLs, ckt, hkt, ⟨pLp, pLv, pLs⟩,
      ?_, ?_⟩⟩
    · simp only [plan, hV, hN, Bool.false_eq_true, if_false, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · simpa using F1
      all_goals try assumption
      · exact cv (by dsimp only; omega) F15
      · exact cv (by dsimp only; omega) F16
      · exact cv (by dsimp only; omega) F17
      · exact cv (by dsimp only; omega) F18
    · simp only [total, hV, Bool.false_eq_true, if_false]
      rw [show s + (176 + V) - 1 = s + (123 + V) + 4 + 8 + 5 + 4 + (32 - 1) by omega]; rw [r18]; grind
    · simp only [total, hV, Bool.false_eq_true, if_false]; omega
  · -- refund
    obtain ⟨L15, H15, F15⟩ := rnext hL (by omega) F14 (X' := sXRI) (g := c RcptV3.hr) (by simp [states])
      (by simp [states]) (by decide) (by decide) r14 (by simp [RcptV3.succ])
      (by simp only [eval_c]; rw [cst F14 hrC _ (by omega), h1])
    have e15 := fld_len_k hL (by omega) F15.fld (m := 31) (by simp [lastIdx]) (by decide)
    subst e15
    obtain ⟨L16, H16, F16⟩ := rnext hL (by omega) F15 (X' := sXG) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F15 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e16 := fld_len_k hL (by omega) F16.fld (m := 7) (by simp [lastIdx]) (by decide)
    subst e16
    obtain ⟨L17, H17, F17⟩ := rnext hL (by omega) F16 (X' := sXST) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F16 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e17 := fld_len_k hL (by omega) F17.fld (m := 4) (by simp [lastIdx]) (by decide)
    subst e17
    obtain ⟨L18, H18, F18⟩ := rnext hL (by omega) F17 (X' := sXL0) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F17 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e18 := fld_len_k hL (by omega) F18.fld (m := 3) (by simp [lastIdx]) (by decide)
    subst e18
    obtain ⟨L19, H19, F19⟩ := rnext hL (by omega) F18 (X' := sXLH) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F18 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e19 := fld_len_k hL (by omega) F19.fld (m := 31) (by simp [lastIdx]) (by decide)
    subst e19
    have r19 := xlh_rl hL (by omega) F19
    rw [h1, show (1 : Fp) - 1 = 0 by grind] at r19
    obtain ⟨L20, H20, F20⟩ := rnext hL (by omega) F19 (X' := sXRH) (g := c RcptV3.hr) (by simp [states])
      (by simp [states]) (by decide) (by decide) r19 (by simp [RcptV3.succ])
      (by simp only [eval_c]; rw [cst F19 hrC _ (by omega), h1])
    have e20 := fld_len_k hL (by omega) F20.fld (m := 15) (by simp [lastIdx]) (by decide)
    subst e20
    obtain ⟨L21, H21, F21⟩ := rnext hL (by omega) F20 (X' := sXRF) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F20 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e21 := fld_len_k hL (by omega) F21.fld (m := 9) (by simp [lastIdx]) (by decide)
    subst e21
    obtain ⟨L22, H22, F22⟩ := rnext hL (by omega) F21 (X' := sXRZ) (g := k 1) (by simp [states])
      (by simp [states]) (by decide) (by decide)
      (end_rl0 hL (by omega) F21 (by simp [states]) (by decide) (by decide)) (by simp [RcptV3.succ]) rfl
    have e22 := fld_len_k hL (by omega) F22.fld (m := 15) (by simp [lastIdx]) (by decide)
    subst e22
    have r22 := xrz_rl hL (by omega) F22
    refine ⟨true, Lp, Lv, Ls, kt, ⟨fun f hf => ?_, by rw [h1]; rfl, cLp, cLv, cLs, ckt, hkt, ⟨pLp, pLv, pLs⟩,
      ?_, ?_⟩⟩
    · simp only [plan, hV, hN, if_true, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using F1
      all_goals try assumption
      · exact cv (by dsimp only; omega) F15
      · exact cv (by dsimp only; omega) F16
      · exact cv (by dsimp only; omega) F17
      · exact cv (by dsimp only; omega) F18
      · exact cv (by dsimp only; omega) F19
      · exact cv (by dsimp only; omega) F20
      · exact cv (by dsimp only; omega) F21
      · exact cv (by dsimp only; omega) F22
    · simp only [total, hV, if_true]
      rw [show s + (250 + V) - 1 = s + (123 + V) + 4 + 32 + 8 + 5 + 4 + 32 + 16 + 10 + (16 - 1) by omega]
      exact r22
    · simp only [total, hV, if_true]; omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
