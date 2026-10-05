import ZkFormal.Near.Render.Proof.RcptCells

/-!
# ZkFormal.Near.Render.Proof.RcptCol — the cells of the honest `rcpt` rows, column by column

`Cc c e (.seg r s i) X` and `Cc c e (.cl i) X` for every column `X` but the
emission slots (generated; one lemma per column or column family).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

set_option maxHeartbeats 400000

theorem b2n_true : b2n true = 1 := rfl
theorem b2n_false : b2n false = 0 := rfl

section
variable (c : Claim) (e : Ext) (r s i : Nat)

theorem S_act : Cc c e (.seg r s i) Rcpt.act = 1 := by
  simp only [Rcpt.act]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_rf : Cc c e (.seg r s i) Rcpt.rf = b2n (decide (s = 5 ∧ i = 0)) := by
  simp only [Rcpt.rf]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_rl : Cc c e (.seg r s i) Rcpt.rl = b2n (isRl (Df c e r) s i) := by
  simp only [Rcpt.rl]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_lastR : Cc c e (.seg r s i) Rcpt.lastR = b2n (isRl (Df c e r) s i && (Df c e r).r + 1 == NN e) := by
  simp only [Rcpt.lastR]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sCL : Cc c e (.seg r s i) Rcpt.sCL = 0 := by
  simp only [Rcpt.sCL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sPL : Cc c e (.seg r s i) Rcpt.sPL = if 5 = s then 1 else 0 := by
  simp only [Rcpt.sPL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sP : Cc c e (.seg r s i) Rcpt.sP = if 6 = s then 1 else 0 := by
  simp only [Rcpt.sP]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sVL : Cc c e (.seg r s i) Rcpt.sVL = if 7 = s then 1 else 0 := by
  simp only [Rcpt.sVL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sV : Cc c e (.seg r s i) Rcpt.sV = if 8 = s then 1 else 0 := by
  simp only [Rcpt.sV]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sRID : Cc c e (.seg r s i) Rcpt.sRID = if 9 = s then 1 else 0 := by
  simp only [Rcpt.sRID]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sT0 : Cc c e (.seg r s i) Rcpt.sT0 = if 10 = s then 1 else 0 := by
  simp only [Rcpt.sT0]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sSL : Cc c e (.seg r s i) Rcpt.sSL = if 11 = s then 1 else 0 := by
  simp only [Rcpt.sSL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sS : Cc c e (.seg r s i) Rcpt.sS = if 12 = s then 1 else 0 := by
  simp only [Rcpt.sS]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sKT : Cc c e (.seg r s i) Rcpt.sKT = if 13 = s then 1 else 0 := by
  simp only [Rcpt.sKT]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sPK : Cc c e (.seg r s i) Rcpt.sPK = if 14 = s then 1 else 0 := by
  simp only [Rcpt.sPK]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sGP : Cc c e (.seg r s i) Rcpt.sGP = if 15 = s then 1 else 0 := by
  simp only [Rcpt.sGP]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sTL : Cc c e (.seg r s i) Rcpt.sTL = if 16 = s then 1 else 0 := by
  simp only [Rcpt.sTL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sDEP : Cc c e (.seg r s i) Rcpt.sDEP = if 17 = s then 1 else 0 := by
  simp only [Rcpt.sDEP]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXP0 : Cc c e (.seg r s i) Rcpt.sXP0 = if 18 = s then 1 else 0 := by
  simp only [Rcpt.sXP0]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXRI : Cc c e (.seg r s i) Rcpt.sXRI = if 19 = s then 1 else 0 := by
  simp only [Rcpt.sXRI]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXG : Cc c e (.seg r s i) Rcpt.sXG = if 20 = s then 1 else 0 := by
  simp only [Rcpt.sXG]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXST : Cc c e (.seg r s i) Rcpt.sXST = if 21 = s then 1 else 0 := by
  simp only [Rcpt.sXST]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXL0 : Cc c e (.seg r s i) Rcpt.sXL0 = if 22 = s then 1 else 0 := by
  simp only [Rcpt.sXL0]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXLH : Cc c e (.seg r s i) Rcpt.sXLH = if 23 = s then 1 else 0 := by
  simp only [Rcpt.sXLH]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXRH : Cc c e (.seg r s i) Rcpt.sXRH = if 24 = s then 1 else 0 := by
  simp only [Rcpt.sXRH]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXRF : Cc c e (.seg r s i) Rcpt.sXRF = if 25 = s then 1 else 0 := by
  simp only [Rcpt.sXRF]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sXRZ : Cc c e (.seg r s i) Rcpt.sXRZ = if 26 = s then 1 else 0 := by
  simp only [Rcpt.sXRZ]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_idx : Cc c e (.seg r s i) Rcpt.idx = i := by
  simp only [Rcpt.idx]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_fs : Cc c e (.seg r s i) Rcpt.fs = b2n (decide (i = 0)) := by
  simp only [Rcpt.fs]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_fe : Cc c e (.seg r s i) Rcpt.fe = b2n (decide (i + 1 = (fLen (Df c e r) s))) := by
  simp only [Rcpt.fe]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_b : Cc c e (.seg r s i) Rcpt.b = (segByte (Df c e r) (PA c e) s i) := by
  simp only [Rcpt.b]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_tA : Cc c e (.seg r s i) Rcpt.tA = if s = 8 then 2 + 2 * i else if s = 7 ∧ i < 2 then i else if s = 9 ∧ i = 0 then 2 + 2 * (Df c e r).recv.length else 0 := by
  simp only [Rcpt.tA]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_symA : Cc c e (.seg r s i) Rcpt.symA = if s = 8 then (segByte (Df c e r) (PA c e) s i) / 16 else if s = 9 ∧ i = 0 then SYM_END else 0 := by
  simp only [Rcpt.symA]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_lastA : Cc c e (.seg r s i) Rcpt.lastA = b2n (decide (s = 9 ∧ i = 0)) := by
  simp only [Rcpt.lastA]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_gKA : Cc c e (.seg r s i) Rcpt.gKA = b2n (decide (s = 8 ∨ (s = 7 ∧ i < 2) ∨ (s = 9 ∧ i = 0))) := by
  simp only [Rcpt.gKA]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_kz : Cc c e (.seg r s i) Rcpt.kz = b2n (decide (s = 7 ∧ i < 2)) := by
  simp only [Rcpt.kz]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_r : Cc c e (.seg r s i) Rcpt.r = (Df c e r).r := by
  simp only [Rcpt.r]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_o : Cc c e (.seg r s i) Rcpt.o = (Df c e r).o := by
  simp only [Rcpt.o]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_o2 : Cc c e (.seg r s i) Rcpt.o2 = (Df c e r).o2 := by
  simp only [Rcpt.o2]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_Lp : Cc c e (.seg r s i) Rcpt.Lp = (Df c e r).pred.length := by
  simp only [Rcpt.Lp]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_Lv : Cc c e (.seg r s i) Rcpt.Lv = (Df c e r).recv.length := by
  simp only [Rcpt.Lv]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_Ls : Cc c e (.seg r s i) Rcpt.Ls = (Df c e r).signer.length := by
  simp only [Rcpt.Ls]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_kt : Cc c e (.seg r s i) Rcpt.kt = (Df c e r).kt := by
  simp only [Rcpt.kt]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_hr : Cc c e (.seg r s i) Rcpt.hr = b2n (Df c e r).hr := by
  simp only [Rcpt.hr]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_kslot : Cc c e (.seg r s i) Rcpt.kslot = (Df c e r).kslot := by
  simp only [Rcpt.kslot]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_tprev : Cc c e (.seg r s i) Rcpt.tprev = (Df c e r).tprev := by
  simp only [Rcpt.tprev]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_rcnt : Cc c e (.seg r s i) Rcpt.rcnt = (Df c e r).rcnt := by
  simp only [Rcpt.rcnt]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_ge : Cc c e (.seg r s i) Rcpt.ge = b2n (Df c e r).ge := by
  simp only [Rcpt.ge]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_big : Cc c e (.seg r s i) Rcpt.big = b2n (Df c e r).big := by
  simp only [Rcpt.big]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_oEnd : Cc c e (.seg r s i) Rcpt.oEnd = oEndOf (Df c e r) := by
  simp only [Rcpt.oEnd]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_o2End : Cc c e (.seg r s i) Rcpt.o2End = o2EndOf (Df c e r) := by
  simp only [Rcpt.o2End]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h2 : Cc c e (.seg r s i) Rcpt.h2 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 111 else 0 := by
  simp only [Rcpt.h2]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h3 : Cc c e (.seg r s i) Rcpt.h3 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 112 else 0 := by
  simp only [Rcpt.h3]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h5 : Cc c e (.seg r s i) Rcpt.h5 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 113 else 0 := by
  simp only [Rcpt.h5]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h6 : Cc c e (.seg r s i) Rcpt.h6 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 114 else 0 := by
  simp only [Rcpt.h6]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h7 : Cc c e (.seg r s i) Rcpt.h7 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 115 else 0 := by
  simp only [Rcpt.h7]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_z : Cc c e (.seg r s i) Rcpt.z = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 120 else 0 := by
  simp only [Rcpt.z]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_linv : Cc c e (.seg r s i) Rcpt.linv = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 121 else 0 := by
  simp only [Rcpt.linv]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_l210 : Cc c e (.seg r s i) Rcpt.l210 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 122 else 0 := by
  simp only [Rcpt.l210]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_hx6 : Cc c e (.seg r s i) Rcpt.hx6 = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) 123 else 0 := by
  simp only [Rcpt.hx6]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_acc : Cc c e (.seg r s i) Rcpt.acc = if s = 6 then accP (Df c e r) i % P else if s = 8 then accV (Df c e r) i else 0 := by
  simp only [Rcpt.acc]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_vc0 : Cc c e (.seg r s i) Rcpt.vc0 = if s = 8 then (Df c e r).recv.getD 0 0 else 0 := by
  simp only [Rcpt.vc0]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_vc1 : Cc c e (.seg r s i) Rcpt.vc1 = if s = 8 then (Df c e r).recv.getD 1 0 else 0 := by
  simp only [Rcpt.vc1]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_h01 : Cc c e (.seg r s i) Rcpt.h01 = if s = 8 then h01V (Df c e r) else 0 := by
  simp only [Rcpt.h01]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_p1 : Cc c e (.seg r s i) Rcpt.p1 = if s = 6 ∧ i + 1 = (fLen (Df c e r) s) then pP (Df c e r) else if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then pV1 (Df c e r) else 0 := by
  simp only [Rcpt.p1]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_p2 : Cc c e (.seg r s i) Rcpt.p2 = if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then pV2 (Df c e r) else 0 := by
  simp only [Rcpt.p2]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_p3 : Cc c e (.seg r s i) Rcpt.p3 = if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then pV3 (Df c e r) else 0 := by
  simp only [Rcpt.p3]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_i1 : Cc c e (.seg r s i) Rcpt.i1 = if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then invP (pV1 (Df c e r)) else 0 := by
  simp only [Rcpt.i1]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_i2 : Cc c e (.seg r s i) Rcpt.i2 = if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then invP (pV2 (Df c e r)) else 0 := by
  simp only [Rcpt.i2]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_i3 : Cc c e (.seg r s i) Rcpt.i3 = if s = 8 ∧ i + 1 = (fLen (Df c e r) s) then invP (pV3 (Df c e r)) else 0 := by
  simp only [Rcpt.i3]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_isys : Cc c e (.seg r s i) Rcpt.isys = if s = 6 ∧ i + 1 = (fLen (Df c e r) s) then invP (pP (Df c e r)) else 0 := by
  simp only [Rcpt.isys]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_r1 : Cc c e (.seg r s i) Rcpt.r1 = b2n (decide (s = 17 ∧ i = 1)) := by
  simp only [Rcpt.r1]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_lo8 : Cc c e (.seg r s i) Rcpt.lo8 = 0 := by
  simp only [Rcpt.lo8]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_lo4 : Cc c e (.seg r s i) Rcpt.lo4 = 0 := by
  simp only [Rcpt.lo4]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_c1 : Cc c e (.seg r s i) Rcpt.c1 = if s = 15 then Seg.gbr (Df c e r) (BG c) i else if s = 17 then chain (Seg.y1 (Df c e r)) i else 0 := by
  simp only [Rcpt.c1]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_c2 : Cc c e (.seg r s i) Rcpt.c2 = if s = 15 then chain (Seg.x2 (Df c e r) (BG c)) i else if s = 17 then chain (Seg.y2 (Df c e r)) i else 0 := by
  simp only [Rcpt.c2]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_c3 : Cc c e (.seg r s i) Rcpt.c3 = if s = 15 then chain (Seg.x3 (Df c e r) (BG c)) i else if s = 17 then chain (Seg.y3 (Df c e r)) i else 0 := by
  simp only [Rcpt.c3]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_c4 : Cc c e (.seg r s i) Rcpt.c4 = if s = 15 then chain (Seg.x4 (Df c e r) (BG c)) i else if s = 17 then Seg.dbr (Df c e r) i else 0 := by
  simp only [Rcpt.c4]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_burnt : Cc c e (.seg r s i) Rcpt.burnt = if s = 15 then Seg.sb (Df c e r) (BG c) i % 256 else 0 := by
  simp only [Rcpt.burnt]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_ramt : Cc c e (.seg r s i) Rcpt.ramt = if s = 15 then Seg.sr (Df c e r) (BG c) i % 256 else 0 := by
  simp only [Rcpt.ramt]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_sumD : Cc c e (.seg r s i) Rcpt.sumD = if s = 15 then runSum (Seg.gdv (Df c e r) (BG c)) i else 0 := by
  simp only [Rcpt.sumD]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_invA : Cc c e (.seg r s i) Rcpt.invA = if s = 15 then (if i + 1 = (fLen (Df c e r) s) ∧ (Df c e r).hr = true then invP (runSum (Seg.gdv (Df c e r) (BG c)) i) else 0) else 0 := by
  simp only [Rcpt.invA]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_bef : Cc c e (.seg r s i) Rcpt.bef = if s = 15 then 0 else if s = 17 then Seg.befB (Df c e r) i else 0 := by
  simp only [Rcpt.bef]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_lk : Cc c e (.seg r s i) Rcpt.lk = if s = 15 then 0 else if s = 17 then Seg.lkB (Df c e r) i else 0 := by
  simp only [Rcpt.lk]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_st : Cc c e (.seg r s i) Rcpt.st = if s = 15 then 0 else if s = 17 then Seg.stB (Df c e r) i else 0 := by
  simp only [Rcpt.st]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_dsum : Cc c e (.seg r s i) Rcpt.dsum = if s = 15 then 0 else if s = 17 then Seg.runA (Df c e r) i else 0 := by
  simp only [Rcpt.dsum]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_invB : Cc c e (.seg r s i) Rcpt.invB = if s = 15 then 0 else if s = 17 then (if i + 1 = (fLen (Df c e r) s) then invP (Seg.runA (Df c e r) i) else 0) else 0 := by
  simp only [Rcpt.invB]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_dI : Cc c e (.seg r s i) Rcpt.dI = if s = 15 then 0 else if s = 17 then 0 else if i = 0 ∧ s = 19 then msgId K_RID (Df c e r).r else if i = 0 ∧ s = 23 then msgId K_PEO (Df c e r).r else 0 := by
  simp only [Rcpt.dI]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_dL : Cc c e (.seg r s i) Rcpt.dL = if s = 15 then 0 else if s = 17 then 0 else if i = 0 ∧ s = 19 then 48 else if i = 0 ∧ s = 23 then (Df c e r).peoLen else 0 := by
  simp only [Rcpt.dL]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_gDg : Cc c e (.seg r s i) Rcpt.gDg = if s = 15 then 0 else if s = 17 then 0 else b2n (decide (i = 0 ∧ (s = 19 ∨ s = 23))) := by
  simp only [Rcpt.gDg]; rw [Cc_seg _ _ _ _ _ _ (by decide)]; simp only [segCell, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self]

theorem S_reg {j : Nat} (hj : j < 32) : Cc c e (.seg r s i) (Rcpt.reg j) = (fLd (Df c e r) (PA c e) s).getD (i + j) 0 := by
  simp only [Rcpt.reg]; rw [Cc_seg _ _ _ _ _ _ (by omega)]; simp (disch := omega) only [segCell, if_neg, if_pos, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self, Nat.add_sub_cancel_left]

theorem S_tok {j : Nat} (hj : j < 16) : Cc c e (.seg r s i) (Rcpt.tok j) = segTok (Df c e r) s i j := by
  simp only [Rcpt.tok]; rw [Cc_seg _ _ _ _ _ _ (by omega)]; simp (disch := omega) only [segCell, if_neg, if_pos, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self, Nat.add_sub_cancel_left]

theorem S_xb {j : Nat} (hj : j < 66) : Cc c e (.seg r s i) (Rcpt.xb j) = segXb (Df c e r) (BG c) s i j := by
  simp only [Rcpt.xb]; rw [Cc_seg _ _ _ _ _ _ (by omega)]; simp (disch := omega) only [segCell, if_neg, if_pos, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self, Nat.add_sub_cancel_left]

theorem S_lb {j : Nat} (hj : j < 4) : Cc c e (.seg r s i) (Rcpt.lb j) = if isStr s then charCell (segByte (Df c e r) (PA c e) s i) (116 + j) else 0 := by
  simp only [Rcpt.lb]; rw [Cc_seg _ _ _ _ _ _ (by omega)]; simp (disch := omega) only [segCell, if_neg, if_pos, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self, Nat.add_sub_cancel_left]

theorem S_dl {j : Nat} (hj : j < 8) : Cc c e (.seg r s i) (Rcpt.dl j) = if s = 15 then (if 208 + j < 212 then (if j < i then Seg.pB (Df c e r) (BG c) (i - 1 - j) else 0) else (if 208 + j - 212 < i then Seg.surB (Df c e r) (BG c) (i - 1 - (208 + j - 212)) else 0)) else if s = 17 then (if 208 + j < 215 then (if j < i then Seg.stB (Df c e r) (i - 1 - j) else 0) else 0) else 0 := by
  simp only [Rcpt.dl]; rw [Cc_seg _ _ _ _ _ _ (by omega)]; simp (disch := omega) only [segCell, if_neg, if_pos, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ite_self, Nat.add_sub_cancel_left]

end

section
variable (c : Claim) (e : Ext) (i : Nat)

theorem L_act : Cc c e (.cl i) Rcpt.act = 1 := by
  simp only [Rcpt.act]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sCL : Cc c e (.cl i) Rcpt.sCL = 1 := by
  simp only [Rcpt.sCL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sPL : Cc c e (.cl i) Rcpt.sPL = 0 := by
  simp only [Rcpt.sPL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sP : Cc c e (.cl i) Rcpt.sP = 0 := by
  simp only [Rcpt.sP]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sVL : Cc c e (.cl i) Rcpt.sVL = 0 := by
  simp only [Rcpt.sVL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sV : Cc c e (.cl i) Rcpt.sV = 0 := by
  simp only [Rcpt.sV]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sRID : Cc c e (.cl i) Rcpt.sRID = 0 := by
  simp only [Rcpt.sRID]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sT0 : Cc c e (.cl i) Rcpt.sT0 = 0 := by
  simp only [Rcpt.sT0]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sSL : Cc c e (.cl i) Rcpt.sSL = 0 := by
  simp only [Rcpt.sSL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sS : Cc c e (.cl i) Rcpt.sS = 0 := by
  simp only [Rcpt.sS]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sKT : Cc c e (.cl i) Rcpt.sKT = 0 := by
  simp only [Rcpt.sKT]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sPK : Cc c e (.cl i) Rcpt.sPK = 0 := by
  simp only [Rcpt.sPK]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sGP : Cc c e (.cl i) Rcpt.sGP = 0 := by
  simp only [Rcpt.sGP]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sTL : Cc c e (.cl i) Rcpt.sTL = 0 := by
  simp only [Rcpt.sTL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sDEP : Cc c e (.cl i) Rcpt.sDEP = 0 := by
  simp only [Rcpt.sDEP]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXP0 : Cc c e (.cl i) Rcpt.sXP0 = 0 := by
  simp only [Rcpt.sXP0]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXRI : Cc c e (.cl i) Rcpt.sXRI = 0 := by
  simp only [Rcpt.sXRI]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXG : Cc c e (.cl i) Rcpt.sXG = 0 := by
  simp only [Rcpt.sXG]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXST : Cc c e (.cl i) Rcpt.sXST = 0 := by
  simp only [Rcpt.sXST]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXL0 : Cc c e (.cl i) Rcpt.sXL0 = 0 := by
  simp only [Rcpt.sXL0]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXLH : Cc c e (.cl i) Rcpt.sXLH = 0 := by
  simp only [Rcpt.sXLH]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXRH : Cc c e (.cl i) Rcpt.sXRH = 0 := by
  simp only [Rcpt.sXRH]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXRF : Cc c e (.cl i) Rcpt.sXRF = 0 := by
  simp only [Rcpt.sXRF]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sXRZ : Cc c e (.cl i) Rcpt.sXRZ = 0 := by
  simp only [Rcpt.sXRZ]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_rf : Cc c e (.cl i) Rcpt.rf = 0 := by
  simp only [Rcpt.rf]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_rl : Cc c e (.cl i) Rcpt.rl = 0 := by
  simp only [Rcpt.rl]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_lastR : Cc c e (.cl i) Rcpt.lastR = 0 := by
  simp only [Rcpt.lastR]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_idx : Cc c e (.cl i) Rcpt.idx = i := by
  simp only [Rcpt.idx]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_fs : Cc c e (.cl i) Rcpt.fs = b2n (decide (i = 0)) := by
  simp only [Rcpt.fs]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_fe : Cc c e (.cl i) Rcpt.fe = b2n (decide (i = 11)) := by
  simp only [Rcpt.fe]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_b : Cc c e (.cl i) Rcpt.b = 0 := by
  simp only [Rcpt.b]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_tA : Cc c e (.cl i) Rcpt.tA = 0 := by
  simp only [Rcpt.tA]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_symA : Cc c e (.cl i) Rcpt.symA = 0 := by
  simp only [Rcpt.symA]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_lastA : Cc c e (.cl i) Rcpt.lastA = 0 := by
  simp only [Rcpt.lastA]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_gKA : Cc c e (.cl i) Rcpt.gKA = 0 := by
  simp only [Rcpt.gKA]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_kz : Cc c e (.cl i) Rcpt.kz = 0 := by
  simp only [Rcpt.kz]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_r : Cc c e (.cl i) Rcpt.r = 0 := by
  simp only [Rcpt.r]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_o : Cc c e (.cl i) Rcpt.o = 0 := by
  simp only [Rcpt.o]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_o2 : Cc c e (.cl i) Rcpt.o2 = 0 := by
  simp only [Rcpt.o2]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_Lp : Cc c e (.cl i) Rcpt.Lp = 0 := by
  simp only [Rcpt.Lp]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_Lv : Cc c e (.cl i) Rcpt.Lv = 0 := by
  simp only [Rcpt.Lv]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_Ls : Cc c e (.cl i) Rcpt.Ls = 0 := by
  simp only [Rcpt.Ls]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_kt : Cc c e (.cl i) Rcpt.kt = 0 := by
  simp only [Rcpt.kt]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_hr : Cc c e (.cl i) Rcpt.hr = 0 := by
  simp only [Rcpt.hr]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_kslot : Cc c e (.cl i) Rcpt.kslot = 0 := by
  simp only [Rcpt.kslot]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_tprev : Cc c e (.cl i) Rcpt.tprev = 0 := by
  simp only [Rcpt.tprev]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_rcnt : Cc c e (.cl i) Rcpt.rcnt = 0 := by
  simp only [Rcpt.rcnt]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_ge : Cc c e (.cl i) Rcpt.ge = 0 := by
  simp only [Rcpt.ge]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_big : Cc c e (.cl i) Rcpt.big = 0 := by
  simp only [Rcpt.big]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_oEnd : Cc c e (.cl i) Rcpt.oEnd = 0 := by
  simp only [Rcpt.oEnd]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_o2End : Cc c e (.cl i) Rcpt.o2End = 0 := by
  simp only [Rcpt.o2End]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h2 : Cc c e (.cl i) Rcpt.h2 = 0 := by
  simp only [Rcpt.h2]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h3 : Cc c e (.cl i) Rcpt.h3 = 0 := by
  simp only [Rcpt.h3]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h5 : Cc c e (.cl i) Rcpt.h5 = 0 := by
  simp only [Rcpt.h5]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h6 : Cc c e (.cl i) Rcpt.h6 = 0 := by
  simp only [Rcpt.h6]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h7 : Cc c e (.cl i) Rcpt.h7 = 0 := by
  simp only [Rcpt.h7]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_z : Cc c e (.cl i) Rcpt.z = 0 := by
  simp only [Rcpt.z]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_linv : Cc c e (.cl i) Rcpt.linv = 0 := by
  simp only [Rcpt.linv]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_l210 : Cc c e (.cl i) Rcpt.l210 = 0 := by
  simp only [Rcpt.l210]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_hx6 : Cc c e (.cl i) Rcpt.hx6 = 0 := by
  simp only [Rcpt.hx6]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_acc : Cc c e (.cl i) Rcpt.acc = 0 := by
  simp only [Rcpt.acc]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_vc0 : Cc c e (.cl i) Rcpt.vc0 = 0 := by
  simp only [Rcpt.vc0]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_vc1 : Cc c e (.cl i) Rcpt.vc1 = 0 := by
  simp only [Rcpt.vc1]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_h01 : Cc c e (.cl i) Rcpt.h01 = 0 := by
  simp only [Rcpt.h01]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_p1 : Cc c e (.cl i) Rcpt.p1 = 0 := by
  simp only [Rcpt.p1]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_p2 : Cc c e (.cl i) Rcpt.p2 = 0 := by
  simp only [Rcpt.p2]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_p3 : Cc c e (.cl i) Rcpt.p3 = 0 := by
  simp only [Rcpt.p3]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_i1 : Cc c e (.cl i) Rcpt.i1 = 0 := by
  simp only [Rcpt.i1]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_i2 : Cc c e (.cl i) Rcpt.i2 = 0 := by
  simp only [Rcpt.i2]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_i3 : Cc c e (.cl i) Rcpt.i3 = 0 := by
  simp only [Rcpt.i3]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_isys : Cc c e (.cl i) Rcpt.isys = 0 := by
  simp only [Rcpt.isys]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_r1 : Cc c e (.cl i) Rcpt.r1 = 0 := by
  simp only [Rcpt.r1]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_c4 : Cc c e (.cl i) Rcpt.c4 = 0 := by
  simp only [Rcpt.c4]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_burnt : Cc c e (.cl i) Rcpt.burnt = 0 := by
  simp only [Rcpt.burnt]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_ramt : Cc c e (.cl i) Rcpt.ramt = 0 := by
  simp only [Rcpt.ramt]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_sumD : Cc c e (.cl i) Rcpt.sumD = 0 := by
  simp only [Rcpt.sumD]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_bef : Cc c e (.cl i) Rcpt.bef = 0 := by
  simp only [Rcpt.bef]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_lk : Cc c e (.cl i) Rcpt.lk = 0 := by
  simp only [Rcpt.lk]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_st : Cc c e (.cl i) Rcpt.st = 0 := by
  simp only [Rcpt.st]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_dsum : Cc c e (.cl i) Rcpt.dsum = 0 := by
  simp only [Rcpt.dsum]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_invB : Cc c e (.cl i) Rcpt.invB = 0 := by
  simp only [Rcpt.invB]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_dI : Cc c e (.cl i) Rcpt.dI = 0 := by
  simp only [Rcpt.dI]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_dL : Cc c e (.cl i) Rcpt.dL = 0 := by
  simp only [Rcpt.dL]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_gDg : Cc c e (.cl i) Rcpt.gDg = 0 := by
  simp only [Rcpt.gDg]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_lo8 : Cc c e (.cl i) Rcpt.lo8 = b2n (decide (i < 8)) := by
  simp only [Rcpt.lo8]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_lo4 : Cc c e (.cl i) Rcpt.lo4 = b2n (decide (i < 4)) := by
  simp only [Rcpt.lo4]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_invA : Cc c e (.cl i) Rcpt.invA = if i = 0 then invP ((PA c e).getD PV_N 0 + (PA c e).getD (PV_N + 1) 0) else 0 := by
  simp only [Rcpt.invA]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_c1 : Cc c e (.cl i) Rcpt.c1 = if i < 8 then chain (Cl.x1 (PA c e)) i else 0 := by
  simp only [Rcpt.c1]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_c2 : Cc c e (.cl i) Rcpt.c2 = if i < 8 then Cl.br (PA c e) i else 0 := by
  simp only [Rcpt.c2]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

theorem L_c3 : Cc c e (.cl i) Rcpt.c3 = if i < 8 then chain (Cl.x3 (PA c e)) i else 0 := by
  simp only [Rcpt.c3]; rw [Cc_cl _ _ _ _ (by decide)]; simp only [clCell, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte, ite_self, and_false, false_and, and_true, true_and]

end

end RcptP

end ZkFormal.Near.Render
