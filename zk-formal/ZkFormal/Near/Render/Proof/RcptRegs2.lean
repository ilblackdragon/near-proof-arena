import ZkFormal.Near.Render.Proof.RcptRegs1
import ZkFormal.Near.Render.Proof.RcptGasB

/-!
# ZkFormal.Near.Render.Proof.RcptRegs2 — `cRegs` on the receipt rows

Loads, register head, shifts, the claim-only constraints (vanish), the tokens
register in `GP` rows (`rH`, `rI`, the new top byte is `tt % 256`) and kept
elsewhere (`rJ`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

section cells
variable {c : Claim} {e : Ext} {r s i : Nat}

theorem cF_st (st : Nat) (h1 : 5 ≤ st) (h2 : st ≤ 26) : cF c e (.seg r s i) st = if st = s then 1 else 0 := by
  simp only [cF, Cc_state h1 h2]; split <;> rfl

theorem cF_act : cF c e (.seg r s i) Rcpt.act = 1 := by simp only [cF, S_act]; rfl
theorem cF_sCL : cF c e (.seg r s i) Rcpt.sCL = 0 := by simp only [cF, S_sCL]; rfl
theorem cF_fs : cF c e (.seg r s i) Rcpt.fs = if i = 0 then 1 else 0 := by
  simp only [cF, S_fs]; by_cases h : i = 0 <;> simp [h, b2n] <;> rfl
theorem cF_fe : cF c e (.seg r s i) Rcpt.fe = if i + 1 = fLen (Df c e r) s then 1 else 0 := by
  simp only [cF, S_fe]; by_cases h : i + 1 = fLen (Df c e r) s <;> simp [h, b2n] <;> rfl
theorem cF_reg {j : Nat} (hj : j < 32) :
    cF c e (.seg r s i) (Rcpt.reg j) = Fp.ofNat ((fLd (Df c e r) (PA c e) s).getD (i + j) 0) := by
  simp only [cF, S_reg c e r s i hj]
theorem cF_tok {j : Nat} (hj : j < 16) : cF c e (.seg r s i) (Rcpt.tok j) = Fp.ofNat (segTok (Df c e r) s i j) := by
  simp only [cF, S_tok c e r s i hj]
theorem cF_sGP : cF c e (.seg r s i) Rcpt.sGP = if s = 15 then 1 else 0 := by
  rw [show Rcpt.sGP = 15 from rfl, cF_st 15 (by omega) (by omega)]; by_cases h : s = 15 <;> simp [h, Eq.comm]
theorem cF_lastR : cF c e (.seg r s i) Rcpt.lastR = Fp.ofNat (b2n (isRl (Df c e r) s i && (Df c e r).r + 1 == NN e)) := by
  simp only [cF, S_lastR]

end cells

theorem loads_range : Rcpt.loads.all (fun p => decide (5 ≤ p.1 ∧ p.1 ≤ 26)) = true := by decide
theorem regStates_range : Rcpt.regStates.all (fun p => decide (5 ≤ p ∧ p ≤ 26)) = true := by decide

/-- The register-head states are the ones whose byte is loaded. -/
theorem segByte_reg {d : RD} {pub : Array Nat} {s : Nat} (hs : s ∈ Rcpt.regStates) (i : Nat) :
    segByte d pub s i = (fLd d pub s).getD i 0 := by
  simp only [Rcpt.regStates, Rcpt.act, Rcpt.rf, Rcpt.rl, Rcpt.lastR, Rcpt.sCL, Rcpt.sPL, Rcpt.sP, Rcpt.sVL, Rcpt.sV, Rcpt.sRID, Rcpt.sT0, Rcpt.sSL, Rcpt.sS, Rcpt.sKT, Rcpt.sPK, Rcpt.sGP, Rcpt.sTL, Rcpt.sDEP, Rcpt.sXP0, Rcpt.sXRI, Rcpt.sXG, Rcpt.sXST, Rcpt.sXL0, Rcpt.sXLH, Rcpt.sXRH, Rcpt.sXRF, Rcpt.sXRZ, Rcpt.idx, Rcpt.fs, Rcpt.fe, Rcpt.b, Rcpt.e1Id, Rcpt.e1Pos, Rcpt.e1V, Rcpt.e1G, Rcpt.e2Id, Rcpt.e2Pos, Rcpt.e2V, Rcpt.e2G, Rcpt.e3Id, Rcpt.e3Pos, Rcpt.e3V, Rcpt.e3G, Rcpt.tA, Rcpt.symA, Rcpt.lastA, Rcpt.gKA, Rcpt.kz, Rcpt.r, Rcpt.o, Rcpt.o2, Rcpt.Lp, Rcpt.Lv, Rcpt.Ls, Rcpt.kt, Rcpt.hr, Rcpt.kslot, Rcpt.tprev, Rcpt.rcnt, Rcpt.ge, Rcpt.big, Rcpt.oEnd, Rcpt.o2End, Rcpt.reg, Rcpt.tok, Rcpt.h2, Rcpt.h3, Rcpt.h5, Rcpt.h6, Rcpt.h7, Rcpt.lb, Rcpt.z, Rcpt.linv, Rcpt.l210, Rcpt.hx6, Rcpt.acc, Rcpt.vc0, Rcpt.vc1, Rcpt.h01, Rcpt.p1, Rcpt.p2, Rcpt.p3, Rcpt.i1, Rcpt.i2, Rcpt.i3, Rcpt.isys, Rcpt.r1, Rcpt.lo8, Rcpt.lo4, Rcpt.xb, Rcpt.c1, Rcpt.c2, Rcpt.c3, Rcpt.c4, Rcpt.dl, Rcpt.burnt, Rcpt.ramt, Rcpt.sumD, Rcpt.invA, Rcpt.bef, Rcpt.lk, Rcpt.st, Rcpt.dsum, Rcpt.invB, Rcpt.dI, Rcpt.dL, Rcpt.gDg, Rcpt.width, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {c : WfClaim} {e : Ext} {r s i : Nat} {nx : Nat → Fp} {lst : Bool}

theorem rA_seg : ∀ x ∈ rA, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rA, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨st, l⟩, hl, ⟨y, j⟩, hy, rfl⟩ := hx
  have hst := List.all_eq_true.1 loads_range _ hl
  simp only [decide_eq_true_eq] at hst
  simp only [evR_mul3, evR_c, evR_sub, cF_st st hst.1 hst.2, cF_fs]
  by_cases h1 : st = s
  · subst h1
    by_cases h2 : i = 0
    · subst h2
      obtain ⟨hj, he⟩ := load_ok (c := c) (e := e) (r := r) (nx := nx) (fst := false) (lst := lst) hl hy
      rw [he, cF_reg hj, Nat.zero_add]; simp; grind
    · rw [if_neg h2]; grind
  · rw [if_neg h1]; grind

theorem rB_seg (hok : s ∈ fields (Df c.1 e r).hr) : ∀ x ∈ rB, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rB, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [evR_mul, evR_sub, evR_c, evR_sum_map]
  by_cases hs : s ∈ Rcpt.regStates
  · rw [cF_reg (by decide), Nat.add_zero]
    simp only [cF, S_b, segByte_reg hs]; grind
  · rw [sumC_zero]
    · grind
    · intro k hk
      have := List.all_eq_true.1 regStates_range _ hk
      simp only [decide_eq_true_eq] at this
      rw [cF_st k this.1 this.2, if_neg (fun h => hs (by subst h; exact hk))]

theorem rC_fe (hfe : i + 1 = fLen (Df c.1 e r) s) :
    ∀ x ∈ rC, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rC, List.mem_map, List.mem_range] at hx
  obtain ⟨j, -, rfl⟩ := hx
  simp only [evR_mul3, evR_not, evR_c, cF_fe, hfe, ↓reduceIte]; grind

theorem rC_in (_hin : i + 1 < fLen (Df c.1 e r) s) :
    ∀ x ∈ rC, evR (cF c.1 e (.seg r s i)) (cF c.1 e (.seg r s (i + 1))) false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rC, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, Rcpt.rowE, cF_reg (show j < 32 by omega),
    cF_reg (show j + 1 < 32 by omega), show i + 1 + j = i + (j + 1) by omega]
  grind

theorem first_zero {y : Expr} {cur : Nat → Fp} : evR cur nx false lst (publicOf c) (.mul .isFirst y) = 0 := by
  simp only [evR_mul, evR_isFirst, Bool.false_eq_true, ↓reduceIte]; grind

theorem rDE_seg : ∀ x ∈ rD ++ rE, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [List.mem_append, rD, rE, List.mem_map] at hx
  rcases hx with ⟨⟨y, j⟩, -, rfl⟩ | ⟨⟨y, j⟩, -, rfl⟩ <;> exact first_zero

theorem rot_seg {col : Nat → Nat} {len : Nat} :
    ∀ x ∈ Rcpt.rot col len, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [Rcpt.rot, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  simp only [evR_mul3, evR_c, cF_sCL]; grind

theorem rFG_seg : ∀ x ∈ rF ++ rG, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rF, List.mem_append] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  any_goals exact rot_seg x h
  simp only [rG, List.mem_map] at h
  obtain ⟨j, -, rfl⟩ := h
  simp only [evR_mul3, evR_c, cF_sCL]; grind

theorem rHI_ne (hs : s ≠ 15) : ∀ x ∈ rH ++ rI, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rH, rI, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨j, -, rfl⟩ | rfl <;> simp only [evR_mul, evR_c, cF_sGP, hs, ↓reduceIte] <;> grind

/-- Tokens register of the next row of a `GP` row. -/
def TokNx (d : RD) (i : Nat) (nx : Nat → Fp) : Prop := ∀ j, j < 16 → nx (Rcpt.tok j) = Fp.ofNat (segTok d 15 (i + 1) j)

theorem rH_gp (_hi : i < 16) (hn : TokNx (Df c.1 e r) i nx) :
    ∀ x ∈ rH, evR (cF c.1 e (.seg r 15 i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rH, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp only [evR_mul, evR_sub, evR_c, evR_n, hn j (by omega), cF_tok (show j + 1 < 16 by omega)]
  simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
    show i + 1 + j = i + (j + 1) by omega]
  grind

theorem rI_gp (hB : c.1.blockGasPrice < 256 ^ 16) (hg : Good c.1 e) (hr : r < NN e) (hi : i < 16)
    (hn : TokNx (Df c.1 e r) i nx) :
    ∀ x ∈ rI, evR (cF c.1 e (.seg r 15 i)) nx false lst (publicOf c) x = 0 := by
  have G := gasOk hg hr hB
  intro x hx
  simp only [rI, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [evR_mul, evR_sub, evR_n, hn 15 (by omega)]
  rw [evR_bitsX (v := fun j => segXb (Df c.1 e r) (BG c.1) 15 i j) 31 8 (fun j h1 h2 => by
    simp only [cF]; rw [S_xb c.1 e r 15 i (by omega)])]
  rw [bitsVal_pool (x := Seg.tt (Df c.1 e r) (BG c.1) i % 256) (fun j hj => by
    simp only [segXb, ↓reduceIte]; simp (disch := omega) only [if_neg, if_pos]; congr 1; omega)
    (Nat.mod_lt _ (by decide)), tt_mod G hi]
  simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
    show ¬ (i + 1 + 15 < 16) by omega, show i + 1 + 15 - 16 = i by omega]
  grind

end

end RcptP

end ZkFormal.Near.Render
