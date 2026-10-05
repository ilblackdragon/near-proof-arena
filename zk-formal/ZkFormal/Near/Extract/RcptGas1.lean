import ZkFormal.Near.Extract.RcptCount
import ZkFormal.Near.Extract.RcptChain

/-!
# ZkFormal.Near.Extract.RcptGas1 — the `GP` rows: comparison with the block gas price

Row `k` of the `GP` field holds `gp_k`, the block gas price byte `bgp_k`
(register), the difference byte `D_k` and the borrow; the borrow chain gives
`gp + 2^128·(1 − ge) = bgp + D`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- Row `k` of the `GP` field. -/
def gq (s Lp Lv Ls kt k : Nat) : Nat := s + (78 + Vt Lp Lv Ls kt) + k

def bvN (tr : Trace Fp) (q off len : Nat) : Nat := bitsVal (fun j => cv tr T_RCPT q (xb j)) off len

theorem cast_cv (tr : Trace Fp) (q x : Nat) : tr.cell T_RCPT q x = ((cv tr T_RCPT q x : Nat) : Fp) :=
  cell_eq_cast tr T_RCPT q x

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
include lay

theorem gp_fld : RFld tr s (s + (78 + Vt Lp Lv Ls kt)) 16 sGP ∧ s + (78 + Vt Lp Lv Ls kt) + 16 < tr.height T_RCPT := by
  have hm : (sGP, 78 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have := lay.fin
  have := total_pos h Lp Lv Ls kt
  exact ⟨lay.flds _ hm, by simp only at hle; omega⟩

theorem gp_row (k : Nat) (hk : k < 16) :
    gq s Lp Lv Ls kt k < tr.height T_RCPT ∧ tr.cell T_RCPT (gq s Lp Lv Ls kt k) sGP = 1 ∧
    tr.cell T_RCPT (gq s Lp Lv Ls kt k) fs = (if k = 0 then 1 else 0) ∧
    tr.cell T_RCPT (gq s Lp Lv Ls kt k) fe = (if k = 15 then 1 else 0) ∧
    tr.cell T_RCPT (gq s Lp Lv Ls kt k) ge = tr.cell T_RCPT s ge ∧
    tr.cell T_RCPT (gq s Lp Lv Ls kt k) Rcpt.hr = tr.cell T_RCPT s Rcpt.hr ∧
    tr.cell T_RCPT (gq s Lp Lv Ls kt k) (reg 0) = pub.getD (PV_BGP + k) 0 := by
  obtain ⟨F, hH⟩ := gp_fld hL lay
  have hq : gq s Lp Lv Ls kt k < tr.height T_RCPT := by unfold gq; omega
  simp only [gq] at hq ⊢
  refine ⟨hq, F.fld.st k hk, F.fld.fs k hk, by rw [F.fld.fe k hk]; simp, F.consts k hk ge (by simp [rconsts]),
    F.consts k hk _ hrC, ?_⟩
  rw [fld_reg hL (by omega) F.fld (by simp [states]) (by decide) k hk 0 (by omega), Nat.zero_add]
  have h1 : tr.cell T_RCPT (s + (78 + Vt Lp Lv Ls kt)) sGP = 1 := by simpa using F.fld.st 0 (by omega)
  have hfs : tr.cell T_RCPT (s + (78 + Vt Lp Lv Ls kt)) fs = 1 := by simpa using F.fld.fs 0 (by omega)
  rw [reg_load hL (by omega) (X := sGP) (l := pubs PV_BGP 16) (by simp [loads]) h1 hfs k (by simp [pubs]; omega)]
  simp [pubs]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem nat_of_fp {a b : Nat} (ha : a < P) (hb : b < P) (h : ((a : Nat) : Fp) = ((b : Nat) : Fp)) : a = b :=
  ofNat_inj ha hb h

theorem pP : (2 ^ 20 : Nat) < P := by decide

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
include lay

theorem ge_bool : cv tr T_RCPT s ge ≤ 1 := by
  have := lay.fin; have := total_pos h Lp Lv Ls kt
  exact cv_bool (isBool hL (by omega) (by simp [boolCols]))

/-- **The borrow chain of `gp − bgp`.** -/
theorem gp_borrow (hgp : ∀ k, k < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt k) b < 256)
    (hbg : ∀ k, k < 16 → pubNat pub (PV_BGP + k) < 256) :
    sumL (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b) 16 + 256 ^ 16 * (1 - cv tr T_RCPT s ge) =
      sumL (fun k => pubNat pub (PV_BGP + k)) 16 + sumL (fun k => bvN tr (gq s Lp Lv Ls kt k) 0 8) 16 := by
  have R := gp_row hL lay
  have hgeb := ge_bool hL lay
  -- the carry links
  have c2 : cv tr T_RCPT (gq s Lp Lv Ls kt 0) c1 = 0 := by
    obtain ⟨hq, h1, hfs, -⟩ := R 0 (by omega)
    have c := con hL hq (e := .mul (.mul gp (c fs)) (c c1)) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul, eval_c] at c
    rw [h1, hfs, if_pos rfl] at c
    have e : tr.cell T_RCPT (gq s Lp Lv Ls kt 0) c1 = 0 := by grind
    unfold cv; rw [e]; rfl
  have c3 : ∀ k, k + 1 < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt (k + 1)) c1 = cv tr T_RCPT (gq s Lp Lv Ls kt k) (xb 8) := by
    intro k hk
    obtain ⟨hq, h1, -, hfe, -⟩ := R k (by omega)
    have hq1 := (R (k + 1) hk).1
    have c := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n c1) (c (xb 8)))) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n,
      nxt (show gq s Lp Lv Ls kt k + 1 < tr.height T_RCPT by unfold gq at *; omega)] at c
    rw [h1, hfe, if_neg (by omega)] at c
    have e : tr.cell T_RCPT (gq s Lp Lv Ls kt k + 1) c1 = tr.cell T_RCPT (gq s Lp Lv Ls kt k) (xb 8) := by grind
    rw [show gq s Lp Lv Ls kt k + 1 = gq s Lp Lv Ls kt (k + 1) by unfold gq; omega] at e
    simp [cv, e]
  have c4 : cv tr T_RCPT (gq s Lp Lv Ls kt 15) (xb 8) = 1 - cv tr T_RCPT s ge := by
    obtain ⟨hq, h1, -, hfe, hge, -⟩ := R 15 (by omega)
    have c := con hL hq (e := mul3 gp (c fe) (sub (c (xb 8)) (Dsl.not (c ge)))) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub] at c
    rw [h1, hfe, if_pos rfl, hge, cast_cv tr s ge] at c
    have e : tr.cell T_RCPT (gq s Lp Lv Ls kt 15) (xb 8) = ((1 - cv tr T_RCPT s ge : Nat) : Fp) := by
      rcases Nat.lt_or_ge (cv tr T_RCPT s ge) 1 with h0 | h0
      · rw [show cv tr T_RCPT s ge = 0 by omega] at c ⊢; simp at c ⊢; grind
      · rw [show cv tr T_RCPT s ge = 1 by omega] at c ⊢; simp at c ⊢; grind
    rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
  have bB : ∀ k, k < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt k) (xb 8) ≤ 1 := fun k hk =>
    cv_bool (xb_bool hL (R k hk).1 8 (by omega))
  have bc : ∀ k, k < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt k) c1 ≤ 1 := by
    intro k hk
    cases k with
    | zero => rw [c2]; omega
    | succ k => rw [c3 k hk]; exact bB k (by omega)
  -- the rows
  have hrow : ∀ k, k < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt k) b + 256 * cv tr T_RCPT (gq s Lp Lv Ls kt k) (xb 8) =
      (pubNat pub (PV_BGP + k) + bvN tr (gq s Lp Lv Ls kt k) 0 8) + cv tr T_RCPT (gq s Lp Lv Ls kt k) c1 := by
    intro k hk
    obtain ⟨hq, h1, -, -, -, -, hbg'⟩ := R k hk
    have cc := con hL hq (e := .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))))
      (mem_gs (by simp [cGas]))
    obtain ⟨be, bl⟩ := bitsX_eval hL hq 0 8 (by omega)
    have be' : (bitsX 0 8).eval tr T_RCPT (gq s Lp Lv Ls kt k) pub = ((bvN tr (gq s Lp Lv Ls kt k) 0 8 : Nat) : Fp) := be
    have bl' : bvN tr (gq s Lp Lv Ls kt k) 0 8 < 256 := bl
    simp only [gp, DE, eval_mul, eval_c, eval_sub, eval_add, eval_smul] at cc
    rw [h1, hbg', cast_cv tr _ b, cast_cv tr _ c1, cast_cv tr _ (xb 8), pub_eq_cast, be'] at cc
    have hg := hgp k hk; have hb := hbg k hk; have := bB k hk; have := bc k hk
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    rw [natCast_add, natCast_add, natCast_add, natCast_mul]; grind
  have hc := chain 16 (by omega) (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b)
    (fun k => pubNat pub (PV_BGP + k) + bvN tr (gq s Lp Lv Ls kt k) 0 8)
    (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) c1) (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) (xb 8)) hrow c2 c3
  simp only [show 16 - 1 = 15 from rfl] at hc
  rw [c4, sumL_add] at hc
  exact hc

end ZkFormal.Near.RcptProof
