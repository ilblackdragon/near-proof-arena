import ZkFormal.NearV3.Assembly.RcptCandidateRegs
-- Original GasCompare.lean SHA256: 06050ea565a71d00b75cc96da16e1e3e0ece09ccb52ac4e25082c7afe52241ae.
-- Table-local premise and constraint membership migrated to arithmetic candidate.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptPrevious
import ZkFormal.Near.Extract.RcptChain

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.GasCompare — the `GP` rows: comparison with the block gas price

Row `k` of the `GP` field holds `gp_k`, the block gas price byte `bgp_k`
(register), the difference byte `D_k` and the borrow; the borrow chain gives
`gp + 2^128·(1 − ge) = bgp + D`.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain sumL_add)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Row `k` of the `GP` field. -/
def gq (s Lp Lv Ls kt k : Nat) : Nat := s + (78 + Vt Lp Lv Ls kt) + k

def bvN (tr : Trace Fp) (tt q off len : Nat) : Nat := bitsVal (fun j => cv tr tt q (xb j)) off len

theorem cast_cv (tr : Trace Fp) (tt q x : Nat) : tr.cell tt q x = ((cv tr tt q x : Nat) : Fp) :=
  cell_eq_cast tr tt q x

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem xb_bool {q : Nat} (hq : q<tr.height tt) (j : Nat) (hj : j<66) :
    tr.cell tt q (xb j)=0 ∨ tr.cell tt q (xb j)=1 := by
  apply isBool hL hq
  have hm : xb j∈(List.range 66).map xb := List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  simp only [boolCols,List.mem_append]
  exact Or.inl (Or.inr hm)

variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem gp_fld : RFld tr tt s (s + (78 + Vt Lp Lv Ls kt)) 16 sGP ∧ s + (78 + Vt Lp Lv Ls kt) + 16 < tr.height tt := by
  have hm : (sGP, 78 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have := lay.fin
  have := total_pos h Lp Lv Ls kt
  exact ⟨lay.flds _ hm, by simp only at hle; omega⟩

theorem gp_row (k : Nat) (hk : k < 16) :
    gq s Lp Lv Ls kt k < tr.height tt ∧ tr.cell tt (gq s Lp Lv Ls kt k) sGP = 1 ∧
    tr.cell tt (gq s Lp Lv Ls kt k) fs = (if k = 0 then 1 else 0) ∧
    tr.cell tt (gq s Lp Lv Ls kt k) fe = (if k = 15 then 1 else 0) ∧
    tr.cell tt (gq s Lp Lv Ls kt k) ge = tr.cell tt s ge ∧
    tr.cell tt (gq s Lp Lv Ls kt k) RcptV3.hr = tr.cell tt s RcptV3.hr ∧
    tr.cell tt (gq s Lp Lv Ls kt k) (reg 0) = pub.getD (PH_GP + k) 0 := by
  obtain ⟨F, hH⟩ := gp_fld hL lay
  have hq : gq s Lp Lv Ls kt k < tr.height tt := by unfold gq; omega
  simp only [gq] at hq ⊢
  refine ⟨hq, F.fld.st k hk, F.fld.fs k hk, by rw [F.fld.fe k hk]; simp, F.consts k hk ge (by simp [rconsts]),
    F.consts k hk _ hrC, ?_⟩
  rw [fld_reg hL (by omega) F.fld (by simp [states]) (by decide) k hk 0 (by omega), Nat.zero_add]
  have h1 : tr.cell tt (s + (78 + Vt Lp Lv Ls kt)) sGP = 1 := by simpa using F.fld.st 0 (by omega)
  have hfs : tr.cell tt (s + (78 + Vt Lp Lv Ls kt)) fs = 1 := by simpa using F.fld.fs 0 (by omega)
  rw [reg_load hL (by omega) (X := sGP) (l := pubs PH_GP 16) (by simp [loads]) h1 hfs k (by simp [pubs]; omega)]
  simp [pubs]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain sumL_add)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem nat_of_fp {a b : Nat} (ha : a < P) (hb : b < P) (h : ((a : Nat) : Fp) = ((b : Nat) : Fp)) : a = b :=
  ofNat_inj ha hb h

theorem pub_eq_cast (pub : List Fp) (i : Nat) : pub.getD i 0 = ((pubNat pub i : Nat) : Fp) := by
  simp [pubNat,natCast_eq,fpN]

theorem pP : (2 ^ 20 : Nat) < P := by decide

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem ge_bool : cv tr tt s ge ≤ 1 := by
  have := lay.fin; have := total_pos h Lp Lv Ls kt
  exact cv_bool (isBool hL (by omega) (by simp [boolCols]))

/-- **The borrow chain of `gp − bgp`.** -/
theorem gp_borrow (hgp : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) b < 256)
    (hbg : ∀ k, k < 16 → pubNat pub (PH_GP + k) < 256) :
    sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) b) 16 + 256 ^ 16 * (1 - cv tr tt s ge) =
      sumL (fun k => pubNat pub (PH_GP + k)) 16 + sumL (fun k => bvN tr tt (gq s Lp Lv Ls kt k) 0 8) 16 := by
  have R := gp_row hL lay
  have hgeb := ge_bool hL lay
  -- the carry links
  have c2 : cv tr tt (gq s Lp Lv Ls kt 0) c1 = 0 := by
    obtain ⟨hq, h1, hfs, -⟩ := R 0 (by omega)
    have c := con hL hq (e := .mul (.mul gp (c fs)) (c c1)) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    simp only [gp, eval_mul, eval_c] at c
    rw [h1, hfs, if_pos rfl] at c
    have e : tr.cell tt (gq s Lp Lv Ls kt 0) c1 = 0 := by grind
    unfold cv; rw [e]; rfl
  have c3 : ∀ k, k + 1 < 16 → cv tr tt (gq s Lp Lv Ls kt (k + 1)) c1 = cv tr tt (gq s Lp Lv Ls kt k) (xb 8) := by
    intro k hk
    obtain ⟨hq, h1, -, hfe, -⟩ := R k (by omega)
    have hq1 := (R (k + 1) hk).1
    have c := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n c1) (c (xb 8)))) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n,
      nxt (show gq s Lp Lv Ls kt k + 1 < tr.height tt by unfold gq at *; omega)] at c
    rw [h1, hfe, if_neg (by omega)] at c
    have e : tr.cell tt (gq s Lp Lv Ls kt k + 1) c1 = tr.cell tt (gq s Lp Lv Ls kt k) (xb 8) := by grind
    rw [show gq s Lp Lv Ls kt k + 1 = gq s Lp Lv Ls kt (k + 1) by unfold gq; omega] at e
    simp [cv, e]
  have c4 : cv tr tt (gq s Lp Lv Ls kt 15) (xb 8) = 1 - cv tr tt s ge := by
    obtain ⟨hq, h1, -, hfe, hge, -⟩ := R 15 (by omega)
    have c := con hL hq (e := mul3 gp (c fe) (sub (c (xb 8)) (Dsl.not (c ge)))) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub] at c
    rw [h1, hfe, if_pos rfl, hge, cast_cv tr tt s ge] at c
    have e : tr.cell tt (gq s Lp Lv Ls kt 15) (xb 8) = ((1 - cv tr tt s ge : Nat) : Fp) := by
      rcases Nat.lt_or_ge (cv tr tt s ge) 1 with h0 | h0
      · rw [show cv tr tt s ge = 0 by omega] at c ⊢; simp at c ⊢; grind
      · rw [show cv tr tt s ge = 1 by omega] at c ⊢; simp at c ⊢; grind
    rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
  have bB : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) (xb 8) ≤ 1 := fun k hk =>
    cv_bool (xb_bool hL (R k hk).1 8 (by omega))
  have bc : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) c1 ≤ 1 := by
    intro k hk
    cases k with
    | zero => rw [c2]; omega
    | succ k => rw [c3 k hk]; exact bB k (by omega)
  -- the rows
  have hrow : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) b + 256 * cv tr tt (gq s Lp Lv Ls kt k) (xb 8) =
      (pubNat pub (PH_GP + k) + bvN tr tt (gq s Lp Lv Ls kt k) 0 8) + cv tr tt (gq s Lp Lv Ls kt k) c1 := by
    intro k hk
    obtain ⟨hq, h1, -, -, -, -, hbg'⟩ := R k hk
    have cc := con hL hq (e := .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))))
      (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    obtain ⟨be, bl⟩ := bitsX_eval hL hq 0 8 (by omega)
    have be' : (bitsX 0 8).eval tr tt (gq s Lp Lv Ls kt k) pub = ((bvN tr tt (gq s Lp Lv Ls kt k) 0 8 : Nat) : Fp) := be
    have bl' : bvN tr tt (gq s Lp Lv Ls kt k) 0 8 < 256 := bl
    simp only [gp, DE, eval_mul, eval_c, eval_sub, eval_add, eval_smul] at cc
    rw [h1, hbg', cast_cv tr tt _ b, cast_cv tr tt _ c1, cast_cv tr tt _ (xb 8), pub_eq_cast, be'] at cc
    have hg := hgp k hk; have hb := hbg k hk; have := bB k hk; have := bc k hk
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    rw [natCast_add, natCast_add, natCast_add, natCast_mul]; grind
  have hc := chain 16 (by omega) (fun k => cv tr tt (gq s Lp Lv Ls kt k) b)
    (fun k => pubNat pub (PH_GP + k) + bvN tr tt (gq s Lp Lv Ls kt k) 0 8)
    (fun k => cv tr tt (gq s Lp Lv Ls kt k) c1) (fun k => cv tr tt (gq s Lp Lv Ls kt k) (xb 8)) hrow c2 c3
  simp only [show 16 - 1 = 15 from rfl] at hc
  rw [c4, sumL_add] at hc
  exact hc

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
