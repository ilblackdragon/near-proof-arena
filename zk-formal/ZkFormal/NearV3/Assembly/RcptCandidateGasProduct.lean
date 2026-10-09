import ZkFormal.NearV3.Assembly.RcptCandidateGasCompare
import ZkFormal.NearV3.Assembly.RcptCandidateGasSound
-- GasProduct source SHA256: e03aa62370cbf028aa9352c3c8d6ab5cfc48b9b40350efb5d5abf791507eedc4.
-- Candidate table, masked native surplus, and gate-derived proof migration.
import ZkFormal.NearV3.Rcpt.Extract.V.GasCompare

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.GasProduct — `GP` rows: effective price, surplus, delay lines, `burnt = G·pc`, `ramt = G·sur`

`pc_k = sys ? 0 : (ge ? bgp_k : gp_k)`, `sur_k = ge ? D_k : 0`; the delay lines hold the
previous four values; the convolutions with `G_LE` and the 11-bit carries give
`burnt = G·pc` and `ramt = G·sur` (no overflow: `ovf` kills `p_12..15`).
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- `G·x` convolution value at position `k` (bytes of `G` LSB first). -/
def convN (f : Nat → Nat) (k : Nat) : Nat :=
  196 * f k + 164 * (if 0 < k then f (k - 1) else 0) + 183 * (if 1 < k then f (k - 2) else 0) +
    246 * (if 2 < k then f (k - 3) else 0) + 51 * (if 3 < k then f (k - 4) else 0)

theorem convN_sum (f : Nat → Nat) (h12 : f 12 = 0) (h13 : f 13 = 0) (h14 : f 14 = 0) (h15 : f 15 = 0) :
    sumL (convN f) 16 = NearSpec.Params.G * sumL f 16 := by
  simp only [sumL, convN, NearSpec.Params.G, NearSpec.Params.newActionReceiptExec, NearSpec.Params.transferExec]
  simp only [Nat.lt_irrefl, Nat.not_lt_zero, ite_false, ite_true, show (0:Nat) < 1 by decide]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.reduceSub, Nat.reducePow]
  omega

def PN (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s Lp Lv Ls kt k : Nat) : Nat :=
  if cv tr tt s RcptV3.sys = 1 then 0 else if cv tr tt s ge = 1 then pubNat pub (PH_GP + k) else cv tr tt (gq s Lp Lv Ls kt k) b
def SN (tr : Trace Fp) (tt : Nat) (s Lp Lv Ls kt k : Nat) : Nat :=
  if cv tr tt s RcptV3.sys = 1 then 0 else if cv tr tt s ge = 1 then bvN tr tt (gq s Lp Lv Ls kt k) 0 8 else 0

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem ge_cases : (tr.cell tt s ge = 0 ∧ cv tr tt s ge = 0) ∨ (tr.cell tt s ge = 1 ∧ cv tr tt s ge = 1) := by
  have := lay.fin; have := total_pos h Lp Lv Ls kt
  rcases isBool hL (r := s) (by omega) (x := ge) (by simp [boolCols]) with e | e
  · exact Or.inl ⟨e, by simp [cv, e, Fp.toNat_zero]⟩
  · exact Or.inr ⟨e, by simp [cv, e, Fp.toNat_one]⟩

theorem pE_eval (k : Nat) (hk : k < 16) :
    tr.cell tt (gq s Lp Lv Ls kt k) pc = ((PN tr tt pub s Lp Lv Ls kt k : Nat) : Fp) ∧
    systemSurplus.eval tr tt (gq s Lp Lv Ls kt k) pub = ((SN tr tt s Lp Lv Ls kt k : Nat) : Fp) := by
  obtain ⟨hq,h1,_,_,hge,_,hbg⟩ := gp_row hL lay k hk
  obtain ⟨be,_⟩ := bitsX_eval hL hq 0 8 (by omega)
  have be' : (bitsX 0 8).eval tr tt (gq s Lp Lv Ls kt k) pub = ((bvN tr tt (gq s Lp Lv Ls kt k) 0 8:Nat):Fp) := be
  have F := (gp_fld hL lay).1
  have hsys : tr.cell tt (gq s Lp Lv Ls kt k) RcptV3.sys=tr.cell tt s RcptV3.sys := F.consts k hk _ (by simp [rconsts])
  have cc := con hL hq (e:=.mul gp (sub (c pc) (.mul (Dsl.not (c RcptV3.sys)) pE))) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
  simp only [gp,pE,eval_mul,eval_sub,eval_add,eval_not,eval_c,h1,hsys,hge,hbg] at cc
  have hs0 : s<tr.height tt := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  have hsc := cvb (isBool hL hs0 (x:=RcptV3.sys) (by simp [boolCols]))
  have hot := oneHot hL hq (show sGP∈states by simp [states]) h1
  have hcl := hot.2 sCL (by simp [states]) (by decide)
  have hgq := gas_gate hL hq (by simp only [rowE,eval_sub,eval_mul,eval_c,eval_not,hot.1,hcl];grind)
  simp only [systemSurplus,DE,eval_c,eval_mul,PN,SN,hgq,hge,hsys,be']
  rcases hsc with ⟨s0,n0⟩|⟨s1,n1⟩ <;>
  rcases ge_cases hL lay with ⟨e0,m0⟩|⟨e1,m1⟩
  all_goals simp_all only [ite_true,ite_false,show ¬ ((0:Nat)=1) by decide,cast_cv tr tt _ b,pub_eq_cast] <;> grind

/-- **Delay lines.** -/
theorem dl_eval : ∀ k, k < 16 → ∀ j, j < 4 →
    tr.cell tt (gq s Lp Lv Ls kt k) (dl j) = ((if j < k then PN tr tt pub s Lp Lv Ls kt (k - 1 - j) else 0 : Nat) : Fp) ∧
    tr.cell tt (gq s Lp Lv Ls kt k) (dl (4 + j)) =
      ((if j < k then SN tr tt s Lp Lv Ls kt (k - 1 - j) else 0 : Nat) : Fp) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    obtain ⟨hq, h1, hfs, -⟩ := gp_row hL lay 0 (by omega)
    have z : ∀ i, i < 8 → tr.cell tt (gq s Lp Lv Ls kt 0) (dl i) = 0 := by
      intro i hi
      have cc := con hL hq (e := mul3 gp (c fs) (c (dl i))) (mem_gs (by
        unfold systemGasConstraints gasConstraintsWith; simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))
      simp only [gp, eval_mul3, eval_c] at cc
      rw [h1, hfs, if_pos rfl] at cc; grind
    rw [z j (by omega), z (4 + j) (by omega)]; simp; rfl
  | succ k ih =>
    intro hk j hj
    obtain ⟨hq, h1, -, hfe, -⟩ := gp_row hL lay k (by omega)
    have hn : gq s Lp Lv Ls kt k + 1 < tr.height tt := by have := (gp_row hL lay (k + 1) hk).1; unfold gq at *; omega
    have e1 : gq s Lp Lv Ls kt (k + 1) = gq s Lp Lv Ls kt k + 1 := by unfold gq; omega
    obtain ⟨pe, se⟩ := pE_eval hL lay k (by omega)
    rw [e1]
    cases j with
    | zero =>
      have c0 := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n (dl 0)) (c pc))) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
      have c4 := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n (dl 4)) systemSurplus)) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
      simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at c0 c4
      rw [h1, hfe, if_neg (by omega), pe] at c0
      rw [h1, hfe, if_neg (by omega), se] at c4
      refine ⟨?_, ?_⟩
      · rw [if_pos (by omega), show k + 1 - 1 - 0 = k by omega]; grind
      · rw [if_pos (by omega), show k + 1 - 1 - 0 = k by omega]; simp only [Nat.add_zero]; grind
    | succ j =>
      have pj := ih (by omega) j (by omega)
      have mA : (j + 1) ∈ [1, 2, 3, 5, 6, 7] := by simp; omega
      have mB : (4 + (j + 1)) ∈ [1, 2, 3, 5, 6, 7] := by simp; omega
      have cA := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n (dl (j + 1))) (c (dl (j + 1 - 1))))) (mem_gs (by
        unfold systemGasConstraints gasConstraintsWith; simp only [List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨j + 1, mA, rfl⟩)))
      have cB := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n (dl (4 + (j + 1)))) (c (dl (4 + (j + 1) - 1)))))
        (mem_gs (by
          unfold systemGasConstraints gasConstraintsWith; simp only [List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨4 + (j + 1), mB, rfl⟩)))
      simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cA cB
      rw [h1, hfe, if_neg (by omega)] at cA cB
      rw [show j + 1 - 1 = j by omega] at cA
      rw [show 4 + (j + 1) - 1 = 4 + j by omega] at cB
      refine ⟨?_, ?_⟩
      · have : tr.cell tt (gq s Lp Lv Ls kt k + 1) (dl (j + 1)) = tr.cell tt (gq s Lp Lv Ls kt k) (dl j) := by
          grind
        rw [this, pj.1]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega), show k + 1 - 1 - (j + 1) = k - 1 - j by omega]
        · rw [if_neg hjk, if_neg (by omega)]
      · have : tr.cell tt (gq s Lp Lv Ls kt k + 1) (dl (4 + (j + 1))) =
            tr.cell tt (gq s Lp Lv Ls kt k) (dl (4 + j)) := by grind
        rw [this, pj.2]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega), show k + 1 - 1 - (j + 1) = k - 1 - j by omega]
        · rw [if_neg hjk, if_neg (by omega)]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem conv_chain (v C cin X : Nat → Nat) (hrow : ∀ k, k < 16 → v k + 256 * C k = convN X k + cin k)
    (h0 : cin 0 = 0) (hlink : ∀ k, k + 1 < 16 → cin (k + 1) = C k) (hC : C 15 = 0)
    (h12 : X 12 = 0) (h13 : X 13 = 0) (h14 : X 14 = 0) (h15 : X 15 = 0) :
    sumL v 16 = NearSpec.Params.G * sumL X 16 := by
  have := chain 16 (by omega) v (convN X) cin C hrow h0 hlink
  simp only [show 16 - 1 = 15 from rfl, hC, Nat.mul_zero, Nat.add_zero] at this
  rw [this, convN_sum X h12 h13 h14 h15]

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem conv_evals (k : Nat) (hk : k < 16) :
    (conv (G_LE.take 5) (c pc) (fun j => c (dl j))).eval tr tt (gq s Lp Lv Ls kt k) pub =
      ((convN (PN tr tt pub s Lp Lv Ls kt) k : Nat) : Fp) ∧
    (conv (G_LE.take 5) systemSurplus (fun j => c (dl (4 + j)))).eval tr tt (gq s Lp Lv Ls kt k) pub =
      ((convN (SN tr tt s Lp Lv Ls kt) k : Nat) : Fp) := by
  obtain ⟨pe, se⟩ := pE_eval hL lay k hk
  have d0 := dl_eval hL lay k hk 0 (by omega)
  have d1 := dl_eval hL lay k hk 1 (by omega)
  have d2 := dl_eval hL lay k hk 2 (by omega)
  have d3 := dl_eval hL lay k hk 3 (by omega)
  simp only [conv, G_LE, List.take, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    eval_sum_cons, eval_sum_nil, eval_smul, eval_c, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd,
    show ¬ (1 = 0) by decide, show ¬ (2 = 0) by decide, show ¬ (3 = 0) by decide, show ¬ (4 = 0) by decide]
  rw [pe, se, d0.1, d1.1, d2.1, d3.1, d0.2, d1.2, d2.2, d3.2]
  simp only [convN, Nat.sub_zero, Nat.sub_sub, Nat.reduceAdd]
  constructor <;> (simp only [natCast_add, natCast_mul]; grind)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem cv_zero_of {q x : Nat} (h0 : tr.cell tt q x = 0) : cv tr tt q x = 0 := by
  unfold cv; rw [h0]; rfl

/-- Generic convolution field (`burnt`/`c2`/`9` or `ramt`/`c3`/`20`). -/
theorem gp_conv (vcol ccol off : Nat) (X : Nat → Nat) (xE : Expr) (dd : Nat → Expr)
    (hoff : off + 11 ≤ 66)
    (hrowE : Expr.mul gp (sub (.add (c vcol) (smul 256 (bitsX off 11))) (.add (conv (G_LE.take 5) xE dd) (c ccol)))
      ∈ receiptArithmeticCandidate.constraints)
    (h0E : Expr.mul (.mul gp (c fs)) (c ccol) ∈ receiptArithmeticCandidate.constraints)
    (hlE : mul3 gp (Dsl.not (c fe)) (sub (n ccol) (bitsX off 11)) ∈ receiptArithmeticCandidate.constraints)
    (hfE : mul3 gp (c fe) (bitsX off 11) ∈ receiptArithmeticCandidate.constraints)
    (hoE : mul3 gp (c fe) (ovf xE dd) ∈ receiptArithmeticCandidate.constraints)
    (hconv : ∀ k, k < 16 → (conv (G_LE.take 5) xE dd).eval tr tt (gq s Lp Lv Ls kt k) pub =
      ((convN X k : Nat) : Fp))
    (hx : xE.eval tr tt (gq s Lp Lv Ls kt 15) pub = ((X 15 : Nat) : Fp))
    (hd : ∀ j, j < 3 → (dd j).eval tr tt (gq s Lp Lv Ls kt 15) pub = ((X (14 - j) : Nat) : Fp))
    (hX : ∀ k, k < 16 → X k < 256) (hv : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) vcol < 256) :
    sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) vcol) 16 = NearSpec.Params.G * sumL X 16 := by
  have R := gp_row hL lay
  have Cb : ∀ k, k < 16 → bvN tr tt (gq s Lp Lv Ls kt k) off 11 < 2048 := fun k hk =>
    (bitsX_eval hL (R k hk).1 off 11 hoff).2
  have Ce : ∀ k, k < 16 → (bitsX off 11).eval tr tt (gq s Lp Lv Ls kt k) pub =
      ((bvN tr tt (gq s Lp Lv Ls kt k) off 11 : Nat) : Fp) := fun k hk => (bitsX_eval hL (R k hk).1 off 11 hoff).1
  have c0 : cv tr tt (gq s Lp Lv Ls kt 0) ccol = 0 := by
    obtain ⟨hq, h1, hfs, -⟩ := R 0 (by omega)
    have cc := con hL hq h0E
    simp only [gp, eval_mul, eval_c] at cc
    rw [h1, hfs, if_pos rfl] at cc
    exact cv_zero_of hL lay (by grind)
  have cl : ∀ k, k + 1 < 16 → cv tr tt (gq s Lp Lv Ls kt (k + 1)) ccol = bvN tr tt (gq s Lp Lv Ls kt k) off 11 := by
    intro k hk
    obtain ⟨hq, h1, -, hfe, -⟩ := R k (by omega)
    have hn : gq s Lp Lv Ls kt k + 1 < tr.height tt := by have := (R (k + 1) hk).1; unfold gq at *; omega
    have cc := con hL hq hlE
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
    rw [h1, hfe, if_neg (by omega), Ce k (by omega)] at cc
    have e : tr.cell tt (gq s Lp Lv Ls kt (k + 1)) ccol = ((bvN tr tt (gq s Lp Lv Ls kt k) off 11 : Nat) : Fp) := by
      rw [show gq s Lp Lv Ls kt (k + 1) = gq s Lp Lv Ls kt k + 1 by unfold gq; omega]; grind
    rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (by have := Cb k (by omega); unfold P; omega)]
  have cb : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) ccol < 2048 := by
    intro k hk; cases k with
    | zero => rw [c0]; omega
    | succ k => rw [cl k hk]; exact Cb k (by omega)
  obtain ⟨hq15, h115, -, hfe15, -⟩ := R 15 (by omega)
  have cf : bvN tr tt (gq s Lp Lv Ls kt 15) off 11 = 0 := by
    have cc := con hL hq15 hfE
    simp only [gp, eval_mul3, eval_c] at cc
    rw [h115, hfe15, if_pos rfl, Ce 15 (by omega)] at cc
    exact nat_of_fp (by have := Cb 15 (by omega); unfold P; omega) (by unfold P; omega) (by grind)
  have co := con hL hq15 hoE
  simp only [gp, ovf, eval_mul3, eval_c, eval_sum_cons, eval_sum_nil, eval_smul] at co
  rw [h115, hfe15, if_pos rfl, hx, hd 0 (by omega), hd 1 (by omega), hd 2 (by omega)] at co
  have ovf0 : (164 + 183 + 246 + 51) * X 15 + (183 + 246 + 51) * X 14 + (246 + 51) * X 13 + 51 * X 12 = 0 := by
    have := hX 15 (by omega); have := hX 14 (by omega); have := hX 13 (by omega); have := hX 12 (by omega)
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  refine conv_chain _ (fun k => bvN tr tt (gq s Lp Lv Ls kt k) off 11) (fun k => cv tr tt (gq s Lp Lv Ls kt k) ccol) X
    (fun k hk => ?_) c0 cl cf (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hq, h1, -⟩ := R k hk
  have cc := con hL hq hrowE
  simp only [gp, eval_mul, eval_c, eval_sub, eval_add, eval_smul] at cc
  rw [h1, Ce k hk, hconv k hk, cast_cv tr tt _ vcol, cast_cv tr tt _ ccol] at cc
  have := hv k hk; have := Cb k hk; have := cb k hk
  have hcv : convN X k ≤ 255 * 840 := by
    have h0 := hX k hk
    unfold convN
    have a1 : (if 0 < k then X (k - 1) else 0) ≤ 255 := by split <;> (try exact Nat.le_of_lt_succ (hX _ (by omega))) <;> omega
    have a2 : (if 1 < k then X (k - 2) else 0) ≤ 255 := by split <;> (try exact Nat.le_of_lt_succ (hX _ (by omega))) <;> omega
    have a3 : (if 2 < k then X (k - 3) else 0) ≤ 255 := by split <;> (try exact Nat.le_of_lt_succ (hX _ (by omega))) <;> omega
    have a4 : (if 3 < k then X (k - 4) else 0) ≤ 255 := by split <;> (try exact Nat.le_of_lt_succ (hX _ (by omega))) <;> omega
    omega
  apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
  simp only [natCast_add, natCast_mul]; grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem PN_lt (hgp : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) b < 256)
    (hbg : ∀ k, k < 16 → pubNat pub (PH_GP + k) < 256) : ∀ k, k < 16 → PN tr tt pub s Lp Lv Ls kt k < 256 := by
  intro k hk; unfold PN; split
  · omega
  · split
    · exact hbg k hk
    · exact hgp k hk

theorem SN_lt : ∀ k, k < 16 → SN tr tt s Lp Lv Ls kt k < 256 := by
  intro k hk; unfold SN; split
  · omega
  · split
    · exact (bitsX_eval hL (gp_row hL lay k hk).1 0 8 (by omega)).2
    · omega

/-- **`burnt = G·pc`.** -/
theorem gp_burnt (hgp : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) b < 256)
    (hbg : ∀ k, k < 16 → pubNat pub (PH_GP + k) < 256)
    (hbu : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) burnt < 256) :
    sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) burnt) 16 =
      NearSpec.Params.G * sumL (PN tr tt pub s Lp Lv Ls kt) 16 :=
  gp_conv hL lay burnt c2 9 _ (c pc) (fun j => c (dl j)) (by omega) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    (fun k hk => (conv_evals hL lay k hk).1) (pE_eval hL lay 15 (by omega)).1
    (fun j hj => by
      simp only [eval_c]; rw [(dl_eval hL lay 15 (by omega) j (by omega)).1, if_pos (by omega)])
    (PN_lt hL lay hgp hbg) hbu

/-- **`ramt = G·sur`.** -/
theorem gp_ramt (hra : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) ramt < 256) :
    sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) ramt) 16 =
      NearSpec.Params.G * sumL (SN tr tt s Lp Lv Ls kt) 16 :=
  gp_conv hL lay ramt c3 20 _ systemSurplus (fun j => c (dl (4 + j))) (by omega) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith])) (mem_gs (by simp [systemGasConstraints,gasConstraintsWith]))
    (fun k hk => (conv_evals hL lay k hk).2) (pE_eval hL lay 15 (by omega)).2
    (fun j hj => by
      simp only [eval_c]; rw [(dl_eval hL lay 15 (by omega) j (by omega)).2, if_pos (by omega)])
    (SN_lt hL lay) hra

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
