import ZkFormal.NearV3.Assembly.RcptCandidateGasCompare
-- Deposit source SHA256: a3cc22518712cb1f1a2b9bdfaba008e9149902c5542cc9c196a10d657d1b5646.
-- Arithmetic proof migration; wider version ordering proved separately.
import ZkFormal.NearV3.Rcpt.Extract.V.GasCompare

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Deposit — the `DEP` rows: balances

`aft = bef + dep`, `aft ≠ u128::MAX`, `tot = aft + lk < 2^128`,
`q = (10^19·st) mod 2^128`, `big → tot ≥ q`, `¬big → st ≤ 770`.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Row `k` of the `DEP` field. -/
def dq (s Lp Lv Ls kt k : Nat) : Nat := s + (107 + Vt Lp Lv Ls kt) + k

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem bitsXn_eval {q : Nat} (hq : q + 1 < tr.height tt) (off len : Nat) :
    (bitsXn off len).eval tr tt q pub = (bitsX off len).eval tr tt (q + 1) pub := by
  simp only [bitsXn, bitsX, bits]
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [List.range_succ, List.map_append, eval_sum_append, List.map_cons, List.map_nil, eval_sum_cons,
      eval_sum_nil, eval_smul, eval_n, eval_c, nxt hq]
    rw [ih]

/-- Carry links of a 16-row field. -/
theorem fld_carry {s r0 X : Nat} (F : RFld tr tt s r0 16 X) (hH : r0 + 16 < tr.height tt) (cin : Nat) (E : Expr)
    (cout : Nat → Nat) (hb : ∀ k, k < 16 → cout k < P)
    (m0 : Expr.mul (.mul (c X) (c fs)) (c cin) ∈ receiptArithmeticCandidate.constraints)
    (m1 : mul3 (c X) (Dsl.not (c fe)) (sub (n cin) E) ∈ receiptArithmeticCandidate.constraints)
    (hE : ∀ k, k < 16 → E.eval tr tt (r0 + k) pub = ((cout k : Nat) : Fp)) :
    cv tr tt r0 cin = 0 ∧ ∀ k, k + 1 < 16 → cv tr tt (r0 + (k + 1)) cin = cout k := by
  constructor
  · have cc := con hL (r := r0) (by omega) m0
    have h1 : tr.cell tt r0 X = 1 := by simpa using F.fld.st 0 (by omega)
    have hfs : tr.cell tt r0 fs = 1 := by simpa using F.fld.fs 0 (by omega)
    simp only [eval_mul, eval_c] at cc
    rw [h1, hfs] at cc
    exact cv_zero_of_cell (by grind)
  · intro k hk
    have hn : r0 + k + 1 < tr.height tt := by omega
    have cc := con hL (r := r0 + k) (by omega) m1
    simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
    rw [F.fld.st k (by omega), F.fld.fe k (by omega), if_neg (by omega), hE k (by omega)] at cc
    have e : tr.cell tt (r0 + (k + 1)) cin = ((cout k : Nat) : Fp) := by
      rw [show r0 + (k + 1) = r0 + k + 1 by omega]; grind
    rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (hb k (by omega))]
where
  cv_zero_of_cell {q x : Nat} (h0 : tr.cell tt q x = 0) : cv tr tt q x = 0 := by
    unfold cv; rw [h0]; rfl

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

theorem dep_fld : RFld tr tt s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP ∧
    s + (107 + Vt Lp Lv Ls kt) + 16 < tr.height tt := by
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have := lay.fin
  exact ⟨lay.flds _ hm, by simp only at hle; omega⟩

theorem dep_row (k : Nat) (hk : k < 16) :
    dq s Lp Lv Ls kt k < tr.height tt ∧ tr.cell tt (dq s Lp Lv Ls kt k) sDEP = 1 ∧
    tr.cell tt (dq s Lp Lv Ls kt k) fs = (if k = 0 then 1 else 0) ∧
    tr.cell tt (dq s Lp Lv Ls kt k) fe = (if k = 15 then 1 else 0) ∧
    tr.cell tt (dq s Lp Lv Ls kt k) big = tr.cell tt s big := by
  obtain ⟨F, hH⟩ := dep_fld hL lay
  have hq : dq s Lp Lv Ls kt k < tr.height tt := by unfold dq; omega
  simp only [dq] at hq ⊢
  exact ⟨hq, F.fld.st k hk, F.fld.fs k hk, by rw [F.fld.fe k hk]; simp, F.consts k hk big (by simp [rconsts])⟩

/-- A byte-serial chain on the `DEP` rows from its row equations (in `Fp`). -/
theorem dep_chain (out : Nat) (cin : Nat) (E : Expr) (sv a : Nat → Nat) (cout : Nat → Nat)
    (hcout : ∀ k, k < 16 → cout k < 4096)
    (hE : ∀ k, k < 16 → E.eval tr tt (dq s Lp Lv Ls kt k) pub = ((cout k : Nat) : Fp))
    (m0 : Expr.mul (.mul (c sDEP) (c fs)) (c cin) ∈ receiptArithmeticCandidate.constraints)
    (m1 : mul3 (c sDEP) (Dsl.not (c fe)) (sub (n cin) E) ∈ receiptArithmeticCandidate.constraints)
    (hrow : ∀ k, k < 16 → cv tr tt (dq s Lp Lv Ls kt k) cin < 4096 →
      sv k + 256 * cout k = a k + cv tr tt (dq s Lp Lv Ls kt k) cin) :
    sumL sv 16 + 256 ^ 16 * cout 15 = sumL a 16 := by
  obtain ⟨F, hH⟩ := dep_fld hL lay
  obtain ⟨c0, cl⟩ := fld_carry hL F hH cin E cout (fun k hk => by have := hcout k hk; unfold P; omega) m0 m1
    (fun k hk => hE k hk)
  have c0' : cv tr tt (dq s Lp Lv Ls kt 0) cin = 0 := by simpa [dq] using c0
  have cl' : ∀ k, k + 1 < 16 → cv tr tt (dq s Lp Lv Ls kt (k + 1)) cin = cout k := fun k hk => cl k hk
  have cb : ∀ k, k < 16 → cv tr tt (dq s Lp Lv Ls kt k) cin < 4096 := by
    intro k hk; cases k with
    | zero => rw [c0']; omega
    | succ k => rw [cl' k hk]; exact hcout k (by omega)
  have := chain 16 (by omega) sv a (fun k => cv tr tt (dq s Lp Lv Ls kt k) cin) cout
    (fun k hk => hrow k hk (cb k hk)) c0' cl'
  simpa using this

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

theorem dep_bits (k : Nat) (hk : k < 16) (off len : Nat) (hl : off + len ≤ 66) :
    (bitsX off len).eval tr tt (Q k) pub = ((bvN tr tt (Q k) off len : Nat) : Fp) ∧ bvN tr tt (Q k) off len < 2 ^ len :=
  bitsX_eval hL (dep_row hL lay k hk).1 off len hl

theorem xbit (k : Nat) (hk : k < 16) (j : Nat) (hj : j < 66) : cv tr tt (Q k) (xb j) ≤ 1 :=
  cv_bool (xb_bool hL (dep_row hL lay k hk).1 j hj)

/-- **`aft = bef + dep`.** -/
theorem dep_aft (hbef : ∀ k, k < 16 → cv tr tt (Q k) bef < 256) (hdep : ∀ k, k < 16 → cv tr tt (Q k) b < 256) :
    sumL (fun k => bvN tr tt (Q k) 0 8) 16 = sumL (fun k => cv tr tt (Q k) bef) 16 + sumL (fun k => cv tr tt (Q k) b) 16 := by
  have hc := dep_chain hL lay 0 c1 (c (xb 8)) (fun k => bvN tr tt (Q k) 0 8)
    (fun k => cv tr tt (Q k) bef + cv tr tt (Q k) b) (fun k => cv tr tt (Q k) (xb 8))
    (fun k hk => by have := xbit hL lay k hk 8 (by omega); omega)
    (fun k hk => by simp only [eval_c]; exact cast_cv tr tt _ _)
    (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (fun k hk hcin => by
      obtain ⟨hq, h1, -⟩ := dep_row hL lay k hk
      obtain ⟨be, bl⟩ := dep_bits hL lay k hk 0 8 (by omega)
      have cc := con hL hq (e := .mul dp (sub (sum [c bef, c b, c c1]) (.add aftE (smul 256 (c (xb 8))))))
        (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, aftE, eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_sum_cons, eval_sum_nil] at cc
      rw [h1, be, cast_cv tr tt _ bef, cast_cv tr tt _ b, cast_cv tr tt _ c1, cast_cv tr tt _ (xb 8)] at cc
      have := hbef k hk; have := hdep k hk; have := xbit hL lay k hk 8 (by omega)
      apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul]; grind)
  have hf : cv tr tt (Q 15) (xb 8) = 0 := by
    obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay 15 (by omega)
    have cc := con hL hq (e := mul3 dp (c fe) (c (xb 8))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
    simp only [dp, eval_mul3, eval_c] at cc
    rw [h1, hfe, if_pos rfl] at cc
    unfold cv; rw [show tr.cell tt (Q 15) (xb 8) = 0 by grind]; rfl
  simp only [hf, Nat.mul_zero, Nat.add_zero] at hc
  rw [hc, sumL_add]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem natCast_sub' (a b : Nat) (h : b ≤ a) : ((a - b : Nat) : Fp) = (a : Fp) - (b : Fp) := by
  have e : ((a - b + b : Nat) : Fp) = (a : Fp) := by rw [Nat.sub_add_cancel h]
  rw [natCast_add] at e; grind

def natSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natSum f n + f n

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

/-- **`aft ≠ u128::MAX`**: some byte is not `255`. -/
theorem dep_notmax : ∃ k, k < 16 ∧ bvN tr tt (Q k) 0 8 ≠ 255 := by
  have Ab : ∀ k, k < 16 → bvN tr tt (Q k) 0 8 < 256 := fun k hk => (dep_bits hL lay k hk 0 8 (by omega)).2
  have ds : ∀ k, k < 16 → tr.cell tt (Q k) dsum = ((natSum (fun m => 255 - bvN tr tt (Q m) 0 8) (k + 1) : Nat) : Fp) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨hq, h1, hfs, -⟩ := dep_row hL lay 0 (by omega)
      have cc := con hL hq (e := mul3 dp (c fs) (sub (c dsum) (sub (k 255) aftE))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, aftE, eval_mul3, eval_c, eval_sub, eval_k] at cc
      rw [h1, hfs, if_pos rfl, (dep_bits hL lay 0 (by omega) 0 8 (by omega)).1] at cc
      have := Ab 0 (by omega)
      simp only [natSum, Nat.zero_add]
      rw [natCast_sub' _ _ (by omega)]
      grind
    | succ k ih =>
      intro hk
      obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay k (by omega)
      have hn : (Q k) + 1 < tr.height tt := by have := (dep_row hL lay (k + 1) hk).1; unfold dq at *; omega
      have cc := con hL hq (e := mul3 dp (Dsl.not (c fe)) (sub (n dsum) (.add (c dsum) (sub (Dsl.k 255) (bitsXn 0 8)))))
        (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_n, nxt hn] at cc
      rw [h1, hfe, if_neg (by omega), bitsXn_eval hL hn, show (Q k) + 1 = Q (k + 1) by unfold dq; omega,
        (dep_bits hL lay (k + 1) hk 0 8 (by omega)).1, ih (by omega)] at cc
      have := Ab (k + 1) hk
      rw [show natSum (fun m => 255 - bvN tr tt (Q m) 0 8) (k + 1 + 1) =
        natSum (fun m => 255 - bvN tr tt (Q m) 0 8) (k + 1) + (255 - bvN tr tt (Q (k + 1)) 0 8) from rfl, natCast_add,
        natCast_sub' _ _ (by omega)]
      grind
  refine Classical.byContradiction fun hne => ?_
  have all : ∀ k, k < 16 → bvN tr tt (Q k) 0 8 = 255 := fun k hk =>
    Classical.byContradiction fun h' => hne ⟨k, hk, h'⟩
  have z : natSum (fun m => 255 - bvN tr tt (Q m) 0 8) 16 = 0 := by
    simp only [natSum]; simp only [all _ (by omega : (0:Nat) < 16), all 1 (by omega), all 2 (by omega),
      all 3 (by omega), all 4 (by omega), all 5 (by omega), all 6 (by omega), all 7 (by omega), all 8 (by omega),
      all 9 (by omega), all 10 (by omega), all 11 (by omega), all 12 (by omega), all 13 (by omega),
      all 14 (by omega), all 15 (by omega)]
  obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay 15 (by omega)
  have cc := con hL hq (e := mul3 dp (c fe) (sub (.mul (c dsum) (c invB)) (k 1))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
  simp only [dp, eval_mul3, eval_mul, eval_c, eval_sub, eval_k] at cc
  rw [h1, hfe, if_pos rfl, ds 15 (by omega), z] at cc
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

theorem dep_last_zero (x : Nat) (hm : mul3 dp (c fe) (c x) ∈ receiptArithmeticCandidate.constraints) : cv tr tt (Q 15) x = 0 := by
  obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay 15 (by omega)
  have cc := con hL hq hm
  simp only [dp, eval_mul3, eval_c] at cc
  rw [h1, hfe, if_pos rfl] at cc
  unfold cv; rw [show tr.cell tt (Q 15) x = 0 by grind]; rfl

/-- **`tot = aft + lk`.** -/
theorem dep_tot (hlk : ∀ k, k < 16 → cv tr tt (Q k) lk < 256) :
    sumL (fun k => bvN tr tt (Q k) 9 8) 16 = sumL (fun k => bvN tr tt (Q k) 0 8) 16 + sumL (fun k => cv tr tt (Q k) lk) 16 := by
  have hc := dep_chain hL lay 0 c2 (c (xb 17)) (fun k => bvN tr tt (Q k) 9 8)
    (fun k => bvN tr tt (Q k) 0 8 + cv tr tt (Q k) lk) (fun k => cv tr tt (Q k) (xb 17))
    (fun k hk => by have := xbit hL lay k hk 17 (by omega); omega)
    (fun k hk => by simp only [eval_c]; exact cast_cv tr tt _ _)
    (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (fun k hk hcin => by
      obtain ⟨hq, h1, -⟩ := dep_row hL lay k hk
      obtain ⟨be, bl⟩ := dep_bits hL lay k hk 0 8 (by omega)
      obtain ⟨be2, bl2⟩ := dep_bits hL lay k hk 9 8 (by omega)
      have cc := con hL hq (e := .mul dp (sub (sum [aftE, c lk, c c2]) (.add (bitsX 9 8) (smul 256 (c (xb 17))))))
        (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, aftE, eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_sum_cons, eval_sum_nil] at cc
      rw [h1, be, be2, cast_cv tr tt _ lk, cast_cv tr tt _ c2, cast_cv tr tt _ (xb 17)] at cc
      have := hlk k hk; have := xbit hL lay k hk 17 (by omega)
      apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul]; grind)
  rw [dep_last_zero hL lay (xb 17) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))] at hc
  simp only [Nat.mul_zero, Nat.add_zero] at hc
  rw [hc, sumL_add]

/-- Delay line of the storage bytes. -/
theorem dep_dl : ∀ k, k < 16 → ∀ j, j < 7 →
    tr.cell tt (Q k) (dl j) = ((if j < k then cv tr tt (Q (k - 1 - j)) st else 0 : Nat) : Fp) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    obtain ⟨hq, h1, hfs, -⟩ := dep_row hL lay 0 (by omega)
    have cc := con hL hq (e := mul3 dp (c fs) (c (dl j))) (mem_dp (by
      unfold depositAgeConstraints depositConstraintsWith; simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
    simp only [dp, eval_mul3, eval_c] at cc
    rw [h1, hfs, if_pos rfl] at cc
    rw [if_neg (by omega)]; grind
  | succ k ih =>
    intro hk j hj
    obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay k (by omega)
    have hn : (Q k) + 1 < tr.height tt := by have := (dep_row hL lay (k + 1) hk).1; unfold dq at *; omega
    have e1 : (Q (k + 1)) = (Q k) + 1 := by unfold dq; omega
    rw [e1]
    cases j with
    | zero =>
      have cc := con hL hq (e := mul3 dp (Dsl.not (c fe)) (sub (n (dl 0)) (c st))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
      rw [h1, hfe, if_neg (by omega), cast_cv tr tt _ st] at cc
      rw [if_pos (by omega), show k + 1 - 1 - 0 = k by omega]; grind
    | succ j =>
      have cc := con hL hq (e := mul3 dp (Dsl.not (c fe)) (sub (n (dl (j + 1))) (c (dl j)))) (mem_dp (by
        unfold depositAgeConstraints depositConstraintsWith; simp only [List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)))
      simp only [dp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
      rw [h1, hfe, if_neg (by omega), ih (by omega) j (by omega)] at cc
      by_cases hjk : j < k
      · rw [if_pos hjk] at cc; rw [if_pos (by omega), show k + 1 - 1 - (j + 1) = k - 1 - j by omega]; grind
      · rw [if_neg hjk] at cc; rw [if_neg (by omega)]; grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

theorem dep_conv (k : Nat) (hk : k < 16) :
    (conv S_LE (c st) (fun j => c (dl j))).eval tr tt (Q k) pub =
      ((convS (fun m => cv tr tt (Q m) st) k : Nat) : Fp) := by
  have D := dep_dl hL lay k hk
  simp only [conv, S_LE, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    eval_sum_cons, eval_sum_nil, eval_smul, eval_c, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd,
    show ¬ (1 = 0) by decide, show ¬ (2 = 0) by decide, show ¬ (3 = 0) by decide, show ¬ (4 = 0) by decide,
    show ¬ (5 = 0) by decide, show ¬ (6 = 0) by decide, show ¬ (7 = 0) by decide]
  rw [D 1 (by omega), D 2 (by omega), D 3 (by omega), D 4 (by omega), D 5 (by omega), D 6 (by omega)]
  simp only [convS, Nat.sub_sub, Nat.reduceAdd, show (1 < k) = (2 ≤ k) from rfl, show (2 < k) = (3 ≤ k) from rfl,
    show (3 < k) = (4 ≤ k) from rfl, show (4 < k) = (5 ≤ k) from rfl, show (5 < k) = (6 ≤ k) from rfl,
    show (6 < k) = (7 ≤ k) from rfl]
  simp only [natCast_add, natCast_mul]; grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

/-- **`q = (10^19·st) mod 2^128`.** -/
theorem dep_q (hst : ∀ k, k < 16 → cv tr tt (Q k) st < 256) :
    sumL (fun k => bvN tr tt (Q k) 18 8) 16 =
      (NearSpec.Params.storageAmountPerByte * sumL (fun k => cv tr tt (Q k) st) 16) % NearSpec.Params.two128 := by
  have Cb : ∀ k, k < 16 → bvN tr tt (Q k) 26 12 < 4096 := fun k hk => (dep_bits hL lay k hk 26 12 (by omega)).2
  have hc := dep_chain hL lay 0 c3 (bitsX 26 12) (fun k => bvN tr tt (Q k) 18 8)
    (convS (fun m => cv tr tt (Q m) st)) (fun k => bvN tr tt (Q k) 26 12) Cb
    (fun k hk => (dep_bits hL lay k hk 26 12 (by omega)).1)
    (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (fun k hk hcin => by
      obtain ⟨hq, h1, -⟩ := dep_row hL lay k hk
      obtain ⟨be, bl⟩ := dep_bits hL lay k hk 18 8 (by omega)
      obtain ⟨be2, bl2⟩ := dep_bits hL lay k hk 26 12 (by omega)
      have cc := con hL hq (e := .mul dp (sub (.add (conv S_LE (c st) (fun j => c (dl j))) (c c3))
        (.add (bitsX 18 8) (smul 256 (bitsX 26 12))))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul, eval_sub, eval_add, eval_smul, eval_c] at cc
      rw [h1, be, be2, dep_conv hL lay k hk, cast_cv tr tt _ c3] at cc
      have hcv : convS (fun m => cv tr tt (Q m) st) k ≤ 255 * 745 := by
        simp only [convS]
        have a : ∀ j, (if j ≤ k then cv tr tt (Q (k - j)) st else 0) ≤ 255 := fun j => by
          split <;> (try exact Nat.le_of_lt_succ (hst _ (by omega))) <;> omega
        have := a 2; have := a 3; have := a 4; have := a 5; have := a 6; have := a 7; omega
      apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul]; grind)
  have hf : bvN tr tt (Q 15) 26 12 = 0 := by
    obtain ⟨hq, h1, -, hfe, -⟩ := dep_row hL lay 15 (by omega)
    have cc := con hL hq (e := mul3 dp (c fe) (bitsX 26 12)) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
    simp only [dp, eval_mul3, eval_c] at cc
    rw [h1, hfe, if_pos rfl, (dep_bits hL lay 15 (by omega) 26 12 (by omega)).1] at cc
    exact nat_of_fp (by have := Cb 15 (by omega); unfold P; omega) (by unfold P; omega) (by grind)
  simp only [hf, Nat.mul_zero, Nat.add_zero] at hc
  have hlt : sumL (fun k => bvN tr tt (Q k) 18 8) 16 < NearSpec.Params.two128 := by
    have := sumL_lt (fun k => bvN tr tt (Q k) 18 8) 16 (fun k hk => (dep_bits hL lay k hk 18 8 (by omega)).2)
    simpa [NearSpec.Params.two128] using this
  rw [convS_id, ← hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **`big → q ≤ tot`.** -/
theorem dep_cmp (hbig : tr.cell tt s big = 1) :
    sumL (fun k => bvN tr tt (Q k) 18 8) 16 ≤ sumL (fun k => bvN tr tt (Q k) 9 8) 16 := by
  have hc := dep_chain hL lay 0 c4 (c (xb 46)) (fun k => bvN tr tt (Q k) 9 8)
    (fun k => bvN tr tt (Q k) 18 8 + bvN tr tt (Q k) 38 8) (fun k => cv tr tt (Q k) (xb 46))
    (fun k hk => by have := xbit hL lay k hk 46 (by omega); omega)
    (fun k hk => by simp only [eval_c]; exact cast_cv tr tt _ _)
    (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith, dp])) (fun k hk hcin => by
      obtain ⟨hq, h1, -⟩ := dep_row hL lay k hk
      obtain ⟨be, bl⟩ := dep_bits hL lay k hk 9 8 (by omega)
      obtain ⟨be2, bl2⟩ := dep_bits hL lay k hk 18 8 (by omega)
      obtain ⟨be3, bl3⟩ := dep_bits hL lay k hk 38 8 (by omega)
      have cc := con hL hq (e := .mul dp (sub (sub (bitsX 9 8) (bitsX 18 8))
        (sub (.add (c c4) (bitsX 38 8)) (smul 256 (c (xb 46)))))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul, eval_sub, eval_add, eval_smul, eval_c] at cc
      rw [h1, be, be2, be3, cast_cv tr tt _ c4, cast_cv tr tt _ (xb 46)] at cc
      have := xbit hL lay k hk 46 (by omega)
      apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul]; grind)
  have hf : cv tr tt (Q 15) (xb 46) = 0 := by
    obtain ⟨hq, h1, -, hfe, hb⟩ := dep_row hL lay 15 (by omega)
    have cc := con hL hq (e := .mul (mul3 dp (c fe) (c big)) (c (xb 46))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
    simp only [dp, eval_mul, eval_mul3, eval_c] at cc
    rw [h1, hfe, if_pos rfl, hb, hbig] at cc
    unfold cv; rw [show tr.cell tt (Q 15) (xb 46) = 0 by grind]; rfl
  simp only [hf, Nat.mul_zero, Nat.add_zero] at hc
  rw [hc, sumL_add]; omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_lt chain sumL_add convS convS_id chainC)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

local notation "Q" k => dq s Lp Lv Ls kt k

/-- **`¬big → st ≤ 770`.** -/
theorem dep_small (hbig : tr.cell tt s big = 0) (hst : ∀ k, k < 16 → cv tr tt (Q k) st < 256) :
    sumL (fun k => cv tr tt (Q k) st) 16 ≤ 770 := by
  have r1v : ∀ k, k < 16 → tr.cell tt (Q k) r1 = if k = 1 then 1 else 0 := by
    intro k hk
    cases k with
    | zero =>
      obtain ⟨hq, h1, hfs, -⟩ := dep_row hL lay 0 (by omega)
      have cc := con hL hq (e := mul3 dp (c fs) (c r1)) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul3, eval_c] at cc
      rw [h1, hfs, if_pos rfl] at cc; simp; grind
    | succ k =>
      obtain ⟨hq, h1, hfs, hfe, -⟩ := dep_row hL lay k (by omega)
      have hn : (Q k) + 1 < tr.height tt := by have := (dep_row hL lay (k + 1) hk).1; unfold dq at *; omega
      have cc := con hL hq (e := mul3 dp (Dsl.not (c fe)) (sub (n r1) (c fs))) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
      simp only [dp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
      rw [h1, hfe, if_neg (by omega), hfs] at cc
      rw [show (Q (k + 1)) = (Q k) + 1 by unfold dq; omega]
      by_cases h0 : k = 0
      · subst h0; simp at cc ⊢; grind
      · rw [if_neg h0] at cc; rw [if_neg (by omega)]; grind
  have zero : ∀ k, 2 ≤ k → k < 16 → cv tr tt (Q k) st = 0 := by
    intro k h2 hk
    obtain ⟨hq, h1, hfs, -, hb⟩ := dep_row hL lay k hk
    have cc := con hL hq (e := mul3 (Dsl.not (c big)) (sub (sub dp (c fs)) (c r1)) (c st)) (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
    simp only [dp, eval_mul3, eval_c, eval_not, eval_sub] at cc
    rw [h1, hfs, if_neg (by omega), r1v k hk, if_neg (by omega), hb, hbig] at cc
    unfold cv; rw [show tr.cell tt (Q k) st = 0 by grind]; rfl
  obtain ⟨hq, -, -, -, hb⟩ := dep_row hL lay 1 (by omega)
  have cc := con hL hq (e := mul3 (Dsl.not (c big)) (c r1) (sub (Dsl.k 770) (sum [c (dl 0), smul 256 (c st), bitsX 47 10])))
    (mem_dp (by simp [depositAgeConstraints,depositConstraintsWith]))
  obtain ⟨be, bl⟩ := dep_bits hL lay 1 (by omega) 47 10 (by omega)
  simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_k, eval_sum_cons, eval_sum_nil, eval_smul] at cc
  rw [hb, hbig, r1v 1 (by omega), if_pos rfl, dep_dl hL lay 1 (by omega) 0 (by omega), if_pos (by omega), be,
    cast_cv tr tt _ st] at cc
  have := hst 0 (by omega); have := hst 1 (by omega)
  have e : 770 = cv tr tt (Q 0) st + 256 * cv tr tt (Q 1) st + bvN tr tt (Q 1) 47 10 := by
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  simp only [sumL]
  simp only [zero _ (by omega : 2 ≤ 2) (by omega), zero 3 (by omega) (by omega), zero 4 (by omega) (by omega),
    zero 5 (by omega) (by omega), zero 6 (by omega) (by omega), zero 7 (by omega) (by omega),
    zero 8 (by omega) (by omega), zero 9 (by omega) (by omega), zero 10 (by omega) (by omega),
    zero 11 (by omega) (by omega), zero 12 (by omega) (by omega), zero 13 (by omega) (by omega),
    zero 14 (by omega) (by omega), zero 15 (by omega) (by omega)]
  omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
