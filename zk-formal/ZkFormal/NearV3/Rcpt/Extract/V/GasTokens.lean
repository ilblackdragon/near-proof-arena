import ZkFormal.NearV3.Rcpt.Extract.V.GasProduct
import ZkFormal.NearV3.Rcpt.Extract.V.Deposit

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.GasTokens — `GP` rows: running tokens, refund flag

The `tok` register rotates through the `GP` rows and is rewritten with
`tok + burnt` (byte-serial, no final carry); `hr = [sur ≠ 0]`.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain sumL_add)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem sumL_zero_iff (f : Nat → Nat) (L : Nat) : sumL f L = 0 ↔ ∀ k, k < L → f k = 0 := by
  induction L with
  | zero => simp [sumL]
  | succ L ih =>
    simp only [sumL]
    constructor
    · intro h k hk
      have h1 : sumL f L = 0 := by omega
      have h2 : 256 ^ L * f L = 0 := by omega
      rcases Nat.lt_or_ge k L with hk' | hk'
      · exact ih.mp h1 k hk'
      · have : k = L := by omega
        subst this
        rcases Nat.mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega)))
        · exact h3
    · intro h
      rw [ih.mpr (fun k hk => h k (by omega)), h L (by omega)]; simp

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Tokens are kept on active receipt and list-header rows outside GP, except the final receipt row. -/
theorem tok_keep {q : Nat} (hq : q + 1 < tr.height tt) (ha : tr.cell tt q act = 1)
    (hg : tr.cell tt q sGP = 0) (hl : tr.cell tt q lastR = 0) :
    ∀ j, j < 16 → tr.cell tt (q + 1) (tok j) = tr.cell tt q (tok j) := by
  intro j hj
  have cc := con hL (by omega : q < _) (e := .mul (sub (sub (c act) (c sGP)) (c lastR)) (sub (n (tok j)) (c (tok j))))
    (mem_rg (by
      unfold cRegs; simp only [List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  simp only [rowE, eval_mul, eval_sub, eval_c, eval_n, nxt hq] at cc
  rw [ha, hg, hl] at cc; grind

variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

/-- The `tok` register along the `GP` rows. -/
theorem tok_rot : ∀ k, k ≤ 16 → ∀ j, j < 16 →
    tr.cell tt (gq s Lp Lv Ls kt 0 + k) (tok j) =
      if j + k < 16 then tr.cell tt (gq s Lp Lv Ls kt 0) (tok (j + k))
      else ((bvN tr tt (gq s Lp Lv Ls kt (j + k - 16)) 31 8 : Nat) : Fp) := by
  intro k
  induction k with
  | zero => intro _ j hj; simp [hj]
  | succ k ih =>
    intro hk j hj
    obtain ⟨hq, h1, -⟩ := gp_row hL lay k (by omega)
    have hn : gq s Lp Lv Ls kt k + 1 < tr.height tt := by
      have := (gp_fld hL lay).2; unfold gq at *; omega
    have e0 : gq s Lp Lv Ls kt 0 + (k + 1) = gq s Lp Lv Ls kt k + 1 := by unfold gq; omega
    have e1 : gq s Lp Lv Ls kt 0 + k = gq s Lp Lv Ls kt k := by unfold gq; omega
    rw [e0]
    by_cases hj15 : j < 15
    · have cc := con hL hq (e := .mul (c sGP) (sub (n (tok j)) (c (tok (j + 1))))) (mem_rg (by
        unfold cRegs; simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj15, rfl⟩)))))
      simp only [eval_mul, eval_sub, eval_c, eval_n, nxt hn] at cc
      rw [h1] at cc
      have := ih (by omega) (j + 1) (by omega)
      rw [e1] at this
      rw [show tr.cell tt (gq s Lp Lv Ls kt k + 1) (tok j) = tr.cell tt (gq s Lp Lv Ls kt k) (tok (j + 1)) by
        grind, this]
      simp only [show j + 1 + k = j + (k + 1) by omega]
    · have hj' : j = 15 := by omega
      subst hj'
      have cc := con hL hq (e := .mul (c sGP) (sub (n (tok 15)) (bitsX 31 8))) (mem_rg (by simp [cRegs]))
      simp only [eval_mul, eval_sub, eval_c, eval_n, nxt hn] at cc
      rw [h1, (bitsX_eval hL hq 31 8 (by omega)).1] at cc
      rw [if_neg (by omega), show 15 + (k + 1) - 16 = k by omega]
      simp only [bvN]; grind

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain sumL_add)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
include lay

/-- **Running tokens: `new = old + burnt`.** -/
theorem gp_tok (hold : ∀ j, j < 16 → cv tr tt (gq s Lp Lv Ls kt 0) (tok j) < 256)
    (hbu : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) burnt < 256) :
    sumL (fun k => bvN tr tt (gq s Lp Lv Ls kt k) 31 8) 16 =
      sumL (fun j => cv tr tt (gq s Lp Lv Ls kt 0) (tok j)) 16 +
        sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) burnt) 16 := by
  have R := gp_row hL lay
  have Xb : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) (xb 39) ≤ 1 := fun k hk =>
    cv_bool (xb_bool hL (R k hk).1 39 (by omega))
  have c0 : cv tr tt (gq s Lp Lv Ls kt 0) c4 = 0 := by
    obtain ⟨hq, h1, hfs, -⟩ := R 0 (by omega)
    have cc := con hL hq (e := .mul (.mul gp (c fs)) (c c4)) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul, eval_c] at cc
    rw [h1, hfs, if_pos rfl] at cc
    exact cv_zero_of hL lay (by grind)
  have cl : ∀ k, k + 1 < 16 → cv tr tt (gq s Lp Lv Ls kt (k + 1)) c4 = cv tr tt (gq s Lp Lv Ls kt k) (xb 39) := by
    intro k hk
    obtain ⟨hq, h1, -, hfe, -⟩ := R k (by omega)
    have hn : gq s Lp Lv Ls kt k + 1 < tr.height tt := by have := (R (k + 1) hk).1; unfold gq at *; omega
    have cc := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n c4) (c (xb 39)))) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
    rw [h1, hfe, if_neg (by omega)] at cc
    have e : tr.cell tt (gq s Lp Lv Ls kt (k + 1)) c4 = tr.cell tt (gq s Lp Lv Ls kt k) (xb 39) := by
      rw [show gq s Lp Lv Ls kt (k + 1) = gq s Lp Lv Ls kt k + 1 by unfold gq; omega]; grind
    simp [cv, e]
  have cb : ∀ k, k < 16 → cv tr tt (gq s Lp Lv Ls kt k) c4 ≤ 1 := by
    intro k hk; cases k with
    | zero => rw [c0]; omega
    | succ k => rw [cl k hk]; exact Xb k (by omega)
  have cf : cv tr tt (gq s Lp Lv Ls kt 15) (xb 39) = 0 := by
    obtain ⟨hq, h1, -, hfe, -⟩ := R 15 (by omega)
    have cc := con hL hq (e := mul3 gp (c fe) (c (xb 39))) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul3, eval_c] at cc
    rw [h1, hfe, if_pos rfl] at cc
    exact cv_zero_of hL lay (by grind)
  have hrow : ∀ k, k < 16 → bvN tr tt (gq s Lp Lv Ls kt k) 31 8 + 256 * cv tr tt (gq s Lp Lv Ls kt k) (xb 39) =
      (cv tr tt (gq s Lp Lv Ls kt 0) (tok k) + cv tr tt (gq s Lp Lv Ls kt k) burnt) +
        cv tr tt (gq s Lp Lv Ls kt k) c4 := by
    intro k hk
    obtain ⟨hq, h1, -⟩ := R k hk
    have cc := con hL hq (e := .mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0), c burnt, c c4])))
      (mem_gs (by simp [cGas]))
    obtain ⟨be, bl⟩ := bitsX_eval hL hq 31 8 (by omega)
    have be' : (bitsX 31 8).eval tr tt (gq s Lp Lv Ls kt k) pub = ((bvN tr tt (gq s Lp Lv Ls kt k) 31 8 : Nat) : Fp) := be
    have bl' : bvN tr tt (gq s Lp Lv Ls kt k) 31 8 < 256 := bl
    have tr0 := tok_rot hL lay k (by omega) 0 (by omega)
    rw [if_pos (by omega), show gq s Lp Lv Ls kt 0 + k = gq s Lp Lv Ls kt k by unfold gq; omega,
      Nat.zero_add] at tr0
    simp only [gp, eval_mul, eval_c, eval_sub, eval_add, eval_smul, eval_sum_cons, eval_sum_nil] at cc
    rw [h1, be', tr0, cast_cv tr tt _ (xb 39), cast_cv tr tt _ (tok k), cast_cv tr tt _ burnt, cast_cv tr tt _ c4] at cc
    have := hold k hk; have := hbu k hk; have := Xb k hk; have := cb k hk
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  have hc := chain 16 (by omega) (fun k => bvN tr tt (gq s Lp Lv Ls kt k) 31 8)
    (fun k => cv tr tt (gq s Lp Lv Ls kt 0) (tok k) + cv tr tt (gq s Lp Lv Ls kt k) burnt)
    (fun k => cv tr tt (gq s Lp Lv Ls kt k) c4) (fun k => cv tr tt (gq s Lp Lv Ls kt k) (xb 39)) hrow c0 cl
  simp only [show 16 - 1 = 15 from rfl, cf, Nat.mul_zero, Nat.add_zero] at hc
  rw [hc, sumL_add]

/-- **Refund flag.** -/
theorem gp_hr (hns : tr.cell tt s RcptV3.sys=0) : tr.cell tt s RcptV3.hr = 1 ↔ sumL (SN tr tt s Lp Lv Ls kt) 16 ≠ 0 := by
  have R := gp_row hL lay
  have Db : ∀ k, k < 16 → bvN tr tt (gq s Lp Lv Ls kt k) 0 8 < 256 := fun k hk => (bitsX_eval hL (R k hk).1 0 8 (by omega)).2
  have De : ∀ k, k < 16 → (bitsX 0 8).eval tr tt (gq s Lp Lv Ls kt k) pub =
      ((bvN tr tt (gq s Lp Lv Ls kt k) 0 8 : Nat) : Fp) := fun k hk => (bitsX_eval hL (R k hk).1 0 8 (by omega)).1
  -- the running sum of D
  have sd : ∀ k, k < 16 → tr.cell tt (gq s Lp Lv Ls kt k) sumD =
      ((sumL (fun _ => 0) 0 + (List.range (k + 1)).foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 : Nat) : Fp) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨hq, h1, hfs, -⟩ := R 0 (by omega)
      have cc := con hL hq (e := mul3 gp (c fs) (sub (c sumD) DE)) (mem_gs (by simp [cGas]))
      simp only [gp, DE, eval_mul3, eval_c, eval_sub] at cc
      rw [h1, hfs, if_pos rfl, De 0 (by omega)] at cc
      simp only [sumL, List.range_one, List.foldr_cons, List.foldr_nil, Nat.zero_add, Nat.add_zero]; grind
    | succ k ih =>
      intro hk
      obtain ⟨hq, h1, -, hfe, -⟩ := R k (by omega)
      have hn : gq s Lp Lv Ls kt k + 1 < tr.height tt := by have := (R (k + 1) hk).1; unfold gq at *; omega
      have cc := con hL hq (e := mul3 gp (Dsl.not (c fe)) (sub (n sumD) (.add (c sumD) DEn))) (mem_gs (by simp [cGas]))
      simp only [gp, DEn, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_n, nxt hn] at cc
      rw [h1, hfe, if_neg (by omega), bitsXn_eval hL hn, show gq s Lp Lv Ls kt k + 1 = gq s Lp Lv Ls kt (k + 1) by
        unfold gq; omega, De (k + 1) hk, ih (by omega)] at cc
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero, sumL, Nat.zero_add] at cc ⊢
      have gen : ∀ (l : List Nat) (a : Nat), l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) a =
          l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 + a := by
        intro l; induction l with
        | nil => intro a; simp
        | cons x l ihl => intro a; simp only [List.foldr_cons]; rw [ihl]; omega
      rw [gen, natCast_add]; grind
  have hs : s < tr.height tt := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  have fs_lt : ∀ k, k < 16 → (List.range (k + 1)).foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 ≤
      255 * (k + 1) := by
    intro k
    induction k with
    | zero => intro _; simp; have := Db 0 (by omega); omega
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
      have gen : ∀ (l : List Nat) (a : Nat), l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) a =
          l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 + a := by
        intro l; induction l with
        | nil => intro a; simp
        | cons x l ihl => intro a; simp only [List.foldr_cons]; rw [ihl]; omega
      rw [gen]; have := ih (by omega); have := Db (k + 1) hk; omega
  have fs_zero : ∀ k, (List.range (k + 1)).foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 = 0 →
      ∀ m, m ≤ k → bvN tr tt (gq s Lp Lv Ls kt m) 0 8 = 0 := by
    intro k hz m hm
    have gen : ∀ (l : List Nat), l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 = 0 →
        ∀ m ∈ l, bvN tr tt (gq s Lp Lv Ls kt m) 0 8 = 0 := by
      intro l; induction l with
      | nil => intro _ m hm; simp at hm
      | cons x l ihl =>
        intro h0 m hm
        simp only [List.foldr_cons] at h0
        rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · exact ihl (by omega) m hm
    exact gen _ hz m (List.mem_range.mpr (by omega))
  obtain ⟨hq15, h115, -, hfe15, -, hhr15, -⟩ := R 15 (by omega)
  constructor
  · intro hhr
    have cc := con hL hq15 (e := mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c RcptV3.hr))) (mem_gs (by simp [cGas]))
    simp only [gp, eval_mul3, eval_mul, eval_c, eval_sub] at cc
    rw [h115, hfe15, if_pos rfl, hhr15, hhr, sd 15 (by omega)] at cc
    simp only [sumL, Nat.zero_add] at cc
    have hne : (List.range 16).foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 ≠ 0 := by
      intro hz; rw [hz] at cc; grind
    have hge : cv tr tt s ge = 1 := by
      have := (bounds hL hs).2.2.2 hhr; simp [cv, this, Fp.toNat_one]
    intro hS
    rw [sumL_zero_iff] at hS
    apply hne
    have : ∀ m, m < 16 → bvN tr tt (gq s Lp Lv Ls kt m) 0 8 = 0 := fun m hm => by
      have := hS m hm; simp only [SN, hge, ↓reduceIte] at this; exact this
    have gen : ∀ (l : List Nat), (∀ m ∈ l, m < 16) → l.foldr (fun m acc => bvN tr tt (gq s Lp Lv Ls kt m) 0 8 + acc) 0 = 0 := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons x l ihl => intro hl; simp only [List.foldr_cons]; rw [this x (hl x (by simp)), ihl (fun m hm => hl m (by simp [hm]))]
    exact gen _ (fun m hm => List.mem_range.mp hm)
  · intro hS
    rw [ne_eq, sumL_zero_iff] at hS
    obtain ⟨m, hm, hne⟩ : ∃ m, m < 16 ∧ SN tr tt s Lp Lv Ls kt m ≠ 0 := by
      refine Classical.byContradiction fun hc => hS fun m hm => Classical.byContradiction fun h0 => hc ⟨m, hm, h0⟩
    have hge : cv tr tt s ge = 1 := by
      unfold SN at hne; split at hne
      · assumption
      · exact absurd rfl hne
    have hD : bvN tr tt (gq s Lp Lv Ls kt m) 0 8 ≠ 0 := by simpa [SN, hge] using hne
    rcases isBool hL hs (x := RcptV3.hr) (by simp [boolCols]) with e | e
    · exfalso
      obtain ⟨hq, h1, -, -, hgeq, hhrq, -⟩ := R m hm
      have cc := con hL hq (e := .mul (mul3 gp (Dsl.not (c RcptV3.hr)) (c RcptV3.gq)) DE) (mem_gs (by simp [cGas]))
      simp only [gp, DE, eval_mul, eval_mul3, eval_c, eval_not] at cc
      have hgeF : tr.cell tt s ge = 1 := by
        rcases ge_cases hL lay with ⟨_, e2⟩ | ⟨e1, _⟩
        · rw [e2] at hge; exact absurd hge (by decide)
        · exact e1
      have F := (gp_fld hL lay).1
      have hs0 : tr.cell tt (gq s Lp Lv Ls kt m) RcptV3.sys=0 := by
        change tr.cell tt (s+(78+Vt Lp Lv Ls kt)+m) RcptV3.sys=0
        rw [F.consts m hm _ (by simp [rconsts]),hns]
      have ho := oneHot hL hq (by simp [states]) h1
      have cq := con hL hq (e:=.mul rowE (sub (c RcptV3.gq) (.mul (c ge) (Dsl.not (c RcptV3.sys))))) (mem_gs (by simp [cGas]))
      simp only [rowE,eval_mul,eval_sub,eval_not,eval_c] at cq
      rw [ho.1,ho.2 sCL (by simp [states]) (by decide),hs0,hgeq,hgeF] at cq
      have hgq : tr.cell tt (gq s Lp Lv Ls kt m) RcptV3.gq=1 := by grind
      rw [h1, hhrq, e, hgq, De m hm] at cc
      apply hD
      exact nat_of_fp (by have := Db m hm; unfold P; omega) (by unfold P; omega) (by grind)
    · exact e

end ZkFormal.NearV3.RcptV3Proof
