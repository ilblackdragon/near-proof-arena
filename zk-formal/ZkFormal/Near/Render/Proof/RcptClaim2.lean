import ZkFormal.Near.Render.Proof.RcptClaim1

/-!
# ZkFormal.Near.Render.Proof.RcptClaim2 — `cClaim` on the honest rows; `claimFam : FamOk cClaim`

The public-only checks (claim prefix, `n ≤ 256`, `nref < 2^16`) hold on every
row; the claim-row checks (`n ≥ 1`, lanes, `y = (n − 1)·G`, `gasLimit − y − 1 ≥ 0`,
`y + G = gasBurnt`) on the claim rows; the rest vanish (`sCL`, `isFirst`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen

def qP : List Expr := (claimPrefix.zip (List.range 77)).map fun (x, j) => sub (.pub j) (k x.toNat)
def qN : List Expr :=
  [ .pub (PV_N + 2), .pub (PV_N + 3), Dsl.bool (.pub (PV_N + 1)), .mul (.pub (PV_N + 1)) (.pub PV_N),
    .pub (PV_NREF + 2), .pub (PV_NREF + 3) ]
def qR : List Expr :=
  let cl := c Rcpt.sCL
  [ .mul .isFirst (sub (.mul (.add (.pub PV_N) (.pub (PV_N + 1))) (c Rcpt.invA)) (k 1)),
    .mul .isFirst (Dsl.not (c Rcpt.lo8)), .mul .isFirst (Dsl.not (c Rcpt.lo4)),
    .mul (mul3 cl (Dsl.not (c Rcpt.fe)) (n Rcpt.lo8)) (Dsl.not (c Rcpt.lo8)),
    .mul (mul3 cl (Dsl.not (c Rcpt.fe)) (n Rcpt.lo4)) (Dsl.not (c Rcpt.lo4)),
    .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (n Rcpt.lo8))) (sub (c Rcpt.idx) (k 7)),
    .mul (mul3 cl (c Rcpt.lo4) (Dsl.not (n Rcpt.lo4))) (sub (c Rcpt.idx) (k 3)),
    mul3 cl (c Rcpt.fe) (c Rcpt.lo8), mul3 cl (c Rcpt.fe) (c Rcpt.lo4),
    mul3 cl (c Rcpt.lo8) (sub (.add (.mul Rcpt.m1E (c (Rcpt.reg 16))) (c Rcpt.c1))
      (.add (Rcpt.bitsX 0 8) (smul 256 (Rcpt.bitsX 8 8)))),
    .mul .isFirst (c Rcpt.c1), .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (c Rcpt.fe))) (sub (n Rcpt.c1) (Rcpt.bitsX 8 8)),
    .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (n Rcpt.lo8))) (Rcpt.bitsX 8 8),
    mul3 cl (c Rcpt.lo8) (sub (sub (c (Rcpt.reg 24)) (Rcpt.bitsX 0 8))
      (sub (.add (c Rcpt.c2) (Rcpt.bitsX 16 8)) (smul 256 (c (Rcpt.xb 24))))),
    .mul .isFirst (sub (c Rcpt.c2) (k 1)), .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (c Rcpt.fe))) (sub (n Rcpt.c2) (c (Rcpt.xb 24))),
    .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (n Rcpt.lo8))) (c (Rcpt.xb 24)),
    mul3 cl (c Rcpt.lo8) (sub (sum [Rcpt.bitsX 0 8, c (Rcpt.reg 16), c Rcpt.c3]) (.add (c (Rcpt.tok 0)) (smul 256 (c (Rcpt.xb 25))))),
    .mul .isFirst (c Rcpt.c3), .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (c Rcpt.fe))) (sub (n Rcpt.c3) (c (Rcpt.xb 25))),
    .mul (mul3 cl (c Rcpt.lo8) (Dsl.not (n Rcpt.lo8))) (c (Rcpt.xb 25)) ]

theorem cClaim_eq : Rcpt.cClaim = qP ++ qN ++ qR := rfl

theorem nPubE_eq : Rcpt.nPubE = sum [smul 1 (.pub 149), smul 256 (.pub 150), smul 65536 (.pub 151),
    smul 16777216 (.pub 152)] := rfl

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem nbytes : pubNat (publicOf c) PV_N + 256 * pubNat (publicOf c) (PV_N + 1) +
    65536 * pubNat (publicOf c) (PV_N + 2) + 16777216 * pubNat (publicOf c) (PV_N + 3) = c.1.receiptCount ∧
    pubNat (publicOf c) (PV_N + 2) = 0 ∧ pubNat (publicOf c) (PV_N + 3) = 0 ∧
    pubNat (publicOf c) (PV_N + 1) ≤ 1 ∧
    pubNat (publicOf c) PV_N = c.1.receiptCount % 256 ∧ pubNat (publicOf c) (PV_N + 1) = c.1.receiptCount / 256 := by
  have h0 := pubN (e := e) hg (k := 0) (by decide); have h1 := pubN (e := e) hg (k := 1) (by decide)
  have h2 := pubN (e := e) hg (k := 2) (by decide); have h3 := pubN (e := e) hg (k := 3) (by decide)
  simp only [leBytes_getD, show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide,
    show (3 : Nat) < 4 by decide, ↓reduceIte, Nat.pow_zero, Nat.pow_one, Nat.div_one,
    show (256 : Nat) ^ 2 = 65536 from rfl, show (256 : Nat) ^ 3 = 16777216 from rfl, Nat.add_zero] at h0 h1 h2 h3
  have := n_lt hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem qPN_ok : ∀ x ∈ qP ++ qN, ∀ (cur nx : Nat → Fp) (fst lst : Bool), evR cur nx fst lst (publicOf c) x = 0 := by
  intro x hx cur nx fst lst
  simp only [List.mem_append] at hx
  rcases hx with hP | hN
  · simp only [qP, List.mem_map] at hP
    obtain ⟨⟨y, j⟩, hy, rfl⟩ := hP
    obtain ⟨hj, rfl⟩ := mem_zip_range' (by rw [claimPrefix_length]; rfl) hy
    have hj' : j < 77 := by rw [claimPrefix_length] at hj; exact hj
    simp only [evR_sub, evR_pub, evR_k, pubF c e, pub_prefix hg hj', natCast_eq,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    grind
  · obtain ⟨_, n2, n3, n1, b0, b1⟩ := nbytes (e := e) hg
    have r2 := pubNref (e := e) hg (k := 2) (by decide); have r3 := pubNref (e := e) hg (k := 3) (by decide)
    have := nref_le hg
    simp only [leBytes_getD, show (2 : Nat) < 4 by decide, show (3 : Nat) < 4 by decide, ↓reduceIte,
      show (256 : Nat) ^ 2 = 65536 from rfl, show (256 : Nat) ^ 3 = 16777216 from rfl] at r2 r3
    simp only [qN, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [evR_pub, pubF c e, n2, ofNat0]
    · simp only [evR_pub, pubF c e, n3, ofNat0]
    · simp only [evR_bool, evR_pub, pubF c e]; exact bool_of_le n1
    · simp only [evR_mul, evR_pub, pubF c e, ← ofNat_mul_e]
      have := n_lt hg
      rw [show pubNat (publicOf c) (PV_N + 1) * pubNat (publicOf c) PV_N = 0 by
        rw [b0, b1]; rcases (show c.1.receiptCount = 256 ∨ c.1.receiptCount < 256 by omega) with h | h
        · rw [h]
        · rw [Nat.div_eq_of_lt h, Nat.zero_mul]]
      rfl
    · simp only [evR_pub, pubF c e, r2, Nat.div_eq_of_lt (show c.1.refundCount < 65536 by omega), Nat.zero_mod, ofNat0]
    · simp only [evR_pub, pubF c e, r3, Nat.div_eq_of_lt (show c.1.refundCount < 16777216 by omega), Nat.zero_mod,
        ofNat0]

theorem nPub_eval {cur nx : Nat → Fp} {fst lst : Bool} :
    evR cur nx fst lst (publicOf c) Rcpt.nPubE = Fp.ofNat c.1.receiptCount := by
  obtain ⟨hn, -⟩ := nbytes (e := e) hg
  rw [← hn, nPubE_eq]
  simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_pub, pubF c e, natCast_eq, ofNat_add_e, ofNat_mul_e]
  simp only [PV_N, ofNat1]; grind

end

/-! ## Claim-row cells -/

section
variable {c : Claim} {e : Ext} {i : Nat}

theorem bitsX_cl {off len X : Nat} {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp}
    (hv : ∀ j, j < len → Cc c e (.cl i) (Rcpt.xb (off + j)) = bitOf X j) (hX : X < 2 ^ len) :
    evR (cF c e (.cl i)) nx fst lst pub (Rcpt.bitsX off len) = Fp.ofNat X := by
  rw [evR_bitsX (v := fun j => Cc c e (.cl i) (Rcpt.xb j)) off len (fun j _ _ => rfl)]
  rw [bitsVal_pool hv hX]

end

section
variable {c : WfClaim} {e : Ext} {i : Nat}

theorem clc_reg16 : cF c.1 e (.cl i) (Rcpt.reg 16) = Fp.ofNat (Rcpt.G_LE.getD (i % 8) 0) := by
  have := cl_G (c := c) (e := e) (i := i) (j := 0) (by decide); simpa using this
theorem clc_reg24 : cF c.1 e (.cl i) (Rcpt.reg 24) = Fp.ofNat ((Cl.D (PA c.1 e)).getD (i % 8) 0) := by
  have := cl_D (c := c) (e := e) (i := i) (j := 0) (by decide); simpa using this
theorem clc_tok0 : cF c.1 e (.cl i) (Rcpt.tok 0) = Fp.ofNat ((Cl.T (PA c.1 e)).getD (i % 8) 0) := by
  have := cl_T (c := c) (e := e) (i := i) (j := 0) (by decide); simpa using this
theorem clc_c1 : cF c.1 e (.cl i) Rcpt.c1 = Fp.ofNat (if i < 8 then chain (Cl.x1 (PA c.1 e)) i else 0) := by
  simp only [cF, L_c1]
theorem clc_c2 : cF c.1 e (.cl i) Rcpt.c2 = Fp.ofNat (if i < 8 then Cl.br (PA c.1 e) i else 0) := by
  simp only [cF, L_c2]
theorem clc_c3 : cF c.1 e (.cl i) Rcpt.c3 = Fp.ofNat (if i < 8 then chain (Cl.x3 (PA c.1 e)) i else 0) := by
  simp only [cF, L_c3]

end

/-- **`qR` on a claim row.** -/
theorem qR_cl {c : WfClaim} {e : Ext} (hg : Good c.1 e) {i : Nat} (hi : i < 12) {nx : Nat → Fp}
    (hn : i < 11 → nx = cF c.1 e (.cl (i + 1))) :
    ∀ x ∈ qR, evR (cF c.1 e (.cl i)) nx (decide (i = 0)) false (publicOf c) x = 0 := by
  have hcl : cF c.1 e (.cl i) Rcpt.sCL = 1 := by simp only [cF, L_sCL]; rfl
  have hlo8 : cF c.1 e (.cl i) Rcpt.lo8 = if i < 8 then 1 else 0 := by
    simp only [cF, L_lo8]; by_cases h : i < 8 <;> simp [h, b2n] <;> rfl
  have hlo4 : cF c.1 e (.cl i) Rcpt.lo4 = if i < 4 then 1 else 0 := by
    simp only [cF, L_lo4]; by_cases h : i < 4 <;> simp [h, b2n] <;> rfl
  have hfe : cF c.1 e (.cl i) Rcpt.fe = if i = 11 then 1 else 0 := by
    simp only [cF, L_fe]; by_cases h : i = 11 <;> simp [h, b2n] <;> rfl
  have hidx : cF c.1 e (.cl i) Rcpt.idx = Fp.ofNat i := by simp only [cF, L_idx]
  have hlo8n : i < 11 → nx Rcpt.lo8 = if i + 1 < 8 then 1 else 0 := by
    intro h; rw [hn h]; simp only [cF, L_lo8]; by_cases h' : i + 1 < 8 <;> simp [h', b2n] <;> rfl
  have hlo4n : i < 11 → nx Rcpt.lo4 = if i + 1 < 4 then 1 else 0 := by
    intro h; rw [hn h]; simp only [cF, L_lo4]; by_cases h' : i + 1 < 4 <;> simp [h', b2n] <;> rfl
  have hn1 : i < 11 → nx Rcpt.c1 = Fp.ofNat (if i + 1 < 8 then chain (Cl.x1 (PA c.1 e)) (i + 1) else 0) := by
    intro h; rw [hn h, clc_c1]
  have hn2 : i < 11 → nx Rcpt.c2 = Fp.ofNat (if i + 1 < 8 then Cl.br (PA c.1 e) (i + 1) else 0) := by
    intro h; rw [hn h, clc_c2]
  have hn3 : i < 11 → nx Rcpt.c3 = Fp.ofNat (if i + 1 < 8 then chain (Cl.x3 (PA c.1 e)) (i + 1) else 0) := by
    intro h; rw [hn h, clc_c3]
  have hP := Link.wf_bounds c
  have h4096 : 4096 < ZkFormal.Algebra.P := by decide
  intro x hx
  simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases (show i < 8 ∨ 8 ≤ i by omega) with h8 | h8
  · -- lanes on
    have hm : i % 8 = i := Nat.mod_eq_of_lt h8
    have hA : ∀ {nx' : Nat → Fp} {f : Bool}, evR (cF c.1 e (.cl i)) nx' f false (publicOf c) (Rcpt.bitsX 0 8) =
        Fp.ofNat ((Cl.yB (PA c.1 e)).getD i 0) := by
      intro nx' f
      rw [bitsX_cl (X := Cl.sy (PA c.1 e) i % 256) (fun j hj => by rw [Nat.zero_add, L_xbA _ _ _ hj, if_pos h8])
        (Nat.mod_lt _ (by decide)), sy_mod hg h8]
    have hB : ∀ {nx' : Nat → Fp} {f : Bool}, evR (cF c.1 e (.cl i)) nx' f false (publicOf c) (Rcpt.bitsX 8 8) =
        Fp.ofNat (chain (Cl.x1 (PA c.1 e)) (i + 1)) := by
      intro nx' f
      rw [bitsX_cl (X := Cl.sy (PA c.1 e) i / 256) (fun j hj => by rw [L_xbB _ _ _ hj, if_pos h8])
        (by rw [sy_div hg]; have := cy_le hg (i + 1); omega), sy_div hg]
    have hC : ∀ {nx' : Nat → Fp} {f : Bool}, evR (cF c.1 e (.cl i)) nx' f false (publicOf c) (Rcpt.bitsX 16 8) =
        Fp.ofNat (Cl.dv (PA c.1 e) i) := by
      intro nx' f
      rw [bitsX_cl (X := Cl.dv (PA c.1 e) i) (fun j hj => by rw [L_xbC _ _ _ hj, if_pos h8]) (dv_lt hg i)]
    have h24 : cF c.1 e (.cl i) (Rcpt.xb 24) = Fp.ofNat (Cl.br (PA c.1 e) (i + 1)) := by
      simp only [cF, L_xb24, if_pos h8, bitOf_small (br_le hg _)]
    have h25 : cF c.1 e (.cl i) (Rcpt.xb 25) = Fp.ofNat (chain (Cl.x3 (PA c.1 e)) (i + 1)) := by
      simp only [cF, L_xb25, if_pos h8, sg_div hg, bitOf_small (cg_le hg _)]
    have hi11 : i < 11 := by omega
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    -- n ≥ 1
    · simp only [evR_mul, evR_sub, evR_add, evR_c, evR_k, evR_isFirst, evR_pub, pubF c e]
      by_cases h0 : i = 0
      · subst h0
        obtain ⟨hn', n2, n3, n1, b0, b1⟩ := nbytes (e := e) hg
        have hpos := hg.n_pos
        simp only [decide_true, ↓reduceIte, cF, L_invA, PA_pubNat]
        rw [← ofNat_add_e, ofNat_invP (ofNat_ne_zero (by omega) (by rw [P_def]; omega))]
        simp only [natCast_eq, ofNat1]; grind
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx]
      by_cases h0 : i = 0
      · subst h0; simp; grind
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, show ¬ i = 11 by omega, ↓reduceIte]
      by_cases h4 : i < 4
      · simp only [h4, ↓reduceIte]; grind
      · simp only [h4, ↓reduceIte, hlo4n hi11, show ¬ (i + 1 < 4) by omega]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, hlo8n hi11]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, natCast_eq, Nat.lt_irrefl]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, hlo4n hi11]
      by_cases h4 : i < 4
      · by_cases h3 : i + 1 < 4
        · simp only [h4, h3, ↓reduceIte]; grind
        · rw [show i = 3 by omega]; simp only [↓reduceIte, natCast_eq]; grind
      · simp only [h4, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, show ¬ i = 11 by omega, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, show ¬ i = 11 by omega, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, Rcpt.m1E, nPub_eval hg, clc_reg16, hm, clc_c1, hA, hB]
      have E := fp_eq (chain_step (Cl.x1 (PA c.1 e)) i)
      have E2 := sy_mod hg h8
      simp only [Cl.sy] at E2
      rw [E2] at E
      simp only [Cl.x1, cl_n hg, ofNat_add_e, ofNat_mul_e, ofNat_sub (show 1 ≤ c.1.receiptCount from hg.n_pos)] at E
      simp only [natCast_eq, ofNat1] at E ⊢; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, clc_c1]
      by_cases h0 : i = 0
      · subst h0; simp [chain, ofNat0]; grind
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, show ¬ i = 11 by omega, ↓reduceIte, hn1 hi11, hB]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, cy_final hg, ofNat0]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, hlo8n hi11, hB]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, cy_final hg, ofNat0]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, clc_reg24, hm, hA, clc_c2, hC, h24]
      have E := fp_eq (br_step hg i)
      simp only [ofNat_add_e, ofNat_mul_e] at E
      simp only [natCast_eq] at E ⊢; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, clc_c2]
      by_cases h0 : i = 0
      · subst h0; simp only [decide_true, ↓reduceIte, show (0 : Nat) < 8 by decide, show Cl.br (PA c.1 e) 0 = 1 from rfl,
          natCast_eq, ofNat1]; grind
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, show ¬ i = 11 by omega, ↓reduceIte, hn2 hi11, h24]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, br_final hg, ofNat0]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, hlo8n hi11, h24]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, br_final hg, ofNat0]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, hA, clc_reg16, hm, clc_c3, clc_tok0, h25]
      have E := fp_eq (chain_step (Cl.x3 (PA c.1 e)) i)
      have E2 := sg_mod hg h8
      simp only [Cl.sg] at E2
      rw [E2] at E
      simp only [Cl.x3, ofNat_add_e, ofNat_mul_e] at E
      simp only [natCast_eq] at E ⊢; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, clc_c3]
      by_cases h0 : i = 0
      · subst h0; simp [chain, ofNat0]; grind
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, show ¬ i = 11 by omega, ↓reduceIte, hn3 hi11, h25]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, cg_final hg, ofNat0]; grind
    · simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, if_pos h8, hlo8n hi11, h25]
      by_cases h7 : i + 1 < 8
      · simp only [h7, ↓reduceIte]; grind
      · rw [show i = 7 by omega]; simp only [↓reduceIte, Nat.lt_irrefl, cg_final hg, ofNat0]; grind
  · -- lanes off
    have h0 : decide (i = 0) = false := by simp; omega
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp only [evR_mul, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, evR_smul, evR_isFirst, evR_sum_cons, evR_sum_nil, hcl, hlo8, hlo4, hfe, hidx, h0, Bool.false_eq_true, ↓reduceIte, show ¬ i < 8 by omega, show ¬ i < 4 by omega]
    all_goals first
      | grind
      | (by_cases h11 : i = 11
         · simp only [h11, ↓reduceIte]; grind
         · simp only [hlo8n (by omega), hlo4n (by omega), show ¬ (i + 1 < 8) by omega, show ¬ (i + 1 < 4) by omega,
             ↓reduceIte, h11]; grind)

set_option maxRecDepth 100000 in
theorem qR_zr : qR.all (Zr (fun x => x == Rcpt.sCL) (fun _ => false) true) = true := by decide

/-- **`cClaim` on the honest rows.** -/
theorem claimFam : FamOk Rcpt.cClaim := by
  intro c e hg _
  have zr : ∀ x ∈ qR, Zr (fun x => x == Rcpt.sCL) (fun _ => false) true x = true :=
    fun x hx => List.all_eq_true.1 qR_zr x hx
  have mem : ∀ x ∈ Rcpt.cClaim, x ∈ qP ++ qN ∨ x ∈ qR := by
    intro x hx; rw [cClaim_eq, List.mem_append] at hx; exact hx
  have segR : ∀ r s i, ∀ {nx : Nat → Fp}, ∀ x ∈ Rcpt.cClaim,
      evR (cF c.1 e (.seg r s i)) nx false false (publicOf c) x = 0 := by
    intro r s i nx x hx
    rcases mem x hx with h | h
    · exact qPN_ok hg x h _ _ _ _
    · exact Zr_sound (z := fun x => x == Rcpt.sCL) (zn := fun _ => false) (f0 := true)
        (fun y hy => by simp only [beq_iff_eq] at hy; subst hy; exact cF_sCL)
        (fun _ h => by cases h) (fun _ => rfl) x (zr x h)
  apply fam_of hg
  · intro i hi x hx
    rcases mem x hx with h | h
    · exact qPN_ok hg x h _ _ _ _
    · exact qR_cl hg hi (fun h' => by simp [nextOf, h']) x h
  · intro r s i _ _ _; exact segR r s i
  · intro r s i _ _ _ _; exact segR r s i
  · intro r s i _ _ _ _; exact segR r s i
  · obtain ⟨r, s, i, he, -⟩ := lastRec_facts hg
    rw [he]; exact segR r s i
  · intro x hx
    rcases mem x hx with h | h
    · exact qPN_ok hg x h _ _ _ _
    · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h)
        (Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => h) (zr x h))
  · intro x hx
    rcases mem x hx with h | h
    · exact qPN_ok hg x h _ _ _ _
    · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h)
        (Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => h) (zr x h))

end RcptP

end ZkFormal.Near.Render
