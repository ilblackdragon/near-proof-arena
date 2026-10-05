import ZkFormal.Near.Extract.RcptToks

/-!
# ZkFormal.Near.Extract.RcptClaimArith — claim rows: `(n−1)·G < gasLimit`, `gasBurnt = n·G`

Rows `0 … 7` (`lo8`): `y = (n−1)·G` byte-serially (`G` from the rotating
register `reg 16..23`), `gasLimit − y − 1 ≥ 0` with a borrow chain started
at `1`, and `y + G = gasBurnt` (the `tok` register holds the public bytes).
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
theorem L32_16 : ∀ i, i < 8 → L32[16 + i]? = some (k (G_LE.getD i 0)) := by decide
theorem L32_24 : ∀ i, i < 8 → L32[24 + i]? = some (Expr.pub (PV_GASLIM + i)) := by decide

theorem getElem_of_get? {l : List Expr} {j : Nat} {e : Expr} (h : l[j]? = some e) (hj : j < l.length) :
    l[j]'hj = e := by rw [List.getElem?_eq_getElem hj] at h; exact Option.some.inj h

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- A cyclically rotating claim register block. -/
theorem rot_block (col : Nat → Nat) (len : Nat) (hlen : 0 < len)
    (hmem : ∀ j, j < len → mul3 (c sCL) (Dsl.not (c fe)) (sub (n (col j)) (c (col ((j + 1) % len)))) ∈ Rcpt.constraints) :
    ∀ i, i < 12 → ∀ j, j < len → tr.cell T_RCPT i (col j) = tr.cell T_RCPT 0 (col ((j + i) % len)) := by
  obtain ⟨h13, F, -⟩ := table_of hL
  intro i
  induction i with
  | zero => intro _ j hj; simp [Nat.mod_eq_of_lt hj]
  | succ i ih =>
    intro hi j hj
    have hc : tr.cell T_RCPT i sCL = 1 := by simpa using F.st i (by omega)
    have hfe : tr.cell T_RCPT i fe = 0 := by have := F.fe i (by omega); simp at this; rw [this, if_neg (by omega)]
    have cc := con hL (r := i) (by omega) (hmem j hj)
    simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt (show i + 1 < tr.height T_RCPT by omega)] at cc
    rw [hc, hfe] at cc
    rw [show tr.cell T_RCPT (i + 1) (col j) = tr.cell T_RCPT i (col ((j + 1) % len)) by grind,
      ih (by omega) _ (Nat.mod_lt _ hlen)]
    congr 2; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; congr 1; omega

theorem claim_cols (i : Nat) (hi : i < 8) :
    tr.cell T_RCPT i (reg 16) = ((G_LE.getD i 0 : Nat) : Fp) ∧
    tr.cell T_RCPT i (reg 24) = pub.getD (PV_GASLIM + i) 0 ∧
    tr.cell T_RCPT i (tok 0) = pub.getD (PV_GAS + i) 0 := by
  have R16 := rot_block hL (fun j => reg (16 + j)) 8 (by omega) (fun j hj => mem_rg (by
    unfold cRegs; simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) i (by omega) 0 (by omega)
  have R24 := rot_block hL (fun j => reg (24 + j)) 8 (by omega) (fun j hj => mem_rg (by
    unfold cRegs; simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) i (by omega) 0 (by omega)
  have RT := rot_block hL (fun j => tok j) 8 (by omega) (fun j hj => mem_rg (by
    unfold cRegs; simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) i (by omega) 0 (by omega)
  simp only [Nat.zero_add, Nat.mod_eq_of_lt hi] at R16 R24 RT
  refine ⟨?_, ?_, ?_⟩
  · rw [R16, reg_row0 hL (16 + i) (by omega), getElem_of_get? (L32_16 i hi)]; rfl
  · rw [R24, reg_row0 hL (24 + i) (by omega), getElem_of_get? (L32_24 i hi)]; rfl
  · rw [RT]
    have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
    have hz : ((pubs PV_GAS 8 ++ ks (List.replicate 8 0))[i]'(by simp [pubs, ks]; omega), i) ∈
        (pubs PV_GAS 8 ++ ks (List.replicate 8 0)).zip (List.range 16) := by
      have : ((pubs PV_GAS 8 ++ ks (List.replicate 8 0)).zip (List.range 16))[i]'(by simp [pubs, ks]; omega) =
          ((pubs PV_GAS 8 ++ ks (List.replicate 8 0))[i]'(by simp [pubs, ks]; omega), i) := by simp
      rw [← this]; exact List.getElem_mem _
    have cc := con hL h0 (e := .mul .isFirst (sub (c (tok i)) ((pubs PV_GAS 8 ++ ks (List.replicate 8 0))[i]'(by
      simp [pubs, ks]; omega)))) (mem_rg (by
        unfold cRegs; simp only [List.mem_append]
        refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))))
        exact List.mem_map.mpr ⟨_, hz, rfl⟩))
    simp only [eval_mul, eval_isFirst, if_true, eval_sub, eval_c] at cc
    rw [show tr.cell T_RCPT 0 (tok i) = ((pubs PV_GAS 8 ++ ks (List.replicate 8 0))[i]'(by
      simp [pubs, ks]; omega)).eval tr T_RCPT 0 pub by grind]
    simp [pubs, List.getElem_append, hi]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem G_sum : sumL (fun i => G_LE.getD i 0) 8 = NearSpec.Params.G := by decide

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem claim_rowf (i : Nat) (hi : i < 8) :
    i + 1 < tr.height T_RCPT ∧ tr.cell T_RCPT i sCL = 1 ∧ tr.cell T_RCPT i lo8 = 1 ∧ tr.cell T_RCPT i fe = 0 ∧
    tr.cell T_RCPT (i + 1) lo8 = (if i = 7 then 0 else 1) := by
  obtain ⟨h13, F, -⟩ := table_of hL
  have l8 := (claim_flags hL).2
  refine ⟨by omega, by simpa using F.st i (by omega), by rw [l8 i (by omega), if_pos (by omega)], ?_, ?_⟩
  · have := F.fe i (by omega); simp at this; rw [this, if_neg (by omega)]
  · rw [l8 (i + 1) (by omega)]; split <;> split <;> first | rfl | omega

theorem cv_lt_of {q x : Nat} {v : Nat} (h : tr.cell T_RCPT q x = ((v : Nat) : Fp)) (hv : v < P) : cv tr T_RCPT q x = v := by
  rw [cv, h, toNat_natCast, Nat.mod_eq_of_lt hv]

/-- Claim-row carry chain: generic form. -/
theorem claim_links (cin : Nat) (E : Expr) (cout : Nat → Nat) (hb : ∀ i, i < 8 → cout i < 4096)
    (hE : ∀ i, i < 8 → E.eval tr T_RCPT i pub = ((cout i : Nat) : Fp))
    (m1 : Expr.mul (mul3 cl (c lo8) (Dsl.not (c fe))) (sub (n cin) E) ∈ Rcpt.constraints) :
    ∀ i, i + 1 < 8 → cv tr T_RCPT (i + 1) cin = cout i := by
  intro i hi
  obtain ⟨hn, hc, hl, hfe, -⟩ := claim_rowf hL i (by omega)
  have cc := con hL (r := i) (by omega) m1
  simp only [cl, eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hn] at cc
  rw [hc, hl, hfe, hE i (by omega)] at cc
  exact cv_lt_of hL (by grind) (by have := hb i (by omega); unfold P; omega)

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem cbits (i : Nat) (hi : i < 8) (off len : Nat) (hl : off + len ≤ 66) :
    (bitsX off len).eval tr T_RCPT i pub = ((bvN tr i off len : Nat) : Fp) ∧ bvN tr i off len < 2 ^ len :=
  bitsX_eval hL (by have := (claim_rowf hL i hi).1; omega) off len hl

theorem cxb (i : Nat) (hi : i < 8) (j : Nat) (hj : j < 66) : cv tr T_RCPT i (xb j) ≤ 1 :=
  cv_bool (xb_bool hL (by have := (claim_rowf hL i hi).1; omega) j hj)

theorem cfirst (x v : Nat) (hm : Expr.mul .isFirst (sub (c x) (k v)) ∈ Rcpt.constraints) (hv : v < P) :
    cv tr T_RCPT 0 x = v := by
  have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
  have cc := con hL h0 hm
  simp only [eval_mul, eval_isFirst, if_true, eval_sub, eval_c, eval_k] at cc
  exact cv_lt_of hL (by grind) hv

theorem clast (E : Expr) (v : Nat) (hm : Expr.mul (mul3 cl (c lo8) (Dsl.not (n lo8))) E ∈ Rcpt.constraints)
    (hE : E.eval tr T_RCPT 7 pub = ((v : Nat) : Fp)) (hv : v < P) : v = 0 := by
  obtain ⟨hn, hc, hl, -, hl1⟩ := claim_rowf hL 7 (by omega)
  have cc := con hL (r := 7) (by omega) hm
  simp only [cl, eval_mul, eval_mul3, eval_c, eval_not, eval_n, nxt hn] at cc
  rw [hc, hl, hl1, if_pos rfl, hE] at cc
  exact nat_of_fp hv (by unfold P; omega) (by grind)

/-- **The claim's gas facts.** -/
theorem gas_ok {rcs : List RS} (S : Shape tr rcs) (hb : ∀ j, j < 309 → pubNat pub j < 256) :
    (rcs.length - 1) * NearSpec.Params.G < leN' (pubBytes pub PV_GASLIM 8) ∧
    leN' (pubBytes pub PV_GAS 8) = rcs.length * NearSpec.Params.G := by
  have hn : 0 < rcs.length := by have := S.ne; cases rcs <;> simp_all
  have hlen := len_lt hL S
  have hH := height_le hL
  -- n − 1 in the field
  have hN : (nPubE).eval tr T_RCPT 0 pub = ((rcs.length : Nat) : Fp) := (last_facts hL S).1.symm
  have hm1 : ∀ i, m1E.eval tr T_RCPT i pub = (((rcs.length - 1 : Nat) : Nat) : Fp) := by
    intro i
    have : (nPubE).eval tr T_RCPT i pub = (nPubE).eval tr T_RCPT 0 pub := by simp [nPubE, leE4]
    simp only [m1E, eval_sub, eval_k, this, hN]
    rw [natCast_sub' _ _ hn]
  have Gb : ∀ i, i < 8 → G_LE.getD i 0 < 256 := by decide
  -- y = (n − 1)·G
  have yC : ∀ i, i < 8 → bvN tr i 8 8 < 256 := fun i hi => (cbits hL i hi 8 8 (by omega)).2
  have y0 : cv tr T_RCPT 0 c1 = 0 := by
    have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
    have cc := con hL h0 (e := .mul .isFirst (c c1)) (mem_cl (by simp [cClaim]))
    simp only [eval_mul, eval_isFirst, if_true, eval_c] at cc
    exact cv_lt_of hL (v := 0) (by grind) (by unfold P; omega)
  have yl := claim_links hL c1 (bitsX 8 8) (fun i => bvN tr i 8 8) (fun i hi => by have := yC i hi; omega)
    (fun i hi => (cbits hL i hi 8 8 (by omega)).1) (mem_cl (by simp [cClaim]))
  have yc : ∀ i, i < 8 → cv tr T_RCPT i c1 < 256 := by
    intro i hi; cases i with
    | zero => rw [y0]; omega
    | succ i => rw [yl i hi]; exact yC i (by omega)
  have yrow : ∀ i, i < 8 → bvN tr i 0 8 + 256 * bvN tr i 8 8 = (rcs.length - 1) * G_LE.getD i 0 + cv tr T_RCPT i c1 := by
    intro i hi
    obtain ⟨-, hc, hl, -⟩ := claim_rowf hL i hi
    have cc := con hL (r := i) (by omega) (e := mul3 cl (c lo8) (sub (.add (.mul m1E (c (reg 16))) (c c1))
      (.add (bitsX 0 8) (smul 256 (bitsX 8 8))))) (mem_cl (by simp [cClaim]))
    simp only [cl, eval_mul3, eval_mul, eval_c, eval_sub, eval_add, eval_smul] at cc
    rw [hc, hl, hm1 i, (claim_cols hL i hi).1, (cbits hL i hi 0 8 (by omega)).1, (cbits hL i hi 8 8 (by omega)).1,
      cast_cv tr _ c1] at cc
    have := (cbits hL i hi 0 8 (by omega)).2; have := yC i hi; have := yc i hi; have := Gb i hi
    have : (rcs.length - 1) * G_LE.getD i 0 ≤ 2 ^ 18 * 255 := Nat.mul_le_mul (by omega) (by omega)
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  have yf := clast hL (bitsX 8 8) (bvN tr 7 8 8) (mem_cl (by simp [cClaim])) (cbits hL 7 (by omega) 8 8 (by omega)).1
    (by have := yC 7 (by omega); unfold P; omega)
  have hy := chain 8 (by omega) (fun i => bvN tr i 0 8) (fun i => (rcs.length - 1) * G_LE.getD i 0)
    (fun i => cv tr T_RCPT i c1) (fun i => bvN tr i 8 8) yrow y0 yl
  simp only [show 8 - 1 = 7 from rfl, yf, Nat.mul_zero, Nat.add_zero] at hy
  have hyG : sumL (fun i => bvN tr i 0 8) 8 = (rcs.length - 1) * NearSpec.Params.G := by
    rw [hy, ← G_sum]
    have gen : ∀ (a : Nat) (f : Nat → Nat) (L : Nat), sumL (fun i => a * f i) L = a * sumL f L := by
      intro a f L; induction L with
      | zero => rfl
      | succ L ih => simp only [sumL]; rw [ih, Nat.mul_add, Nat.mul_left_comm]
    exact gen _ _ 8
  have pub8 : ∀ off, off + 8 ≤ 309 → leN' (pubBytes pub off 8) = sumL (fun i => pubNat pub (off + i)) 8 := by
    intro off ho
    rw [leN', pubBytes, le256_eq_leNat _ (fun y hy => by
      simp only [List.mem_map, List.mem_range] at hy; obtain ⟨k, hk, rfl⟩ := hy; exact hb _ (by omega)),
      le256_map_range]
  -- gasLimit
  have glrow : ∀ i, i < 8 → cv tr T_RCPT i c2 ≤ 1 →
      pubNat pub (PV_GASLIM + i) + 256 * cv tr T_RCPT i (xb 24) = (bvN tr i 0 8 + bvN tr i 16 8) + cv tr T_RCPT i c2 := by
    intro i hi hc2
    obtain ⟨-, hc, hl, -⟩ := claim_rowf hL i hi
    have cc := con hL (r := i) (by omega) (e := mul3 cl (c lo8) (sub (sub (c (reg 24)) (bitsX 0 8))
      (sub (.add (c c2) (bitsX 16 8)) (smul 256 (c (xb 24)))))) (mem_cl (by simp [cClaim]))
    simp only [cl, eval_mul3, eval_c, eval_sub, eval_add, eval_smul] at cc
    rw [hc, hl, (claim_cols hL i hi).2.1, pub_eq_cast, (cbits hL i hi 0 8 (by omega)).1,
      (cbits hL i hi 16 8 (by omega)).1, cast_cv tr _ c2, cast_cv tr _ (xb 24)] at cc
    have := (cbits hL i hi 0 8 (by omega)).2; have := (cbits hL i hi 16 8 (by omega)).2
    have := cxb hL i hi 24 (by omega); have := hb (PV_GASLIM + i) (by unfold PV_GASLIM; omega)
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  have g0 := cfirst hL c2 1 (mem_cl (by simp [cClaim])) (by unfold P; omega)
  have gl := claim_links hL c2 (c (xb 24)) (fun i => cv tr T_RCPT i (xb 24))
    (fun i hi => by have := cxb hL i hi 24 (by omega); omega) (fun i hi => by simp only [eval_c]; exact cast_cv tr _ _)
    (mem_cl (by simp [cClaim]))
  have gc : ∀ i, i < 8 → cv tr T_RCPT i c2 ≤ 1 := by
    intro i hi; cases i with
    | zero => rw [g0]; omega
    | succ i => rw [gl i hi]; exact cxb hL i (by omega) 24 (by omega)
  have gf := clast hL (c (xb 24)) (cv tr T_RCPT 7 (xb 24)) (mem_cl (by simp [cClaim])) (by simp only [eval_c]; exact cast_cv tr _ _)
    (by have := cxb hL 7 (by omega) 24 (by omega); unfold P; omega)
  have hg := chainC 8 (by omega) (fun i => pubNat pub (PV_GASLIM + i)) (fun i => bvN tr i 0 8 + bvN tr i 16 8)
    (fun i => cv tr T_RCPT i c2) (fun i => cv tr T_RCPT i (xb 24)) (fun i hi => glrow i hi (gc i hi)) gl
  simp only [show 8 - 1 = 7 from rfl, gf, Nat.mul_zero, Nat.add_zero, g0, sumL_add] at hg
  -- gasBurnt
  have brow : ∀ i, i < 8 → cv tr T_RCPT i c3 ≤ 1 →
      pubNat pub (PV_GAS + i) + 256 * cv tr T_RCPT i (xb 25) = (bvN tr i 0 8 + G_LE.getD i 0) + cv tr T_RCPT i c3 := by
    intro i hi hc3
    obtain ⟨-, hc, hl, -⟩ := claim_rowf hL i hi
    have cc := con hL (r := i) (by omega) (e := mul3 cl (c lo8) (sub (sum [bitsX 0 8, c (reg 16), c c3])
      (.add (c (tok 0)) (smul 256 (c (xb 25)))))) (mem_cl (by simp [cClaim]))
    simp only [cl, eval_mul3, eval_c, eval_sub, eval_add, eval_smul, eval_sum_cons, eval_sum_nil] at cc
    rw [hc, hl, (claim_cols hL i hi).1, (claim_cols hL i hi).2.2, pub_eq_cast, (cbits hL i hi 0 8 (by omega)).1,
      cast_cv tr _ c3, cast_cv tr _ (xb 25)] at cc
    have := (cbits hL i hi 0 8 (by omega)).2; have := Gb i hi
    have := cxb hL i hi 25 (by omega); have := hb (PV_GAS + i) (by unfold PV_GAS; omega)
    apply nat_of_fp (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul]; grind
  have b0 : cv tr T_RCPT 0 c3 = 0 := by
    have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
    have cc := con hL h0 (e := .mul .isFirst (c c3)) (mem_cl (by simp [cClaim]))
    simp only [eval_mul, eval_isFirst, if_true, eval_c] at cc
    exact cv_lt_of hL (v := 0) (by grind) (by unfold P; omega)
  have bl := claim_links hL c3 (c (xb 25)) (fun i => cv tr T_RCPT i (xb 25))
    (fun i hi => by have := cxb hL i hi 25 (by omega); omega) (fun i hi => by simp only [eval_c]; exact cast_cv tr _ _)
    (mem_cl (by simp [cClaim]))
  have bc : ∀ i, i < 8 → cv tr T_RCPT i c3 ≤ 1 := by
    intro i hi; cases i with
    | zero => rw [b0]; omega
    | succ i => rw [bl i hi]; exact cxb hL i (by omega) 25 (by omega)
  have bf := clast hL (c (xb 25)) (cv tr T_RCPT 7 (xb 25)) (mem_cl (by simp [cClaim])) (by simp only [eval_c]; exact cast_cv tr _ _)
    (by have := cxb hL 7 (by omega) 25 (by omega); unfold P; omega)
  have hbu := chain 8 (by omega) (fun i => pubNat pub (PV_GAS + i)) (fun i => bvN tr i 0 8 + G_LE.getD i 0)
    (fun i => cv tr T_RCPT i c3) (fun i => cv tr T_RCPT i (xb 25)) (fun i hi => brow i hi (bc i hi)) b0 bl
  simp only [show 8 - 1 = 7 from rfl, bf, Nat.mul_zero, Nat.add_zero, sumL_add, G_sum] at hbu
  rw [pub8 PV_GASLIM (by decide), pub8 PV_GAS (by decide)]
  constructor
  · rw [← hyG]; omega
  · rw [hbu, hyG]
    obtain ⟨m, hm⟩ : ∃ m, rcs.length = m + 1 := ⟨rcs.length - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, Nat.succ_mul]

end ZkFormal.Near.RcptProof
