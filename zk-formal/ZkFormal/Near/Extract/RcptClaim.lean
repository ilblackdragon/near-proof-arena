import ZkFormal.Near.Extract.RcptDig

/-!
# ZkFormal.Near.Extract.RcptClaim — the claim rows and the padding rows

Claim rows `0 … 11`: rotating registers (`reg 0` runs over `shard ‖ n`,
`reg 12` over `nref`), lane flags `lo4`, `lo8`; their only messages are the
`RC`/`RF` headers.  Padding rows send nothing.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- A boolean flag that is `1` on a prefix `0 … m` of rows `0 … N−1`. -/
theorem step_flag (g : Nat → Fp) (m N : Nat) (hm : m + 1 < N) (hb : ∀ i, i < N → g i = 0 ∨ g i = 1)
    (h0 : g 0 = 1) (hmono : ∀ i, i + 1 < N → g (i + 1) = 1 → g i = 1)
    (hdrop : ∀ i, i + 1 < N → g i = 1 → g (i + 1) = 0 → i = m) (hlast : g (N - 1) = 0) :
    ∀ i, i < N → g i = if i ≤ m then 1 else 0 := by
  have up : ∀ i, i ≤ m → g i = 1 := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ i ih =>
      intro hi
      rcases hb (i + 1) (by omega) with h | h
      · exact absurd (hdrop i (by omega) (ih (by omega)) h) (by omega)
      · exact h
  have hm1 : g (m + 1) = 0 := by
    rcases hb (m + 1) hm with h | h
    · exact h
    · exfalso
      have : ∀ i, m + 1 ≤ i → i < N → g i = 1 := by
        intro i h1 h2
        induction i with
        | zero => omega
        | succ i ih =>
          rcases Nat.lt_or_ge i (m + 1) with h' | h'
          · have : i = m := by omega
            subst this; exact h
          · rcases hb (i + 1) h2 with h0' | h0'
            · exact absurd (hdrop i h2 (ih h' (by omega)) h0') (by omega)
            · exact h0'
      have := this (N - 1) (by omega) (by omega)
      rw [hlast] at this; exact fp_zero_ne_one this
  have down : ∀ i, m + 1 ≤ i → i < N → g i = 0 := by
    intro i h1 h2
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.lt_or_ge i (m + 1) with h' | h'
      · have : i = m := by omega
        subst this; exact hm1
      · rcases hb (i + 1) h2 with h0' | h0'
        · exact h0'
        · have := hmono i h2 h0'; rw [ih h' (by omega)] at this; exact absurd this fp_zero_ne_one
  intro i hi
  split
  · exact up i (by omega)
  · exact down i (by omega) hi

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem claim_flags :
    (∀ i, i < 12 → tr.cell T_RCPT i lo4 = if i ≤ 3 then 1 else 0) ∧
    (∀ i, i < 12 → tr.cell T_RCPT i lo8 = if i ≤ 7 then 1 else 0) := by
  obtain ⟨h13, F, -⟩ := table_of hL
  have hc : ∀ i, i < 12 → tr.cell T_RCPT i sCL = 1 := fun i hi => by simpa using F.st i hi
  have hfe : ∀ i, i < 12 → tr.cell T_RCPT i fe = if i = 11 then 1 else 0 := fun i hi => by
    have := F.fe i hi; simpa [show (i + 1 = 12) = (i = 11) by simp] using this
  have hidx : ∀ i, i < 12 → tr.cell T_RCPT i idx = ((i : Nat) : Fp) := fun i hi => by simpa using F.idx i hi
  have flag : ∀ (x m : Nat), x ∈ boolCols → m + 1 < 12 →
      (Expr.mul .isFirst (Dsl.not (c x))) ∈ Rcpt.constraints →
      (Expr.mul (mul3 cl (Dsl.not (c fe)) (n x)) (Dsl.not (c x))) ∈ Rcpt.constraints →
      (Expr.mul (mul3 cl (c x) (Dsl.not (n x))) (sub (c idx) (k m))) ∈ Rcpt.constraints →
      (mul3 cl (c fe) (c x)) ∈ Rcpt.constraints →
      ∀ i, i < 12 → tr.cell T_RCPT i x = if i ≤ m then 1 else 0 := by
    intro x m hx hm m1 m2 m3 m4
    refine step_flag (fun i => tr.cell T_RCPT i x) m 12 hm (fun i hi => isBool hL (by omega) hx) ?_ ?_ ?_ ?_
    · have := con hL (r := 0) (by omega) m1
      simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_true] at this; grind
    · intro i hi h1
      have := con hL (r := i) (by omega) m2
      simp only [cl, eval_mul, eval_mul3, eval_c, eval_not, eval_n, nxt (show i + 1 < tr.height T_RCPT by omega)] at this
      rw [hc i (by omega), hfe i (by omega), if_neg (by omega)] at this
      rw [h1] at this; grind
    · intro i hi h1 h0
      have := con hL (r := i) (by omega) m3
      simp only [cl, eval_mul, eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_k,
        nxt (show i + 1 < tr.height T_RCPT by omega)] at this
      rw [hc i (by omega), h1, h0, hidx i (by omega)] at this
      exact ofNat_inj (by unfold P; omega) (by unfold P; omega) (by grind)
    · have := con hL (r := 11) (by omega) m4
      simp only [cl, eval_mul3, eval_c] at this
      rw [hc 11 (by omega), hfe 11 (by omega), if_pos rfl] at this
      grind
  exact ⟨flag lo4 3 (by simp [boolCols]) (by omega) (mem_cl (by simp [cClaim])) (mem_cl (by simp [cClaim]))
      (mem_cl (by simp [cClaim])) (mem_cl (by simp [cClaim])),
    flag lo8 7 (by simp [boolCols]) (by omega) (mem_cl (by simp [cClaim])) (mem_cl (by simp [cClaim]))
      (mem_cl (by simp [cClaim])) (mem_cl (by simp [cClaim]))⟩

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- The register loads of row 0. -/
def L32 : List Expr := pubs PV_SHARD 8 ++ pubs PV_N 4 ++ pubs PV_NREF 4 ++ ks G_LE ++ pubs PV_GASLIM 8

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem reg_row0 (j : Nat) (hj : j < 32) :
    tr.cell T_RCPT 0 (reg j) = (L32[j]'(by simp [L32, pubs, ks, G_LE]; omega)).eval tr T_RCPT 0 pub := by
  have hz : (L32[j]'(by simp [L32, pubs, ks, G_LE]; omega), j) ∈ L32.zip (List.range 32) := by
    have : (L32.zip (List.range 32))[j]'(by simp [L32, pubs, ks, G_LE]; omega) =
        (L32[j]'(by simp [L32, pubs, ks, G_LE]; omega), j) := by simp
    rw [← this]; exact List.getElem_mem _
  have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
  have c := con hL h0 (e := .mul .isFirst (sub (c (reg j)) (L32[j]'(by simp [L32, pubs, ks, G_LE]; omega))))
    (mem_rg (by
      unfold cRegs; simp only [List.mem_append]
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))))))
      exact List.mem_map.mpr ⟨_, hz, rfl⟩))
  simp only [eval_mul, eval_isFirst, if_true, eval_sub, eval_c] at c
  grind

theorem reg_rot {q : Nat} (hq : q < 11) (h13 : 13 < tr.height T_RCPT) (F : Fld tr 0 12 sCL) :
    (∀ j, j < 12 → tr.cell T_RCPT (q + 1) (reg j) = tr.cell T_RCPT q (reg ((j + 1) % 12))) ∧
    (∀ j, j < 4 → tr.cell T_RCPT (q + 1) (reg (12 + j)) = tr.cell T_RCPT q (reg (12 + (j + 1) % 4))) := by
  have hc : tr.cell T_RCPT q sCL = 1 := by simpa using F.st q (by omega)
  have hfe : tr.cell T_RCPT q fe = 0 := by
    have := F.fe q (by omega); simp at this; rw [this, if_neg (by omega)]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have c := con hL (r := q) (by omega) (e := mul3 (c sCL) (Dsl.not (c fe))
      (sub (n (reg j)) (c (reg ((j + 1) % 12))))) (mem_rg (by
        unfold cRegs; simp only [List.mem_append]
        refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))))
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt (show q + 1 < tr.height T_RCPT by omega)] at c
    rw [hc, hfe] at c; grind
  · have c := con hL (r := q) (by omega) (e := mul3 (c sCL) (Dsl.not (c fe))
      (sub (n (reg (12 + j))) (c (reg (12 + (j + 1) % 4))))) (mem_rg (by
        unfold cRegs; simp only [List.mem_append]
        refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt (show q + 1 < tr.height T_RCPT by omega)] at c
    rw [hc, hfe] at c; grind

theorem claim_reg (h13 : 13 < tr.height T_RCPT) (F : Fld tr 0 12 sCL) :
    (∀ i, i < 12 → ∀ j, j < 12 → tr.cell T_RCPT i (reg j) = tr.cell T_RCPT 0 (reg ((j + i) % 12))) ∧
    (∀ i, i < 12 → ∀ j, j < 4 → tr.cell T_RCPT i (reg (12 + j)) = tr.cell T_RCPT 0 (reg (12 + (j + i) % 4))) := by
  constructor
  · intro i
    induction i with
    | zero => intro _ j hj; simp [Nat.mod_eq_of_lt hj]
    | succ i ih =>
      intro hi j hj
      rw [(reg_rot hL (q := i) (by omega) h13 F).1 j hj, ih (by omega) _ (Nat.mod_lt _ (by omega))]
      congr 2; omega
  · intro i
    induction i with
    | zero => intro _ j hj; simp [Nat.mod_eq_of_lt hj]
    | succ i ih =>
      intro hi j hj
      rw [(reg_rot hL (q := i) (by omega) h13 F).2 j hj, ih (by omega) _ (Nat.mod_lt _ (by omega))]
      congr 3; omega

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem pub_cast (pub : List Fp) (i : Nat) : pub.getD i 0 = ((pubNat pub i : Nat) : Fp) := by
  simp [pubNat, natCast_eq, fpN]

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem claim_vals (h13 : 13 < tr.height T_RCPT) (F : Fld tr 0 12 sCL) :
    (∀ i, i < 12 → tr.cell T_RCPT i (reg 0) = (((pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4).getD i 0 : Nat) : Fp)) ∧
    (∀ i, i < 4 → tr.cell T_RCPT i (reg 12) = (((pubBytes pub PV_NREF 4).getD i 0 : Nat) : Fp)) := by
  obtain ⟨R1, R2⟩ := claim_reg hL h13 F
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [R1 i hi 0 (by omega), show (0 + i) % 12 = i by omega, reg_row0 hL i (by omega)]
    by_cases h8 : i < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [pubBytes]; omega)]
      simp [L32, pubs, pubBytes, List.getElem_append, h8, show i < 12 by omega, show i < 16 by omega,
        show i < 24 by omega, List.getElem?_range h8]
      simp [pubNat, natCast_eq, fpN, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [pubBytes]; omega)]
      simp [L32, pubs, pubBytes, List.getElem_append, h8, show i < 12 by omega, show i < 16 by omega,
        show i < 24 by omega, List.getElem?_range (show i - 8 < 4 by omega)]
      simp [pubNat, natCast_eq, fpN, List.getD_eq_getElem?_getD, show i - 8 < 4 by omega]
  · rw [R2 i (by omega) 0 (by omega), show (0 + i) % 4 = i by omega, reg_row0 hL (12 + i) (by omega)]
    simp [L32, pubs, pubBytes, List.getElem_append, show ¬ (12 + i < 8) by omega, show ¬ 12 + i < 12 by omega,
      show 12 + i < 16 by omega, show 12 + i < 24 by omega, List.getD_eq_getElem?_getD, List.getElem?_range hi]
    simp [pubNat, natCast_eq, fpN, List.getD_eq_getElem?_getD, show ¬ (12 + i - 8 < 4) by omega,
      show 12 + i - 8 - 4 < 4 by omega, show 12 + i - 8 - 4 = i by omega, hi]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **The claim rows' `BYTES` messages: the `RC` and `RF` headers.** -/
theorem claim_bytes :
    ((List.range' 0 12).flatMap fun q => rowTraffic Rcpt.interactions tr T_RCPT q pub B_BYTES true).Perm
      ((emitAt K_RC 0 (pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4) ++
        emitAt K_RF 0 (pubBytes pub PV_NREF 4)).map Msg.toFp) := by
  obtain ⟨h13, F, -⟩ := table_of hL
  obtain ⟨V1, V2⟩ := claim_vals hL h13 F
  have l4 := (claim_flags hL).1
  have hX : (sCL, [(RC, ix, c (reg 0), k 1), (RF, ix, c (reg 12), c lo4)]) ∈ emits := by simp [emits]
  have hst : ∀ i, i < 12 → tr.cell T_RCPT i sCL = 1 := fun i hi => by simpa using F.st i hi
  have hix : ∀ i, i < 12 → tr.cell T_RCPT i idx = ((i : Nat) : Fp) := fun i hi => by simpa using F.idx i hi
  rw [flatMap_congr' (G := fun q => (List.range 3).flatMap (slotT tr q)) (fun q _ => rowT_bytes q)]
  refine (slots_perm tr 0 12).trans (List.Perm.of_eq ?_)
  have e0 : (List.range' 0 12).flatMap (fun q => slotT tr q 0) =
      (emitAt K_RC 0 (pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4)).map Msg.toFp := by
    rw [flatMap_range'_single _ (fun i => Msg.toFp [K_RC, 0 + i,
      (pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4).getD i 0]) 0 12 (fun i hi => ?_)]
    · simp [emitAt, pubBytes, List.map_map, Function.comp_def]
    · rw [Nat.zero_add, emit_some hL (by omega) hX (hst i hi) (e := 0) (by decide) rfl, if_pos (by rfl)]
      simp only [RC, ix, eval_k, eval_c, hix i hi, V1 i hi, Msg.toFp, List.map_cons, List.map_nil, natCast_eq,
        Nat.zero_add]
  have e1 : (List.range' 0 12).flatMap (fun q => slotT tr q 1) =
      (emitAt K_RF 0 (pubBytes pub PV_NREF 4)).map Msg.toFp := by
    rw [flatMap_window _ 0 12 0 4 (by omega) (fun j hj hout => by
      rw [Nat.zero_add, emit_some hL (by omega) hX (hst j hj) (e := 1) (by decide) rfl, if_neg (by
        simp only [eval_c]; rw [l4 j hj, if_neg (by omega)]; exact fp_zero_ne_one)])]
    rw [flatMap_range'_single _ (fun i => Msg.toFp [K_RF, 0 + i, (pubBytes pub PV_NREF 4).getD i 0]) (0 + 0) 4
      (fun i hi => ?_)]
    · simp [emitAt, pubBytes, List.map_map, Function.comp_def]
    · rw [Nat.zero_add, emit_some hL (by omega) hX (hst i (by omega)) (e := 1) (by decide) rfl,
        if_pos (by simp only [eval_c]; rw [l4 i (by omega), if_pos (by omega)])]
      simp only [RF, ix, eval_k, eval_c, hix i (by omega), V2 i hi, Msg.toFp, List.map_cons, List.map_nil,
        natCast_eq, Nat.zero_add]
  have e2 : (List.range' 0 12).flatMap (fun q => slotT tr q 2) = [] := by
    apply flatMap_range'_nil; intro i hi
    exact emit_none hL (by omega) hX (hst _ (by omega)) (e := 2) (by decide) rfl
  rw [e0, e1, e2, List.append_nil, List.map_append]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- A row on which no receipt-specific state is on sends only its `BYTES` slots. -/
theorem quiet {q : Nat} (hq : q < tr.height T_RCPT) (h1 : tr.cell T_RCPT q sXRI = 0) (h2 : tr.cell T_RCPT q sXLH = 0)
    (h3 : tr.cell T_RCPT q rl = 0) (h4 : tr.cell T_RCPT q sV = 0) (h5 : tr.cell T_RCPT q sVL = 0)
    (h6 : tr.cell T_RCPT q sRID = 0) (h7 : tr.cell T_RCPT q sPL = 0) (h8 : tr.cell T_RCPT q sDEP = 0)
    (b : Nat) (sd : Bool) :
    rowTraffic Rcpt.interactions tr T_RCPT q pub b sd =
      if b = B_BYTES ∧ sd = true then (List.range 3).flatMap (slotT tr q) else [] := by
  have hg := (dig_row hL hq).1
  rw [h1, h2] at hg
  have hl : tr.cell T_RCPT q lastR = 0 := by
    have c := con hL hq (e := sub (c lastR) (.mul (c rl) (Dsl.not (n act)))) (mem_st (by simp [cStates]))
    simp only [eval_sub, eval_mul, eval_c, eval_not, eval_n] at c
    rw [h3] at c; grind
  have hk := (key_row hL hq).1
  rw [h4, kz_zero hL hq h5, h6] at hk
  have hrf : tr.cell T_RCPT q rf = 0 := bool01 hL hq (by simp [boolCols]) (fun e => by
    have := ((bounds hL hq).2.1 e).1; rw [h7] at this; exact fp_zero_ne_one this)
  rw [rowT]
  simp only [C, gt_zero (show tr.cell T_RCPT q gDg = 0 by rw [hg]; grind), gt_zero hl,
    gt_zero (show tr.cell T_RCPT q gKA = 0 by rw [hk]; grind), gt_zero h4, gt_zero hrf, gt_zero h8, gt_zero h6]
  simp

theorem claim_quiet {q : Nat} (hq : q < 12) (b : Nat) (sd : Bool) :
    rowTraffic Rcpt.interactions tr T_RCPT q pub b sd =
      if b = B_BYTES ∧ sd = true then (List.range 3).flatMap (slotT tr q) else [] := by
  obtain ⟨h13, F, -⟩ := table_of hL
  have hc : tr.cell T_RCPT q sCL = 1 := by simpa using F.st q hq
  have oh := (oneHot hL (by omega) (by simp [states]) hc).2
  have hrl : tr.cell T_RCPT q rl = 0 := by
    rw [rl_at hL (by omega) (by simp [states]) hc, if_neg (by decide), if_neg (by decide)]; grind
  exact quiet hL (by omega) (oh _ (by simp [states]) (by decide)) (oh _ (by simp [states]) (by decide)) hrl
    (oh _ (by simp [states]) (by decide)) (oh _ (by simp [states]) (by decide)) (oh _ (by simp [states]) (by decide))
    (oh _ (by simp [states]) (by decide)) (oh _ (by simp [states]) (by decide)) b sd

theorem pad_quiet {q : Nat} (hq : q < tr.height T_RCPT) (ha : tr.cell T_RCPT q act = 0) (b : Nat) (sd : Bool) :
    rowTraffic Rcpt.interactions tr T_RCPT q pub b sd = [] := by
  have ns := noState hL hq ha
  have hrl : tr.cell T_RCPT q rl = 0 := by
    rw [(bounds hL hq).1, ns sXRZ (by simp [states]), ns sXLH (by simp [states])]; grind
  rw [quiet hL hq (ns _ (by simp [states])) (ns _ (by simp [states])) hrl (ns _ (by simp [states]))
    (ns _ (by simp [states])) (ns _ (by simp [states])) (ns _ (by simp [states])) (ns _ (by simp [states])) b sd]
  split
  · rw [flatMap_congr' (G := fun _ => []) (fun e he => ?_), flatMap_nil_fun]
    have c := con hL hq (e := .mul (Dsl.not (c act)) (c (eG e))) (mem_em (by
      unfold cEmit; simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem (f := fun e => Expr.mul (Dsl.not (c act)) (c (eG e))) he))))
    simp only [eval_mul, eval_not, eval_c] at c
    rw [ha] at c
    have : tr.cell T_RCPT q (eG e) = 0 := by grind
    simp [slotT, this]
  · rfl

end ZkFormal.Near.RcptProof
