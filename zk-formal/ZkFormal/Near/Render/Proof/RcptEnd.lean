import ZkFormal.Near.Render.Proof.RcptClaim2

/-!
# ZkFormal.Near.Render.Proof.RcptEnd — `cEnd` on the honest rows; `endFam : FamOk cEnd`

On the batch's last row (`lastR`): `n = r + 1`, the refund count
`nref = rcnt + hr` and the tokens register `= tokens_burnt_total`
(`Good.len`, `Good.refundCount`, `Good.tokens` and the claim bytes); on the
first rows of `XRI`/`XLH` the digest lookups (`RID(r)`, 48 bytes; `PEO(r)`,
`37 + 32·hr + Lv` bytes).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen

theorem nrefPubE_eq : Rcpt.nrefPubE = sum [smul 1 (.pub 249), smul 256 (.pub 250), smul 65536 (.pub 251),
    smul 16777216 (.pub 252)] := rfl

/-- The refunds are one per receipt with a refund. -/
theorem refunds_len (c : Claim) (e : Ext) (m : Nat) :
    ((List.range m).flatMap (e.refundOf c)).length = ((List.range m).map fun r => b2n (hasRefund (mkInfo c e) r)).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.map_append, List.sum_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    congr 1
    simp only [hasRefund, mkInfo_e, mkInfo_c, Ext.refundOf]
    by_cases hs : surplusOf c.blockGasPrice (e.rc m) = 0 <;> simp [hs, b2n]

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem nref_eval {cur nx : Nat → Fp} {fst lst : Bool} :
    evR cur nx fst lst (publicOf c) Rcpt.nrefPubE = Fp.ofNat c.1.refundCount := by
  have h := fun k (hk : k < 4) => pubNref (e := e) hg (k := k) hk
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [leBytes_getD, show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide,
    show (3 : Nat) < 4 by decide, ↓reduceIte, Nat.pow_zero, Nat.pow_one, Nat.div_one,
    show (256 : Nat) ^ 2 = 65536 from rfl, show (256 : Nat) ^ 3 = 16777216 from rfl, Nat.add_zero] at h0 h1 h2 h3
  have hb := (Link.wf_bounds c).2.2.2.2.2.1
  have : (256 : Nat) ^ 4 = 4294967296 := rfl
  rw [nrefPubE_eq]
  simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_pub, pubF c e, natCast_eq]
  have hn : pubNat (publicOf c) 249 + 256 * pubNat (publicOf c) 250 + 65536 * pubNat (publicOf c) 251 +
      16777216 * pubNat (publicOf c) 252 = c.1.refundCount := by
    simp only [PV_NREF, Nat.reduceAdd] at h0 h1 h2 h3; omega
  rw [← hn]; simp only [ofNat_add_e, ofNat_mul_e, ofNat1]; grind

theorem peoLen_eq {r : Nat} (hr : r < NN e) :
    (Df c.1 e r).peoLen = 37 + 32 * b2n (Df c.1 e r).hr + (Df c.1 e r).recv.length := by
  have := peo_eq hg hr
  rw [Df_eq hr]
  simp only [rdOf] at this ⊢
  rw [← this]
  cases h : hasRefund (mkInfo c.1 e) r <;>
  simp [rcptViewOf, RcptV.peo, RcptV.borshN, u32r, G_LEn, rdOf, h, b2n, leBytes, leN_length, shaN, toNats,
    ArenaCore.sha256_length] <;> omega

/-- The last receipt: refund count and tokens. -/
theorem last_facts :
    (Df c.1 e (NN e - 1)).rcnt + b2n (Df c.1 e (NN e - 1)).hr = c.1.refundCount ∧
    (Df c.1 e (NN e - 1)).tok0 + (Df c.1 e (NN e - 1)).burnt = c.1.tokensBurntTotal := by
  have hN := NN_pos hg
  rw [Df_eq (show NN e - 1 < NN e by omega)]
  constructor
  · rw [← hg.refundCount, Ext.refunds, refunds_len]
    simp only [rdOf, NN] at hN ⊢
    conv => rhs; rw [show e.rs.length = e.rs.length - 1 + 1 by omega]
    rw [List.range_succ, List.map_append, List.sum_append]; simp
  · rw [← hg.tokens]
    simp only [rdOf, NN] at hN ⊢
    conv => rhs; rw [show e.rs.length = e.rs.length - 1 + 1 by omega]
    rfl

end

/-! ## Rows -/

/-- **`cEnd` on a receipt row.** -/
theorem end_seg {c : WfClaim} {e : Ext} (hg : Good c.1 e) {r s i : Nat} (hr : r < NN e) {nx : Nat → Fp} :
    ∀ x ∈ Rcpt.cEnd, evR (cF c.1 e (.seg r s i)) nx false false (publicOf c) x = 0 := by
  have hr0 := Df_r (c := c.1) hr
  have hlast : cF c.1 e (.seg r s i) Rcpt.lastR = 0 ∨
      (cF c.1 e (.seg r s i) Rcpt.lastR = 1 ∧ r + 1 = NN e ∧ (s = 23 ∨ s = 26)) := by
    rw [cF_lastR]
    cases h : isRl (Df c.1 e r) s i && (Df c.1 e r).r + 1 == NN e
    · left; rfl
    · right
      simp only [Bool.and_eq_true, beq_iff_eq, isRl, Bool.or_eq_true, Bool.not_eq_true'] at h
      refine ⟨rfl, by rw [← hr0]; exact h.2, ?_⟩
      rcases h.1.2 with h' | h'
      · exact .inr h'
      · exact .inl h'.1
  intro x hx
  simp only [Rcpt.cEnd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hx
  rcases hx with ((rfl | rfl) | ⟨j, hj, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · rcases hlast with h | ⟨h, hrN, -⟩
    · simp only [evR_mul, evR_c, h]; grind
    · simp only [evR_mul, evR_sub, evR_add, evR_c, evR_k, h, nPub_eval hg, cF, S_r, hr0, hg.len.symm, natCast_eq]
      simp only [NN] at hrN
      rw [show e.rs.length = r + 1 by omega, ofNat_add_e, ofNat1]; grind
  · rcases hlast with h | ⟨h, hrN, -⟩
    · simp only [evR_mul, evR_c, h]; grind
    · simp only [evR_mul, evR_sub, evR_add, evR_c, h, nref_eval hg, cF, S_rcnt, S_hr]
      rw [show r = NN e - 1 by omega, ← (last_facts hg).1, ofNat_add_e]; grind
  · rcases hlast with h | ⟨h, hrN, hs⟩
    · simp only [evR_mul, evR_c, h]; grind
    · simp only [evR_mul, evR_sub, evR_c, evR_pub, h, pubF c e, cF_tok hj]
      rw [← PA_pubNat c e, PA_field (Link.pub_tok (hdr hg)) hj, ← (last_facts hg).2, ← show r = NN e - 1 by omega]
      rcases hs with rfl | rfl <;>
      simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
        Nat.reduceEqDiff, Seg.tokNew] <;> grind
  · simp only [evR_sub, evR_mul, evR_add, evR_c, cF, S_gDg, S_fs, S_sXRI, S_sXLH]
    by_cases h15 : s = 15
    · subst h15; simp [b2n]; grind
    by_cases h17 : s = 17
    · subst h17; simp [b2n]; grind
    simp only [h15, h17, ↓reduceIte]
    by_cases h0 : i = 0 <;> by_cases h19 : s = 19 <;> by_cases h23 : s = 23 <;>
      simp [b2n, h0, h19, h23, Eq.comm] <;> grind
  all_goals simp only [evR_mul3, evR_sub, evR_add, evR_c, evR_smul, evR_k, evR_mid, evR_sum_cons, evR_sum_nil,
    cF, S_fs, S_sXRI, S_sXLH, S_dI, S_dL, S_r, S_hr, S_Lv]
  all_goals by_cases h0 : i = 0
  all_goals try (simp only [h0, decide_false, b2n_false, ofNat0]; grind)
  all_goals subst h0
  all_goals rcases (show s = 19 ∨ s = 23 ∨ (¬ s = 19 ∧ ¬ s = 23) by omega) with rfl | rfl | ⟨h19, h23⟩
  all_goals first
    | (simp only [decide_true, b2n_true, ofNat1, ofNat0, ↓reduceIte, Nat.reduceEqDiff, and_self, and_true, and_false, true_and, false_and, msgId, natCast_eq, ofNat_add_e, ofNat_mul_e]; grind)
    | (simp only [decide_true, b2n_true, ofNat1, ofNat0, ↓reduceIte, Nat.reduceEqDiff, and_self, and_true, and_false, true_and, false_and, msgId, natCast_eq, ofNat_add_e, ofNat_mul_e, peoLen_eq hg hr]
       cases (Df c.1 e r).hr <;> simp only [b2n_false, b2n_true, ofNat0, ofNat1] <;> grind)
    | (simp only [show (19 = s) ↔ False from ⟨fun h => h19 h.symm, False.elim⟩,
         show (23 = s) ↔ False from ⟨fun h => h23 h.symm, False.elim⟩, ↓reduceIte, ofNat0]; grind)

theorem end_zr : Rcpt.cEnd.all (Zr (fun x => x == Rcpt.lastR || x == Rcpt.gDg || x == Rcpt.sXRI || x == Rcpt.sXLH)
    (fun _ => false) false) = true := by decide

/-- **`cEnd` on the honest rows.** -/
theorem endFam : FamOk Rcpt.cEnd := by
  intro c e hg _
  have zr := fun x hx => List.all_eq_true.1 end_zr x hx
  have clR : ∀ i, ∀ {nx : Nat → Fp} {fst : Bool}, ∀ x ∈ Rcpt.cEnd,
      evR (cF c.1 e (.cl i)) nx fst false (publicOf c) x = 0 := by
    intro i nx fst x hx
    exact Zr_sound (zn := fun _ => false) (f0 := false)
      (fun y hy => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hy
        rcases hy with ((rfl | rfl) | rfl) | rfl <;> simp only [cF, L_lastR, L_gDg, L_sXRI, L_sXLH] <;> rfl)
      (fun _ h => by cases h) (fun h => by cases h) x (zr x hx)
  apply fam_of hg
  · intro i _; exact clR i
  · intro r s i hr _ _; exact end_seg hg hr
  · intro r s i hr _ _ _; exact end_seg hg hr
  · intro r s i hr _ _ _; exact end_seg hg (by omega)
  · obtain ⟨r, s, i, he, hr, -⟩ := lastRec_facts hg
    rw [he]; exact end_seg hg (by omega)
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h)
      (Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => by cases h) (zr x hx))
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h)
      (Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => by cases h) (zr x hx))

/-- **`RcptLocalStmt`.** -/
theorem rcptLocal : RcptLocalStmt := rcptLocal_of regsFam gasFam depFam claimFam endFam

end RcptP

end ZkFormal.Near.Render
