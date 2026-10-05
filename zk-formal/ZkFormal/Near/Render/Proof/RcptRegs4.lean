import ZkFormal.Near.Render.Proof.RcptRegs3
import ZkFormal.Near.Link.Claim

/-!
# ZkFormal.Near.Render.Proof.RcptRegs4 — `cRegs` on the claim rows; `regsFam : FamOk cRegs`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

section
variable {c : WfClaim} {e : Ext}

theorem rD_cl0 {nx : Nat → Fp} : ∀ x ∈ rD, evR (cF c.1 e (.cl 0)) nx true false (publicOf c) x = 0 := by
  intro x hx
  simp only [rD, List.mem_map] at hx
  obtain ⟨⟨y, j⟩, hy, rfl⟩ := hx
  obtain ⟨hj, rfl⟩ := mem_zip_range' (by rfl) hy
  simp only [clLd, Rcpt.pubs, Rcpt.ks, List.length_append, List.length_map, List.length_range, Rcpt.G_LE,
    List.length_cons, List.length_nil] at hj
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | (simp [clLd, Rcpt.pubs, Rcpt.ks, Rcpt.G_LE, cF, L_reg, Cl.A, Cl.B, Cl.D, RcptGen.pubs, pub_get c e,
        natCast_eq, PV_SHARD, PV_N, PV_NREF, PV_GASLIM]; grind)

theorem rE_cl0 {nx : Nat → Fp} : ∀ x ∈ rE, evR (cF c.1 e (.cl 0)) nx true false (publicOf c) x = 0 := by
  intro x hx
  simp only [rE, List.mem_map] at hx
  obtain ⟨⟨y, j⟩, hy, rfl⟩ := hx
  obtain ⟨hj, rfl⟩ := mem_zip_range' (by rfl) hy
  simp only [tkLd, Rcpt.pubs, Rcpt.ks, List.length_append, List.length_map, List.length_range,
    List.length_replicate] at hj
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | (simp [tkLd, Rcpt.pubs, Rcpt.ks, cF, L_tok, Cl.T, RcptGen.pubs, pub_get c e, natCast_eq, PV_GAS,
        List.replicate]; grind)

theorem cl_st0 {i st : Nat} (hi : i < 12) (h1 : 5 ≤ st) (h2 : st ≤ 26) : cF c.1 e (.cl i) st = 0 := by
  simp only [cF, Cc_cl_st hi (by omega) h2, show st ≠ 4 by omega, ↓reduceIte]; rfl

/-- **`cRegs` on a claim row.** -/
theorem cl_regs (hg : Good c.1 e) {i : Nat} (hi : i < 12) :
    ∀ x ∈ Rcpt.cRegs, evR (cF c.1 e (.cl i)) (cF c.1 e (nextOf (Df c.1 e) (.cl i))) (decide (i = 0)) false
      (publicOf c) x = 0 := by
  have hn : i < 11 → cF c.1 e (nextOf (Df c.1 e) (.cl i)) = cF c.1 e (.cl (i + 1)) := by
    intro h; simp [nextOf, h]
  have hact : cF c.1 e (.cl i) Rcpt.act = 1 := by simp only [cF, L_act]; rfl
  have hcl : cF c.1 e (.cl i) Rcpt.sCL = 1 := by simp only [cF, L_sCL]; rfl
  have hgp : cF c.1 e (.cl i) Rcpt.sGP = 0 := by simp only [cF, L_sGP]; rfl
  have hlr : cF c.1 e (.cl i) Rcpt.lastR = 0 := by simp only [cF, L_lastR]; rfl
  intro x hx
  rw [cRegs_eq] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((((((((hA | hB) | hC) | hD) | hE) | hF) | hG) | hH) | hI) | hJ
  · simp only [rA, List.mem_flatMap, List.mem_map] at hA
    obtain ⟨⟨st, l⟩, hl, ⟨y, j⟩, -, rfl⟩ := hA
    have hst := List.all_eq_true.1 loads_range _ hl
    simp only [decide_eq_true_eq] at hst
    simp only [evR_mul3, evR_c, cl_st0 hi hst.1 hst.2]; grind
  · simp only [rB, List.mem_cons, List.not_mem_nil, or_false] at hB
    subst hB
    simp only [evR_mul, evR_sum_map]
    rw [sumC_zero _ (fun k hk => by
      have := List.all_eq_true.1 regStates_range _ hk
      simp only [decide_eq_true_eq] at this
      exact cl_st0 hi this.1 this.2)]
    grind
  · simp only [rC, List.mem_map] at hC
    obtain ⟨j, -, rfl⟩ := hC
    simp only [evR_mul3, Rcpt.rowE, evR_sub, evR_c, hact, hcl]; grind
  · by_cases h0 : i = 0
    · subst h0; exact rD_cl0 x hD
    · simp only [rD, List.mem_map] at hD
      obtain ⟨⟨y, j⟩, -, rfl⟩ := hD
      simp only [evR_mul, evR_isFirst, h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
  · by_cases h0 : i = 0
    · subst h0; exact rE_cl0 x hE
    · simp only [rE, List.mem_map] at hE
      obtain ⟨⟨y, j⟩, -, rfl⟩ := hE
      simp only [evR_mul, evR_isFirst, h0, decide_false, Bool.false_eq_true, ↓reduceIte]; grind
  · simp only [rF, List.mem_append] at hF
    have hn' : i < 11 → cF c.1 e (nextOf (Df c.1 e) (.cl i)) = cF c.1 e (.cl (i + 1)) := hn
    rcases hF with (((h | h) | h) | h) | h
    · exact rot_cl hi (by decide) (fun i' j hj => cl_A hj) hn' x h
    · exact rot_cl hi (by decide) (fun i' j hj => cl_B hj) hn' x h
    · exact rot_cl hi (by decide) (fun i' j hj => cl_G hj) hn' x h
    · exact rot_cl hi (by decide) (fun i' j hj => cl_D hj) hn' x h
    · exact rot_cl hi (by decide) (fun i' j hj => cl_T hj) hn' x h
  · simp only [rG, List.mem_map, List.mem_range] at hG
    obtain ⟨j, hj, rfl⟩ := hG
    rcases (show i < 11 ∨ i = 11 by omega) with h | rfl
    · simp only [evR_mul3, evR_c, cF, L_fe, show ¬ i = 11 by omega, decide_false, b2n_false, ofNat0]; grind
    · have hN := NN_pos hg
      obtain ⟨-, -, -, ht, -⟩ := d_zero (c := c.1) (e := e) (by omega)
      have : nextOf (Df c.1 e) (.cl 11) = .seg 0 5 0 := by simp [nextOf]
      simp only [evR_mul3, evR_c, evR_n, this, cF_tok hj]
      simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, ↓reduceIte, Seg.tokOld, ht,
        leBytes_getD, Nat.zero_div, Nat.zero_mod, ite_self, ofNat0]
      grind
  · simp only [rH, List.mem_map] at hH
    obtain ⟨j, -, rfl⟩ := hH
    simp only [evR_mul, evR_c, hgp]; grind
  · simp only [rI, List.mem_cons, List.not_mem_nil, or_false] at hI
    subst hI; simp only [evR_mul, evR_c, hgp]; grind
  · simp only [rJ, List.mem_map] at hJ
    obtain ⟨j, -, rfl⟩ := hJ
    simp only [evR_mul, evR_sub, evR_c, Rcpt.rowE, hact, hcl, hgp, hlr]; grind

end

set_option maxRecDepth 100000 in
theorem regs_zrP : Rcpt.cRegs.all (Zr (fun _ => true) (fun _ => false) true) = true := by decide

/-- **`cRegs` on the honest rows.** -/
theorem regsFam : FamOk Rcpt.cRegs := by
  intro c e hg _
  have hB : c.1.blockGasPrice < 256 ^ 16 := (Link.wf_bounds c).2.2.1
  have mem : ∀ x ∈ Rcpt.cRegs, x ∈ rA ∨ x ∈ rB ∨ x ∈ rC ∨ x ∈ rD ++ rE ∨ x ∈ rF ++ rG ∨ x ∈ rH ++ rI ∨ x ∈ rJ := by
    intro x hx; rw [cRegs_eq] at hx; simp only [List.mem_append] at hx ⊢
    rcases hx with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
    all_goals simp only [h, true_or, or_true]
  have fifteen : ∀ r, fLen (Df c.1 e r) 15 = 16 := fun r => rfl
  apply fam_of hg
  · exact fun i hi => cl_regs hg hi
  · intro r s i hr hs hin x hx
    rcases mem x hx with h | h | h | h | h | h | h
    · exact rA_seg x h
    · exact rB_seg hs x h
    · exact rC_in hin x h
    · exact rDE_seg x h
    · exact rFG_seg x h
    · by_cases h15 : s = 15
      · subst h15
        have hi : i < 16 := by rw [fifteen] at hin; omega
        have tn : TokNx (Df c.1 e r) i (cF c.1 e (.seg r 15 (i + 1))) := fun j hj => cF_tok hj
        simp only [List.mem_append] at h
        rcases h with h | h
        · exact rH_gp hi tn x h
        · exact rI_gp hB hg hr hi tn x h
      · exact rHI_ne h15 x h
    · by_cases h15 : s = 15
      · subst h15; exact rJ_gp x h
      · exact rJ_keep (fun j hj => by rw [cF_tok hj, cF_tok hj, segTok_in h15]) x h
  · intro r s i hr hs hfe hrl x hx
    have hrl' : s ≠ 26 ∧ (s = 23 → (Df c.1 e r).hr = true) := by
      simp only [isRl, hfe, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
        Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hrl
      exact ⟨hrl.1, fun h => by rcases hrl.2 with h' | h'; exact absurd h h'; exact h'⟩
    rcases mem x hx with h | h | h | h | h | h | h
    · exact rA_seg x h
    · exact rB_seg hs x h
    · exact rC_fe hfe x h
    · exact rDE_seg x h
    · exact rFG_seg x h
    · by_cases h15 : s = 15
      · subst h15
        have hi : i = 15 := by rw [fifteen] at hfe; omega
        subst hi
        have tn : TokNx (Df c.1 e r) 15 (cF c.1 e (.seg r (nextF (Df c.1 e r).hr 15) 0)) := by
          intro j hj
          rw [show nextF (Df c.1 e r).hr 15 = 16 from rfl, cF_tok hj]
          simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
            Nat.reduceEqDiff, show ¬ (15 + 1 + j < 16) by omega, show 15 + 1 + j - 16 = j by omega]
        simp only [List.mem_append] at h
        rcases h with h | h
        · exact rH_gp (by omega) tn x h
        · exact rI_gp hB hg hr (by omega) tn x h
      · exact rHI_ne h15 x h
    · by_cases h15 : s = 15
      · subst h15; exact rJ_gp x h
      · exact rJ_keep (fun j hj => by rw [cF_tok hj, cF_tok hj, segTok_fe hs h15 hrl'.1 hrl'.2 hj]) x h
  · intro r s i hr hs hfe hrl x hx
    have h2326 : s = 23 ∨ s = 26 := by
      simp only [isRl, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hrl
      rcases hrl.2 with h | h
      · exact .inr h
      · exact .inl h.1
    have h15 : s ≠ 15 := by omega
    rcases mem x hx with h | h | h | h | h | h | h
    · exact rA_seg x h
    · exact rB_seg hs x h
    · exact rC_fe hfe x h
    · exact rDE_seg x h
    · exact rFG_seg x h
    · exact rHI_ne h15 x h
    · refine rJ_keep (fun j hj => ?_) x h
      have ht := (d_succ hg hr).2.2.2
      rw [cF_tok hj, cF_tok hj]
      rcases h2326 with rfl | rfl <;>
      simp only [segTok, beforeGP, List.contains, List.elem, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
        Seg.tokOld, Seg.tokNew, ht, Nat.reduceEqDiff]
  · obtain ⟨r, s, i, he, hr, hs, hfe, hrl, h2326⟩ := lastRec_facts hg
    rw [he]
    have h15 : s ≠ 15 := by omega
    intro x hx
    rcases mem x hx with h | h | h | h | h | h | h
    · exact rA_seg x h
    · exact rB_seg hs x h
    · exact rC_fe hfe x h
    · exact rDE_seg x h
    · exact rFG_seg x h
    · exact rHI_ne h15 x h
    · exact rJ_last hrl hr (Df_r (by omega)) h15 x h
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 regs_zrP x hx)
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 regs_zrP x hx)

end RcptP

end ZkFormal.Near.Render
