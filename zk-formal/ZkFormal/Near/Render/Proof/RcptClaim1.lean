import ZkFormal.Near.Render.Proof.RcptDep3

/-!
# ZkFormal.Near.Render.Proof.RcptClaim1 — the claim bytes and the claim-row arithmetic

Under `Good` (`Hdr c = ⟨pv, chain⟩`): the public claim prefix, the bytes of
`n`, `nref`; the generator's claim-row values `Cl.n = n`, `y = (n − 1)·G` as
bytes, `gasLimit − y − 1` with borrow, `y + G = gasBurnt`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen

theorem pubF (c : WfClaim) (e : Ext) (j : Nat) : (publicOf c).getD j 0 = Fp.ofNat (pubNat (publicOf c) j) := by
  rw [pub_eq c e, PA_pubNat]

theorem G_V : V (fun i => Rcpt.G_LE.getD i 0) 8 = Params.G := by simp [V, Rcpt.G_LE, G_val]

theorem refunds_le (c : Claim) (e : Ext) : (e.refunds c).length ≤ e.rs.length := by
  unfold Ext.refunds
  rw [List.length_flatMap]
  have : ∀ m, ((List.range m).map fun r => (e.refundOf c r).length).sum ≤ m := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      have : (e.refundOf c m).length ≤ 1 := by
        unfold Ext.refundOf
        by_cases hs : surplusOf c.blockGasPrice (e.rc m) = 0 <;> simp [hs]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  exact this _

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem hdr : Link.Hdr c := ⟨hg.pv, hg.chain⟩

theorem pub_prefix {j : Nat} (hj : j < 77) : pubNat (publicOf c) j = (claimPrefix.getD j 0).toNat := by
  rw [Link.pubNat_publicOf, Link.encode_eq (hdr hg)]
  have hl : claimPrefix.length = 77 := by rw [claimPrefix_length]; rfl
  simp only [List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem n_lt : c.1.receiptCount ≤ 256 := by have := hg.n_le; simp only [Params.maxBatch] at this; omega

theorem pubN {k : Nat} (hk : k < 4) : pubNat (publicOf c) (PV_N + k) = (leBytes 4 c.1.receiptCount).getD k 0 := by
  rw [← PA_pubNat c e, PA_field (Link.pub_n (hdr hg)) hk]

theorem pubNref {k : Nat} (hk : k < 4) : pubNat (publicOf c) (PV_NREF + k) = (leBytes 4 c.1.refundCount).getD k 0 := by
  rw [← PA_pubNat c e, PA_field (Link.pub_nref (hdr hg)) hk]

theorem nref_le : c.1.refundCount ≤ 256 := by
  have := refunds_le c.1 e; rw [hg.refundCount, hg.len] at this; have := n_lt hg; omega

/-- `Cl.n` is the receipt count. -/
theorem cl_n : Cl.n (PA c.1 e) = c.1.receiptCount := by
  have h := fun k (hk : k < 4) => PA_field (e := e) (Link.pub_n (hdr hg)) hk
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [leBytes_getD, show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide,
    show (3 : Nat) < 4 by decide, ↓reduceIte] at h0 h1 h2 h3
  have := n_lt hg
  simp only [Cl.n, RcptGen.pubs, List.range, List.range.loop, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, h0, h1, h2, h3, PV_N] at *
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, show (256 : Nat) ^ 2 = 65536 from rfl,
    show (256 : Nat) ^ 3 = 16777216 from rfl]
  omega

/-! ## `y = (n − 1)·G` -/

theorem V_x1 : V (Cl.x1 (PA c.1 e)) 8 = (c.1.receiptCount - 1) * Params.G := by
  rw [show Cl.x1 (PA c.1 e) = fun i => (Cl.n (PA c.1 e) - 1) * Rcpt.G_LE.getD i 0 from rfl, V_smul, G_V, cl_n hg]

theorem y_lt : (c.1.receiptCount - 1) * Params.G < 256 ^ 8 := by
  have := n_lt hg; rw [G_val]
  have : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  omega

theorem yB_eq : Cl.yB (PA c.1 e) = leBytes 8 ((c.1.receiptCount - 1) * Params.G) := by
  simp only [Cl.yB, cl_n hg]

theorem sy_mod {i : Nat} (hi : i < 8) : Cl.sy (PA c.1 e) i % 256 = (Cl.yB (PA c.1 e)).getD i 0 := by
  rw [yB_eq hg]; exact chain_byte _ hi (V_x1 hg)

theorem x1_le (i : Nat) : Cl.x1 (PA c.1 e) i ≤ 65025 := by
  simp only [Cl.x1, cl_n hg]
  have := n_lt hg
  have : Rcpt.G_LE.getD i 0 ≤ 255 := by
    simp only [Rcpt.G_LE]
    rcases (show i < 8 ∨ 8 ≤ i by omega) with h | h
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp [List.getD_eq_getElem?_getD, show ¬ i < 8 by omega]
  exact Nat.le_trans (Nat.mul_le_mul (show c.1.receiptCount - 1 ≤ 255 by omega) this) (by decide)

theorem cy_le (i : Nat) : chain (Cl.x1 (PA c.1 e)) i ≤ 255 := chain_le _ (fun j => by have := x1_le hg j; omega) i
theorem sy_div (i : Nat) : Cl.sy (PA c.1 e) i / 256 = chain (Cl.x1 (PA c.1 e)) (i + 1) := by
  simp only [Cl.sy, chain]
theorem cy_final : chain (Cl.x1 (PA c.1 e)) 8 = 0 := chain_zero_of _ (by rw [V_x1 hg]; exact y_lt hg)

/-! ## `gasLimit − y − 1` -/

theorem D_eq {i : Nat} (hi : i < 8) : (Cl.D (PA c.1 e)).getD i 0 = (leBytes 8 c.1.gasLimit).getD i 0 := by
  simp only [Cl.D]; rw [pubs_getD _ hi, PA_field (Link.pub_gasLimit (hdr hg)) hi]

theorem D_lt (i : Nat) : (Cl.D (PA c.1 e)).getD i 0 < 256 := by
  rcases (show i < 8 ∨ 8 ≤ i by omega) with h | h
  · rw [D_eq hg h]; exact leBytes_getD_lt _ _ _
  · simp [Cl.D, RcptGen.pubs, List.getD_eq_getElem?_getD, show ¬ i < 8 by omega]

theorem yB_lt (i : Nat) : (Cl.yB (PA c.1 e)).getD i 0 < 256 := by rw [yB_eq hg]; exact leBytes_getD_lt _ _ _

theorem br_step (i : Nat) : (Cl.D (PA c.1 e)).getD i 0 + 256 * Cl.br (PA c.1 e) (i + 1) =
    (Cl.yB (PA c.1 e)).getD i 0 + Cl.br (PA c.1 e) i + Cl.dv (PA c.1 e) i :=
  (bdig_step _ _ 1 (D_lt hg) (yB_lt hg) (by decide) i).1

theorem dv_lt (i : Nat) : Cl.dv (PA c.1 e) i < 256 := bdig_lt _ _ 1 (D_lt hg) (yB_lt hg) (by decide) i
theorem br_le (i : Nat) : Cl.br (PA c.1 e) i ≤ 1 := bchain_le _ _ 1 i (by decide)

theorem br_final : Cl.br (PA c.1 e) 8 = 0 := by
  have := bchain_final (fun i => (Cl.D (PA c.1 e)).getD i 0) (fun i => (Cl.yB (PA c.1 e)).getD i 0) 1
    (D_lt hg) (yB_lt hg) (by decide) 8
  have e1 : V (fun i => (Cl.D (PA c.1 e)).getD i 0) 8 = c.1.gasLimit := by
    rw [V_congr (y := fun i => (leBytes 8 c.1.gasLimit).getD i 0) 8 (fun i hi => D_eq hg hi)]
    exact V_leBytes_of (Nat.le_refl _) (Link.wf_bounds c).2.2.2.1
  have e2 : V (fun i => (Cl.yB (PA c.1 e)).getD i 0) 8 = (c.1.receiptCount - 1) * Params.G := by
    rw [yB_eq hg]; exact V_leBytes_of (Nat.le_refl _) (y_lt hg)
  rw [e1, e2] at this
  have hgl := hg.gas_limit
  simp only [Cl.br]; rw [this, if_neg (by omega)]

/-! ## `y + G = gasBurnt` -/

theorem V_x3c : V (Cl.x3 (PA c.1 e)) 8 = c.1.gasBurntTotal := by
  rw [show Cl.x3 (PA c.1 e) = fun i => (Cl.yB (PA c.1 e)).getD i 0 + Rcpt.G_LE.getD i 0 from rfl, V_add, G_V,
    yB_eq hg, V_leBytes_of (Nat.le_refl _) (y_lt hg), hg.gas_total]
  have := hg.n_pos
  rw [show c.1.receiptCount * Params.G = (c.1.receiptCount - 1) * Params.G + Params.G by
    rw [← Nat.succ_mul, show (c.1.receiptCount - 1).succ = c.1.receiptCount by omega]]

theorem T_eq {i : Nat} (hi : i < 8) : (Cl.T (PA c.1 e)).getD i 0 = (leBytes 8 c.1.gasBurntTotal).getD i 0 := by
  simp only [Cl.T]; rw [pubs_getD _ hi, PA_field (Link.pub_gas (hdr hg)) hi]

theorem sg_mod {i : Nat} (hi : i < 8) : Cl.sg (PA c.1 e) i % 256 = (Cl.T (PA c.1 e)).getD i 0 := by
  rw [T_eq hg hi]; exact chain_byte _ hi (V_x3c hg)

theorem cg_le (i : Nat) : chain (Cl.x3 (PA c.1 e)) i ≤ 1 :=
  chain_le _ (fun j => by
    simp only [Cl.x3]
    have := yB_lt hg j
    have : Rcpt.G_LE.getD j 0 ≤ 255 := by
      simp only [Rcpt.G_LE]
      rcases (show j < 8 ∨ 8 ≤ j by omega) with h | h
      · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp [List.getD_eq_getElem?_getD, show ¬ j < 8 by omega]
    omega) i
theorem sg_div (i : Nat) : Cl.sg (PA c.1 e) i / 256 = chain (Cl.x3 (PA c.1 e)) (i + 1) := by
  simp only [Cl.sg, chain]
theorem cg_final : chain (Cl.x3 (PA c.1 e)) 8 = 0 :=
  chain_zero_of _ (by rw [V_x3c hg]; exact (Link.wf_bounds c).2.2.2.2.2.2.1)

end

end RcptP

end ZkFormal.Near.Render
