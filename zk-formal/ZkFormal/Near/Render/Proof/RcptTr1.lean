import ZkFormal.Near.Render.Proof.RcptEnd
import ZkFormal.Near.Extract.RcptProof

/-!
# ZkFormal.Near.Render.Proof.RcptTr1 — the shape of the honest `rcpt` table

`RcptLocalStmt` gives the extraction's `Shape tr rcs` of the honest table
(`shape_of`).  Every field row of the extracted receipt `i` is the honest record
`seg i f k` (`rec_at`): the row is active, in state `f`, at index `k`, with the
receipt constant `r = i`, and these cells determine the record.  Hence the
extracted receipt parameters are the honest ones (`rs_eq`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen RcptProof

theorem ofNat_inj {a b : Nat} (ha : a < Render.P) (hb : b < Render.P) (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have := congrArg Fp.toNat h
  rwa [ofNat_lt_eq ha, ofNat_lt_eq hb] at this

theorem nodeSize_pos (nr : NodeRec) : 1 ≤ nodeSize nr := by
  unfold nodeSize
  cases nr with
  | leaf k v mem => simp [ser]; omega
  | ext k kid mem => simp [ser]; omega
  | branch v kids mem => cases v <;> simp [ser] <;> omega

theorem ns_len_le : ∀ ns : List NodeRec, ns.length ≤ revealedOf ns
  | [] => Nat.zero_le _
  | nr :: ns => by
    have := ns_len_le ns; have := nodeSize_pos nr
    simp only [revealedOf, List.map_cons, List.sum_cons, List.length_cons] at *; omega

theorem kslot_lt {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e) : (Df c e r).kslot < 3000001 := by
  have hm := slot_mem hg hr
  rw [mem_touched] at hm
  obtain ⟨nr, h, -⟩ := hm
  have hk : e.slot r < e.ns.length := by
    rcases Nat.lt_or_ge (e.slot r) e.ns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have := ns_len_le e.ns; have := hg.size
  simp only [Params.maxWitnessBytes] at this
  rw [Df_eq hr]; simp only [rdOf, mkInfo_e]; omega

theorem P_3M : 3000001 < Render.P := by decide

theorem height_le18 {c : Claim} {e : Ext} (hg : Good c e) : (render c e).height T_RCPT ≤ 2 ^ 18 := by
  rw [rcpt_height, ← rcpt_log]; exact Nat.pow_le_pow_right (by decide) (rcpt_log_le hg)

theorem height_ltP {c : Claim} {e : Ext} (hg : Good c e) : (render c e).height T_RCPT < Render.P := by
  have := height_le18 hg; have : (2 : Nat) ^ 18 < Render.P := by decide
  omega

/-- The cell of the honest table at row `q`. -/
theorem cell_q {c : Claim} {e : Ext} (hg : Good c e) {q : Nat} (hq : q < (render c e).height T_RCPT) (col : Nat) :
    (render c e).cell T_RCPT q col =
      if h : q < (RL c e).length then cF c e (RL c e)[q] col else 0 := by
  rw [rcpt_cell c e hq, cellQ]
  split
  · rename_i h; rw [getD_RL hg h]; rfl
  · rfl

theorem fLen_lt {c : Claim} {e : Ext} (hg : Good c e) {r s : Nat} (hr : r < NN e) : fLen (Df c e r) s ≤ 64 := by
  have := (pred_ok hg hr).len; have := (recv_ok hg hr).len; have := (signer_ok hg hr).len; have := d_kt hg hr
  unfold fLen
  by_cases h5 : s = 5
  · simp only [h5, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h6 : s = 6
  · simp only [h6, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h7 : s = 7
  · simp only [h7, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h8 : s = 8
  · simp only [h8, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h9 : s = 9
  · simp only [h9, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h10 : s = 10
  · simp only [h10, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h11 : s = 11
  · simp only [h11, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h12 : s = 12
  · simp only [h12, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h13 : s = 13
  · simp only [h13, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h14 : s = 14
  · simp only [h14, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h15 : s = 15
  · simp only [h15, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h16 : s = 16
  · simp only [h16, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h17 : s = 17
  · simp only [h17, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h18 : s = 18
  · simp only [h18, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h19 : s = 19
  · simp only [h19, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h20 : s = 20
  · simp only [h20, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h21 : s = 21
  · simp only [h21, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h22 : s = 22
  · simp only [h22, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h23 : s = 23
  · simp only [h23, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h24 : s = 24
  · simp only [h24, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h25 : s = 25
  · simp only [h25, ↓reduceIte, Nat.reduceEqDiff]; omega
  by_cases h26 : s = 26
  · simp only [h26, ↓reduceIte, Nat.reduceEqDiff]; omega
  simp only [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, ↓reduceIte]; omega

theorem plan_fst (h : Bool) (Lp Lv Ls kt : Nat) : (plan h Lp Lv Ls kt).map Prod.fst = fields h := by
  cases h <;> rfl

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hL : TableLocal Rcpt.table (render c.1 e) T_RCPT (publicOf c))
  {rcs : List RS} (S : Shape (render c.1 e) rcs)
include hg hL S

/-- **The record at a field row** of the extracted receipt `i`. -/
theorem rec_at {i : Nat} (hi : i < rcs.length) {f o L : Nat}
    (hf : (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt) {k : Nat} (hk : k < L) :
    ∃ h : rcs[i].s + o + k < (RL c.1 e).length, (RL c.1 e)[rcs[i].s + o + k] = .seg i f k := by
  have lay := S.lay _ (List.getElem_mem hi)
  have F := lay.flds _ hf
  simp only at F
  have hpl : o + L ≤ total rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt := by
    unfold plan at hf; unfold total Vt hN at *
    cases hh : rcs[i].h <;> simp [hh] at hf ⊢ <;> omega
  have hfin := lay.fin
  have hH := height_ltP hg
  have hq : rcs[i].s + o + k < (render c.1 e).height T_RCPT := by omega
  have hact := F.fld.act k hk
  have hst := F.fld.st k hk
  have hidx := F.fld.idx k hk
  have hr := F.consts k hk Rcpt.r (by simp [Rcpt.rconsts])
  rw [S.r i hi] at hr
  rw [cell_q hg hq] at hact hst hidx hr
  by_cases hlt : rcs[i].s + o + k < (RL c.1 e).length
  · refine ⟨hlt, ?_⟩
    rw [dif_pos hlt] at hact hst hidx hr
    have hok := RL_ok hg _ (List.getElem_mem hlt)
    have hff : f ∈ fields rcs[i].h := by
      rw [← plan_fst rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt]
      exact List.mem_map_of_mem (f := Prod.fst) hf
    have hf5 : 5 ≤ f ∧ f ≤ 26 := by
      cases rcs[i].h <;> simp [fields] at hff <;> omega
    generalize hρ : (RL c.1 e)[rcs[i].s + o + k] = ρ at hok hact hst hidx hr
    cases ρ with
    | cl i' =>
      have : cF c.1 e (.cl i') f = 0 := by
        simp only [cF, Cc_cl_st (show i' < 12 from hok) (by omega) hf5.2, show f ≠ 4 by omega, ↓reduceIte]; rfl
      rw [this] at hst; exact absurd hst (by decide)
    | seg r' s' i' =>
      obtain ⟨hr', hs', hi'⟩ := hok
      have e1 : s' = f := by
        rw [cF_st f hf5.1 hf5.2] at hst
        by_cases hne : s' = f
        · exact hne
        · rw [if_neg (Ne.symm hne)] at hst; exact absurd hst (by decide)
      subst e1
      have e2 : i' = k := by
        simp only [cF, S_idx, natCast_eq] at hidx
        have := fLen_lt hg hr' (s := s'); have := P_3M
        exact ofNat_inj (by omega) (by omega) hidx
      have e3 : r' = i := by
        simp only [cF, S_r, Df_r hr', natCast_eq] at hr
        have := len_lt hL S; have := P_3M
        have : NN e ≤ 256 := by have := hg.n_le; have := hg.len; simp only [NN, Params.maxBatch] at *; omega
        exact ofNat_inj (by omega) (by omega) hr
      subst e2 e3; rfl
  · rw [dif_neg hlt] at hact; exact absurd hact (by decide)

end

end RcptP

end ZkFormal.Near.Render
