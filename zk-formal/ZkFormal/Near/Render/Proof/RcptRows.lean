import ZkFormal.Near.Render.Proof.RcptBase
import ZkFormal.Near.Link.RcptFacts
import ZkFormal.Near.Render.Proof.RcptBytes1

/-!
# ZkFormal.Near.Render.Proof.RcptRows — the honest `rcpt` table, row by row

The `rcpt` table of `render c e` has height `2^logOf (L + 1)` (`L` records) and
cells `Cc ρ col` on the record rows, `0` on the padding rows (`rcpt_cell`).
`allRows_of`: a constraint holds on every row once it holds on

* every record row but the last, with the next record (`nextOf`);
* the last record row, with a padding row next;
* a padding row followed by a padding row, or by row `0` (last row).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

section
variable (c : Claim) (e : Ext)

/-- Receipt data, public inputs, block gas price bytes, receipt count. -/
def DS : Array RD := (rcptData (mkInfo c e)).toArray
def Df (r : Nat) : RD := (DS c e).getD r default
def PA : Array Nat := pubArr (mkInfo c e)
def BG (i : Nat) : Nat := (leBytes 16 c.blockGasPrice).getD i 0
def NN : Nat := e.rs.length

/-- Cells of record `ρ`. -/
def Cc (ρ : RRec) (col : Nat) : Nat := fullCell (DS c e) (PA c e) (BG c) (NN e) ρ col
def cF (ρ : RRec) : Nat → Fp := fun col => Fp.ofNat (Cc c e ρ col)

/-- The records. -/
def RL : List RRec := recs (NN e) (Df c e)

/-- The last record. -/
def lastRec : RRec :=
  .seg (NN e - 1) (lastF (Df c e (NN e - 1)).hr) (fLen (Df c e (NN e - 1)) (lastF (Df c e (NN e - 1)).hr) - 1)

end

theorem Df_eq {c : Claim} {e : Ext} {r : Nat} (hr : r < NN e) : Df c e r = rdOf (mkInfo c e) r := by
  simp only [Df, DS, rcptData, Info.nRcpt, mkInfo_e]
  simp only [NN] at hr
  simp [Array.getD_eq_getD_getElem?, hr, mkInfo_e]

theorem Df_r {c : Claim} {e : Ext} {r : Nat} (hr : r < NN e) : (Df c e r).r = r := by
  rw [Df_eq hr]; rfl

theorem recs_rcptData (c : Claim) (e : Ext) : recsOf (rcptData (mkInfo c e)) = RL c e := by
  simp only [RL, recs]
  congr 1
  simp only [rcptData, Info.nRcpt, mkInfo_e, NN]
  exact List.map_congr_left (fun r hr => (Df_eq (by simpa [NN] using List.mem_range.1 hr)).symm)

/-! ## Cells beyond the width -/

theorem fullCell_ge {ds : Array RD} {pub : Array Nat} {bgp : Nat → Nat} {N : Nat} (ρ : RRec) {col : Nat}
    (h : 228 ≤ col) : fullCell ds pub bgp N ρ col = 0 := by
  have h1 : ¬ (31 ≤ col ∧ col < 43) := by omega
  simp only [fullCell, h1, if_false]
  cases ρ with
  | cl i =>
    simp only [baseCell, clCell]
    simp (disch := omega) only [if_neg]
    split <;> rfl
  | seg r s i =>
    simp (disch := omega) only [baseCell, segCell, if_neg]
    split
    all_goals (try simp (disch := omega) only [if_neg])
    all_goals (try split)
    all_goals (try simp (disch := omega) only [if_neg])

theorem mkTab_get_ge {H W : Nat} {f : Nat → Nat → Nat} {q col : Nat} (hc : W ≤ col) :
    ((mkTab H W f).getD q #[]).getD col 0 = 0 := by
  simp only [mkTab, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases (Array.range H)[q]? <;> simp [show ¬ col < W by omega]

/-! ## The table -/

section
variable {c : Claim} {e : Ext} (hg : Good c e)

theorem D_ok (hg : Good c e) : ∀ r, r < NN e → (Df c e r).r = r ∧ DOk (Df c e r) := by
  intro r hr
  refine ⟨Df_r hr, ?_⟩
  rw [Df_eq hr]
  have hm : e.rc r ∈ e.rs := by
    simp only [Ext.rc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < e.rs.length from hr),
      Option.getD_some]
    exact List.getElem_mem _
  have hs := List.all_eq_true.1 hg.inSlice _ hm
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨vp, vv⟩, vs⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
  have l1 := Link.valid_length vp; have l2 := Link.valid_length vv; have l3 := Link.valid_length vs
  simp only [DOk, rdOf, mkInfo_e, toNats, List.length_map]
  omega

theorem NN_pos (hg : Good c e) : 1 ≤ NN e := by
  have := hg.n_pos; have := hg.len; simp only [NN]; omega

include hg

theorem RL_adj : Adj2 (fun a b => b = nextOf (Df c e) a) (RL c e) := recs_adj (D_ok hg) (NN_pos hg)

theorem RL_ok : ∀ ρ ∈ RL c e, RecOk (NN e) (Df c e) ρ := recs_ok (D_ok hg)

theorem RL_last : (RL c e).getLast? = some (lastRec c e) := recs_last (D_ok hg) (NN_pos hg)

theorem RL_len : 13 ≤ (RL c e).length := by
  have hd := (segs_adj (D_ok hg) (NN e) (Nat.le_refl _)).2.1 (NN_pos hg)
  rw [RL, recs_eq, List.length_append, List.length_map, List.length_range]
  have : 0 < ((List.range (NN e)).flatMap fun r => segRecs (Df c e r)).length := by
    cases h : (List.range (NN e)).flatMap fun r => segRecs (Df c e r) with
    | nil => rw [h] at hd; cases hd
    | cons a l => simp
  omega

end

/-! ## Nodup -/

theorem chunk_nodup (d : RD) (s : Nat) : (chunk d s).Nodup := by
  simp only [chunk]
  exact List.Pairwise.map _ (fun a b h h' => h (by cases h'; rfl)) List.nodup_range

theorem fields_nodup (h : Bool) : (fields h).Nodup := by cases h <;> decide

theorem segRecs_nodup (d : RD) : (segRecs d).Nodup := by
  rw [segRecs_eq]
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun s _ => chunk_nodup d s, ?_⟩
  refine (fields_nodup d.hr).imp ?_
  intro s s' hne x hx y hy hxy
  simp only [chunk, List.mem_map, List.mem_range] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨i', -, rfl⟩ := hy
  cases hxy; exact hne rfl

theorem recs_nodup {N : Nat} {D : Nat → RD} (hD : ∀ r, r < N → (D r).r = r) : (recs N D).Nodup := by
  rw [recs_eq, List.nodup_append]
  refine ⟨List.Pairwise.map _ (fun a b h h' => h (by cases h'; rfl)) List.nodup_range, ?_, ?_⟩
  · unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun r _ => segRecs_nodup _, List.nodup_range.imp_of_mem ?_⟩
    intro r r' hr hr' hne x hx y hy hxy
    obtain ⟨s, i, rfl, -, -⟩ := segRecs_mem hx
    obtain ⟨s', i', rfl, -, -⟩ := segRecs_mem hy
    rw [hD r (List.mem_range.1 hr), hD r' (List.mem_range.1 hr')] at hxy
    cases hxy; exact hne rfl
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    simp only [List.mem_flatMap] at hb
    obtain ⟨r, -, hb⟩ := hb
    obtain ⟨s, i', rfl, -, -⟩ := segRecs_mem hb
    intro h; cases h

/-! ## The `rcpt` table of `render` -/

theorem rcpt_part (c : Claim) (e : Ext) : partOf (bundle c e) T_RCPT =
    mkTab (2 ^ logOf ((RL c e).length + 1)) Rcpt.width
      (fun q col => if q < (RL c e).length then Cc c e ((RL c e).getD q (.cl 0)) col else 0) := by
  show rcptRowsAll (mkInfo c e) = _
  simp only [rcptRowsAll, recs_rcptData]
  congr 1
  funext q col
  simp only [rcptCell, List.size_toArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

/-- Cells of the honest `rcpt` table. -/
def cellQ (c : Claim) (e : Ext) (q col : Nat) : Nat :=
  if q < (RL c e).length then Cc c e ((RL c e).getD q (.cl 0)) col else 0

theorem rcpt_log (c : Claim) (e : Ext) : (render c e).log T_RCPT = logOf ((RL c e).length + 1) :=
  (render_mkTab (by decide) (by decide) (rcpt_part c e)).1

theorem rcpt_height (c : Claim) (e : Ext) : (render c e).height T_RCPT = 2 ^ logOf ((RL c e).length + 1) :=
  (render_mkTab (by decide) (by decide) (rcpt_part c e)).2.1

theorem rcpt_cell (c : Claim) (e : Ext) {q : Nat} (hq : q < (render c e).height T_RCPT) (col : Nat) :
    (render c e).cell T_RCPT q col = Fp.ofNat (cellQ c e q col) := by
  rw [rcpt_height] at hq
  by_cases hc : col < Rcpt.width
  · exact (render_mkTab (by decide) (by decide) (rcpt_part c e)).2.2 q col hq hc
  · rw [render_cell c e (by decide) (by decide), rcpt_part, mkTab_get_ge (by omega), cellQ]
    split
    · rw [Cc, fullCell_ge _ (by simp [Rcpt.width] at hc; omega)]
    · rfl

/-! ## Row categories -/

section
variable {c : Claim} {e : Ext} (hg : Good c e)
include hg

theorem RL_nodup : (RL c e).Nodup := recs_nodup (fun r hr => (D_ok hg r hr).1)

theorem RL_get_last : (RL c e)[(RL c e).length - 1]'(by have := RL_len hg; omega) = lastRec c e := by
  have h := RL_last hg
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by have := RL_len hg; omega)] at h
  exact Option.some.inj h

theorem RL_get0 : (RL c e)[0]'(by have := RL_len hg; omega) = .cl 0 := by
  have := recs_get_cl (N := NN e) (D := Df c e) 0 (by omega)
  rw [← RL, List.getElem?_eq_getElem (by have := RL_len hg; omega)] at this
  exact Option.some.inj this

theorem getD_RL {q : Nat} (hq : q < (RL c e).length) : (RL c e).getD q (.cl 0) = (RL c e)[q] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]

/-- **A constraint holds on every row** of the honest `rcpt` table from the row categories. -/
theorem allRows_of {pub : List Fp} {x : Expr}
    (hA : ∀ ρ ∈ RL c e, ρ ≠ lastRec c e → nextOf (Df c e) ρ ∈ RL c e →
      evR (cF c e ρ) (cF c e (nextOf (Df c e) ρ)) (ρ == .cl 0) false pub x = 0)
    (hB : evR (cF c e (lastRec c e)) (fun _ => 0) false false pub x = 0)
    (hP : evR (fun _ => 0) (fun _ => 0) false false pub x = 0)
    (hW : evR (fun _ => 0) (cF c e (.cl 0)) false true pub x = 0) :
    ∀ q, q < (render c e).height T_RCPT → x.eval (render c e) T_RCPT q pub = 0 := by
  intro q hq
  have hH := rcpt_height c e
  have hL := RL_len hg
  have hLH : (RL c e).length + 1 ≤ (render c e).height T_RCPT := by rw [hH]; exact le_pow_logOf _
  have hcur : (render c e).cell T_RCPT q = fun col => Fp.ofNat (cellQ c e q col) := funext (rcpt_cell c e hq)
  rw [eval_evR, hcur]
  have zero : ∀ q', (RL c e).length ≤ q' → (fun col => Fp.ofNat (cellQ c e q' col)) = fun _ => 0 := by
    intro q' h; funext col; simp only [cellQ, show ¬ q' < (RL c e).length by omega, if_false]; rfl
  have atR : ∀ q' (h : q' < (RL c e).length), (fun col => Fp.ofNat (cellQ c e q' col)) = cF c e (RL c e)[q'] := by
    intro q' h; funext col; simp only [cellQ, h, if_true, getD_RL hg h]; rfl
  by_cases h1 : q + 1 < (RL c e).length
  · have hnx : (q + 1) % (render c e).height T_RCPT = q + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hnx, show (render c e).cell T_RCPT (q + 1) = fun col => Fp.ofNat (cellQ c e (q + 1) col) from
      funext (rcpt_cell c e (by omega))]
    have adj := (RL_adj hg).get q h1
    rw [atR q (by omega), atR (q + 1) h1, adj, show decide (q + 1 = (render c e).height T_RCPT) = false by
      simp only [decide_eq_false_iff_not]; omega]
    have hfst : decide (q = 0) = ((RL c e)[q] == .cl 0) := by
      by_cases hq0 : q = 0
      · subst hq0; simp [RL_get0 hg]
      · have : (RL c e)[q] ≠ .cl 0 := by
          intro heq
          rw [← RL_get0 hg] at heq
          exact hq0 ((RL_nodup hg).getElem_inj.1 heq)
        simp [hq0, this]
    rw [hfst]
    refine hA _ (List.getElem_mem _) ?_ ?_
    · intro heq
      rw [← RL_get_last hg] at heq
      have := (RL_nodup hg).getElem_inj.1 heq
      omega
    · rw [← adj]; exact List.getElem_mem _
  · by_cases h2 : q < (RL c e).length
    · have hq1 : q = (RL c e).length - 1 := by omega
      have hnx : (q + 1) % (render c e).height T_RCPT = q + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hnx, show (render c e).cell T_RCPT (q + 1) = fun col => Fp.ofNat (cellQ c e (q + 1) col) from
        funext (rcpt_cell c e (by omega)), zero (q + 1) (by omega), atR q h2]
      have : (RL c e)[q] = lastRec c e := by rw [← RL_get_last hg]; congr 1
      rw [this, show decide (q = 0) = false by simp only [decide_eq_false_iff_not]; omega,
        show decide (q + 1 = (render c e).height T_RCPT) = false by simp only [decide_eq_false_iff_not]; omega]
      exact hB
    · rw [zero q (by omega), show decide (q = 0) = false by simp only [decide_eq_false_iff_not]; omega]
      by_cases h3 : q + 1 < (render c e).height T_RCPT
      · rw [Nat.mod_eq_of_lt h3, show (render c e).cell T_RCPT (q + 1) = fun col => Fp.ofNat (cellQ c e (q + 1) col)
          from funext (rcpt_cell c e h3), zero (q + 1) (by omega),
          show decide (q + 1 = (render c e).height T_RCPT) = false by simp only [decide_eq_false_iff_not]; omega]
        exact hP
      · have hq1 : q + 1 = (render c e).height T_RCPT := by omega
        rw [hq1, Nat.mod_self, show (render c e).cell T_RCPT 0 = fun col => Fp.ofNat (cellQ c e 0 col)
          from funext (rcpt_cell c e (by omega)), atR 0 (by omega), RL_get0 hg]
        simpa using hW

end

end RcptP

end ZkFormal.Near.Render
