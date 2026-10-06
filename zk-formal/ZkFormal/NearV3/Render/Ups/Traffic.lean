import ZkFormal.NearV3.Render.Ups.Rows
import ZkFormal.NearV3.Extract.Ups.Proof

/-!
# ZkFormal.NearV3.Render.Ups.Traffic — traffic of the honest `upsV3` table

The honest table's instance segments are `segsOf insts` (instance `i` occupies rows
`start i … start i + |recsI|−1`).  For a trace with the generator's cells and a locally legal
table, **`ups_render_traffic`**: the traffic is `upsTraffic` of the view of these segments
(`UpsRows.viewOf`, the view `ups_view` extracts); **`ups_render_view`**: the view's rows are the
generator's cells (as canonical naturals of their images in `Fp`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.NearV3.UpsRows

namespace UpsGen

variable {insts : List UpsInst}

/-- First row of instance `i`. -/
def start (insts : List UpsInst) (i : Nat) : Nat := ((List.range i).map fun j => (recsI (inst insts j)).length).sum

/-- The instance segments `(start, length)`. -/
def segsOf (insts : List UpsInst) : List (Nat × Nat) :=
  (List.range insts.length).map fun i => (start insts i, (recsI (inst insts i)).length)

theorem flatMap_len {β : Type} (f : Nat → List β) : ∀ n,
    ((List.range n).flatMap f).length = ((List.range n).map fun j => (f j).length).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_len f n, List.map_append,
      List.sum_append]; simp

theorem sum_mono {g : Nat → Nat} : ∀ {i n}, i ≤ n →
    ((List.range i).map g).sum ≤ ((List.range n).map g).sum
  | i, 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | i, n + 1, h => by
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · have := sum_mono (g := g) (i := i) (n := n) (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]; simp; omega
    · rw [show i = n + 1 by omega]; exact Nat.le_refl _

theorem flatMap_getD_pre {β : Type} (f : Nat → List β) (d0 : β) : ∀ n i e, i < n → e < (f i).length →
    ((List.range n).flatMap f).getD (((List.range i).map fun j => (f j).length).sum + e) d0 = (f i).getD e d0
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, i, e, hi, he => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge i n with h | h
    · have hl : ((List.range i).map fun j => (f j).length).sum + e < ((List.range n).flatMap f).length := by
        rw [flatMap_len]
        have := sum_mono (g := fun j => (f j).length) (i := i + 1) (n := n) (by omega)
        rw [List.range_succ, List.map_append, List.sum_append] at this; simp at this; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
      exact flatMap_getD_pre f d0 n i e h he
    · have hin : i = n := by omega
      subst hin
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [flatMap_len]; omega), flatMap_len]
      simp [List.getD_eq_getElem?_getD]

theorem recs_seg {i d : Nat} (hi : i < insts.length) (hd : d < (recsI (inst insts i)).length) :
    (recs insts).getD (start insts i + d) default = (i, (recsI (inst insts i)).getD d default) := by
  unfold recs start
  have := flatMap_getD_pre (fun i => (recsI (insts.getD i default)).map ((i, ·))) default insts.length i d hi
    (by simp only [List.length_map]; exact hd)
  simp only [List.length_map] at this
  rw [show inst insts = fun j => insts.getD j default from rfl]
  simp only at hd ⊢
  rw [this]
  have hd' : d < (recsI (insts.getD i default)).length := hd
  simp only [List.getD_eq_getElem?_getD] at hd' ⊢
  simp [List.getElem?_eq_getElem hd']

theorem start_succ (i : Nat) : start insts (i + 1) = start insts i + (recsI (inst insts i)).length := by
  simp [start, List.range_succ]

theorem segs_consec : ∀ n s0, (∀ i, s0 = start insts i → True) →
    Consec (start insts 0) ((List.range n).map fun i => (start insts i, (recsI (inst insts i)).length)) := by
  intro n _ _
  suffices h : ∀ m, Consec (start insts m) ((List.range' m n).map fun i => (start insts i, (recsI (inst insts i)).length)) by
    have := h 0; rwa [List.range_eq_range']
  induction n with
  | zero => intro m; simp [Consec]
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons]
    exact ⟨rfl, by rw [← start_succ]; exact ih (m + 1)⟩

theorem segEnd_eq : ∀ n m, segEnd (start insts m) ((List.range' m n).map fun i =>
    (start insts i, (recsI (inst insts i)).length)) = start insts (m + n)
  | 0, m => by simp [segEnd]
  | n + 1, m => by
    rw [List.range'_succ, List.map_cons]
    simp only [segEnd]
    rw [← start_succ, segEnd_eq n (m + 1), show m + 1 + n = m + (n + 1) by omega]

theorem start_len : start insts insts.length = R insts := by
  unfold start R recs
  rw [flatMap_len]
  simp [inst]

theorem segEnd_R : segEnd 0 (segsOf insts) = R insts := by
  have := segEnd_eq (insts := insts) insts.length 0
  rw [List.range_eq_range'.symm, show start insts 0 = 0 from rfl] at this
  rw [segsOf, this, Nat.zero_add, start_len]

/-! ## Cells as canonical naturals -/

theorem toNat_int1 : ((1 : Int) : Fp).toNat = 1 := rfl
theorem toNat_int0 : ((0 : Int) : Fp).toNat = 0 := rfl

section
variable {tr : Trace Fp} {t : Nat}
  (hcell : ∀ r x, r < tr.height t → x < 187 → tr.cell t r x = ((cell insts r x : Int) : Fp))
include hcell

theorem rowC_cell {r x : Nat} (hr : r < tr.height t) (hx : x < 187) :
    rowC tr t r x = ((cell insts r x : Int) : Fp).toNat := by
  show (tr.cell t r x).toNat = _
  rw [hcell r x hr hx]

end

/-- Row-kind cells of an active row. -/
theorem cell_act {r : Nat} (hr : r < R insts) : cell insts r UpsV3.act = 1 := by
  simp only [cell, hr, if_true, rowCell]
  generalize (recs insts).getD r default = a
  obtain ⟨i, rk⟩ := a
  cases rk <;> rfl

theorem cell_pad {r x : Nat} (hr : ¬ r < R insts) : cell insts r x = 0 := by
  simp [cell, hr]

theorem cell_sf {r : Nat} (hr : r < R insts) :
    cell insts r UpsV3.sf = if ((recs insts).getD r default).2 = RK.w 0 then 1 else 0 := by
  simp only [cell, hr, if_true, rowCell]
  generalize (recs insts).getD r default = a
  obtain ⟨i, rk⟩ := a
  cases rk with
  | w t => by_cases h : t = 0 <;> simp [h, wCell, isSeg, UpsV3.sf, ind]
  | v p => simp [vCell, isSeg, UpsV3.sf]
  | q k p => simp [qCell, isSeg, isPC, qRowCell, qRow, UpsV3.sf]

theorem qc3 (r i k p : Nat) : rowCell insts r (i, .q k p) 3 = 1 := rfl
theorem qc9 (r i k p : Nat) : rowCell insts r (i, .q k p) 9 = ind (p + 1 = (part (inst insts i) k).q.length) := rfl
theorem qc79 (r i k p : Nat) : rowCell insts r (i, .q k p) 79 = ind (k + 1 = nQ (inst insts i)) := rfl
theorem wc3 (r i t : Nat) : rowCell insts r (i, .w t) 3 = 0 := rfl
theorem vc3 (r i p : Nat) : rowCell insts r (i, .v p) 3 = 0 := rfl

/-- `qb·pl·rootP` of an active row: its instance's last row. -/
theorem cell_last {r : Nat} (hr : r < R insts) :
    (cell insts r UpsV3.qb = 1 ∧ cell insts r UpsV3.pl = 1 ∧ cell insts r UpsV3.rootP = 1) ↔
      nextRK (inst insts ((recs insts).getD r default).1) ((recs insts).getD r default).2 = none := by
  have hm := (mem_recs.1 (getD_mem hr)).2
  simp only [cell, hr, if_true]
  generalize (recs insts).getD r default = a at hm
  obtain ⟨i, rk⟩ := a
  cases rk with
  | w t =>
    rw [show UpsV3.qb = 3 from rfl, wc3]
    simp only [nextRK]
    constructor
    · intro h; exact absurd h.1 (by decide)
    · intro h; split at h <;> simp at h
  | v p =>
    rw [show UpsV3.qb = 3 from rfl, vc3]
    simp only [nextRK]
    constructor
    · intro h; exact absurd h.1 (by decide)
    · intro h; split at h <;> simp at h
  | q k p =>
    obtain ⟨k', p', hk, hp, he⟩ : ∃ k' p', k' < nQ (inst insts i) ∧ p' < (part (inst insts i) k').q.length ∧
        RK.q k p = RK.q k' p' := by
      rcases mem_recsI.1 hm with ⟨t, -, h⟩ | ⟨p', -, h⟩ | ⟨k', p', hk, hp, h⟩
      · cases h
      · cases h
      · exact ⟨k', p', hk, hp, h⟩
    cases he
    rw [show UpsV3.qb = 3 from rfl, show UpsV3.pl = 9 from rfl, show UpsV3.rootP = 79 from rfl, qc3, qc9, qc79]
    simp only [nextRK]
    by_cases h1 : p + 1 = (part (inst insts i) k).q.length
    · by_cases h2 : k + 1 = nQ (inst insts i)
      · rw [if_neg (by omega), if_neg (by omega)]; simp [ind, h1, h2]
      · rw [if_neg (by omega), if_pos (by omega)]; simp [ind, h2]
    · rw [if_pos (by omega)]; simp [ind, h1]

theorem cell_notlast {r : Nat} (hr : r < R insts)
    (h : nextRK (inst insts ((recs insts).getD r default).1) ((recs insts).getD r default).2 ≠ none) :
    cell insts r UpsV3.qb = 0 ∨ cell insts r UpsV3.pl = 0 ∨ cell insts r UpsV3.rootP = 0 := by
  simp only [cell, hr, if_true]
  generalize (recs insts).getD r default = a at h
  obtain ⟨i, rk⟩ := a
  cases rk with
  | w t => left; rfl
  | v p => left; rfl
  | q k p =>
    right
    rw [show UpsV3.pl = 9 from rfl, show UpsV3.rootP = 79 from rfl, qc9, qc79]
    simp only [nextRK] at h
    by_cases h1 : p + 1 < (part (inst insts i) k).q.length
    · left; simp [ind]; omega
    · right; rw [if_neg h1] at h
      by_cases h2 : k + 1 < nQ (inst insts i)
      · simp [ind]; omega
      · rw [if_neg h2] at h; exact absurd rfl h

theorem consec_segs : Consec 0 (segsOf insts) := by
  have := segs_consec (insts := insts) insts.length 0 (fun _ _ => trivial)
  exact this

theorem recsI_next {I : UpsInst} (hL : 1 ≤ L I) (hQ : 1 ≤ nQ I) (hq : ∀ k, k < nQ I → 1 ≤ (part I k).q.length)
    {d : Nat} (hd : d + 1 < (recsI I).length) :
    nextRK I ((recsI I).getD d default) = some ((recsI I).getD (d + 1) default) := by
  have := (recsI_adj hL hQ hq).get d hd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hd]
  exact this

theorem nextRK_ne_w0 {I : UpsInst} {a b : RK} (h : nextRK I a = some b) : b ≠ RK.w 0 := by
  cases a with
  | w t => simp only [nextRK] at h; split at h <;> (cases h; simp)
  | v p => simp only [nextRK] at h; split at h <;> (cases h; simp)
  | q k p => simp only [nextRK] at h; split at h <;> (try split at h) <;> (try (cases h; simp)) <;> simp at h

theorem recsI_len4 (I : UpsInst) : 4 ≤ (recsI I).length := by simp [recsI]

theorem recsI_get0 (I : UpsInst) : (recsI I).getD 0 default = RK.w 0 := by
  simp [recsI, List.getD_eq_getElem?_getD, List.range_succ_eq_map]

theorem recsI_getLast {I : UpsInst} (hL : 1 ≤ L I) (hQ : 1 ≤ nQ I) (hq : ∀ k, k < nQ I → 1 ≤ (part I k).q.length) :
    (recsI I).getD ((recsI I).length - 1) default = lastRK I := by
  have h := recsI_last hL hQ hq
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- The honest table's rows: segments, `act`, `sf`, last rows. -/
theorem segs_isSeg (hs : UpsShape insts) {tr : Trace Fp} {t : Nat} (hH : R insts + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < 187 → tr.cell t r x = ((cell insts r x : Int) : Fp)) :
    ∀ p ∈ segsOf insts, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2 := by
  intro p hp
  simp only [segsOf, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hm := inst_mem hi
  have hL := hs.L1 _ hm
  have hQ := hs.nQ1 _ hm
  have hq := hs.q1 _ hm
  have h4 := recsI_len4 (inst insts i)
  have hend : start insts i + (recsI (inst insts i)).length ≤ R insts := by
    rw [← start_succ, ← start_len]
    exact sum_mono (by omega)
  have hrow : ∀ d, d < (recsI (inst insts i)).length → start insts i + d < R insts := fun d hd => by omega
  have hrec := fun d (hd : d < (recsI (inst insts i)).length) => recs_seg (insts := insts) hi hd
  have hC := fun r x (hr : r < R insts) (hx : x < 187) => rowC_cell hcell (r := r) (x := x) (by omega) hx
  simp only
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [firstB, decide_eq_true_eq]
    have := hrow 0 (by omega)
    rw [hC _ _ (by simpa using this) (by decide), cell_sf (by simpa using this)]
    rw [show start insts i = start insts i + 0 by omega, hrec 0 (by omega), recsI_get0]; rfl
  · simp only [lastB, decide_eq_true_eq]
    have hr := hrow ((recsI (inst insts i)).length - 1) (by omega)
    have hr' : start insts i + (recsI (inst insts i)).length - 1 < tr.height t := by omega
    rw [hC _ _ (by omega) (by decide), hC _ _ (by omega) (by decide), hC _ _ (by omega) (by decide)]
    have e : start insts i + (recsI (inst insts i)).length - 1 = start insts i + ((recsI (inst insts i)).length - 1) := by omega
    have := (cell_last (insts := insts) (r := start insts i + ((recsI (inst insts i)).length - 1)) hr).2 (by
      rw [hrec _ (by omega), recsI_getLast hL hQ hq]; exact next_last hL hQ hq)
    rw [e, this.1, this.2.1, this.2.2]
    exact ⟨rfl, rfl, rfl⟩
  · intro r h1 h2
    simp only [actB, decide_eq_true_eq]
    rw [hC _ _ (by omega) (by decide), cell_act (by omega)]; rfl
  · intro r h1 h2
    simp only [firstB, decide_eq_false_iff_not]
    obtain ⟨d, rfl⟩ : ∃ d, r = start insts i + (d + 1) := ⟨r - start insts i - 1, by omega⟩
    rw [hC _ _ (by omega) (by decide), cell_sf (by omega), hrec _ (by omega)]
    have := nextRK_ne_w0 (recsI_next hL hQ hq (d := d) (by omega))
    simp only [this, if_false]; decide
  · intro r h1 h2
    simp only [lastB, decide_eq_false_iff_not]
    obtain ⟨d, rfl⟩ : ∃ d, r = start insts i + d := ⟨r - start insts i, by omega⟩
    rw [hC _ _ (by omega) (by decide), hC _ _ (by omega) (by decide), hC _ _ (by omega) (by decide)]
    have := cell_notlast (insts := insts) (r := start insts i + d) (by omega) (by
      rw [hrec _ (by omega), recsI_next hL hQ hq (by omega)]; simp)
    rcases this with h | h | h <;> rw [h] <;> simp [toNat_int0]

theorem height_ge {tr : Trace Fp} {t : Nat} (hlog : tr.log t = logOf (R insts + 1)) : R insts + 1 ≤ tr.height t := by
  simp only [Trace.height, hlog]; exact le_pow_logOf _

end UpsGen

open UpsGen in
/-- **The honest `upsV3` table has the traffic of its view.**  For a trace whose table `t` has
height `2^logOf (R + 1)` and the generator's cells, and which is locally legal
(`ups_render_local`): the traffic is `upsTraffic` of the view of the instance segments
`segsOf insts` (the view `ups_view` extracts). -/
theorem ups_render_traffic (insts : List UpsInst) (hs : UpsShape insts) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t = logOf (R insts + 1))
    (hcell : ∀ r x, r < tr.height t → x < 187 → tr.cell t r x = ((cell insts r x : Int) : Fp)) :
    TableTraffic UpsV3.interactions tr t pub (upsTraffic (UpsRows.viewOf tr t (segsOf insts))) := by
  have hH := height_ge hlog
  refine UpsRows.viewTraffic hL consec_segs (by rw [segEnd_R]; omega) (segs_isSeg hs hH hcell) ?_
  intro r h1 h2
  rw [segEnd_R] at h1
  simp only [UpsRows.actB, decide_eq_false_iff_not]
  rw [rowC_cell hcell h2 (by decide), cell_pad (by omega)]
  decide

open UpsGen in
/-- **The view's rows are the generator's cells** (canonical naturals of their images in `Fp`):
row `d` of instance `i`'s segment is generator row `start i + d`. -/
theorem ups_render_view (insts : List UpsInst) (hs : UpsShape insts) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t = logOf (R insts + 1))
    (hcell : ∀ r x, r < tr.height t → x < 187 → tr.cell t r x = ((cell insts r x : Int) : Fp))
    {i d x : Nat} (hi : i < insts.length) (hd : d < (recsI (inst insts i)).length) (hx : x < 187) :
    ((UpsRows.viewOf tr t (segsOf insts)).getD i ⟨[], fun _ => 0⟩).row d x =
      ((rowCell insts (start insts i + d) (i, (recsI (inst insts i)).getD d default) x : Int) : Fp).toNat := by
  have hH := height_ge hlog
  have hend : start insts i + (recsI (inst insts i)).length ≤ R insts := by
    rw [← start_succ, ← start_len]; exact sum_mono (by omega)
  have hseg : (UpsRows.viewOf tr t (segsOf insts)).getD i ⟨[], fun _ => 0⟩ =
      UpsRows.segOf tr t (start insts i, (recsI (inst insts i)).length) := by
    simp [UpsRows.viewOf, segsOf, List.getD_eq_getElem?_getD, hi]
  rw [hseg, UpsRows.segOf_row tr t _ hd, rowC_cell hcell (by omega) hx]
  simp only [cell, show start insts i + d < R insts by omega, if_true, recs_seg hi hd]

end ZkFormal.NearV3.Render
