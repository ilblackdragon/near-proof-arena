import ZkFormal.Chacha.Shuffle.Complete.Basic

/-!
# ZkFormal.Chacha.Shuffle.Complete.Rows — the row structure of the honest `shufV3` trace

* `Step X Y`: the legal (row, next row) pairs: step `q ≥ 1` of an instance followed by row
  `q − 1` of the same instance; the final row (`q = 0`) or a padding row followed by the first
  row of an instance or padding (`StartOk`);
* `Links L Y`: consecutive rows of `L` (and its last row with `Y`) are `Step`s; `links_full`;
* `Valid X r`: row `r` is position `q < L` of a supported instance starting at row
  `s = r − (L − 1 − q)`, or padding (`valid_rowAt`);
* `step_at`: on every row `r < H`, (row `r`, row `(r+1) % H`) is a `Step` (cyclic wrap
  included); height bounds.
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen

/-- Rows that may follow a final row (and row `0`): the first row of an instance or padding. -/
def StartOk (Y : Row) : Prop := Y = .pad ∨ ∃ I s, InstOk I ∧ Y = .pos I s (I.L - 1)

/-- Legal (row, next row) pairs of the honest trace. -/
inductive Step : Row → Row → Prop
  | cont (I : SInst) (s q : Nat) (hI : InstOk I) (h1 : 1 ≤ q) (h2 : q < I.L) :
      Step (.pos I s q) (.pos I s (q - 1))
  | last (I : SInst) (s : Nat) (hI : InstOk I) (Y : Row) (hY : StartOk Y) : Step (.pos I s 0) Y
  | pad (Y : Row) (hY : StartOk Y) : Step .pad Y

/-! ## Chains of rows -/

def Links (L : List Row) (Y : Row) : Prop :=
  ∀ i, i < L.length → Step (L.getD i .pad) ((L ++ [Y]).getD (i + 1) .pad)

theorem getD_app_left {L1 L2 : List Row} {i : Nat} (h : i < L1.length) :
    (L1 ++ L2).getD i .pad = L1.getD i .pad := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {L1 L2 : List Row} {i : Nat} (h : L1.length ≤ i) :
    (L1 ++ L2).getD i .pad = L2.getD (i - L1.length) .pad := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_single (x : Row) : [x].getD 0 .pad = x := rfl

theorem links_append {L1 L2 : List Row} {Y : Row} (h1 : Links L1 ((L2 ++ [Y]).getD 0 .pad))
    (h2 : Links L2 Y) : Links (L1 ++ L2) Y := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hi1 : i < L1.length
  · have := h1 i hi1
    rw [getD_app_left hi1, List.append_assoc]
    by_cases hi2 : i + 1 < L1.length
    · rw [getD_app_left hi2]; rw [getD_app_left hi2] at this; exact this
    · have e : i + 1 = L1.length := by omega
      rw [getD_app_right (by omega), e, Nat.sub_self]
      rw [getD_app_right (by omega), e, Nat.sub_self, getD_single] at this
      exact this
  · have := h2 (i - L1.length) (by omega)
    rw [getD_app_right (by omega), List.append_assoc, getD_app_right (by omega),
      show i + 1 - L1.length = i - L1.length + 1 by omega]
    exact this

theorem instRows_length (I : SInst) (s : Nat) : (instRows I s).length = I.L := by simp [instRows]

theorem instRows_getD (I : SInst) (s : Nat) {i : Nat} (hi : i < I.L) :
    (instRows I s).getD i .pad = .pos I s (I.L - 1 - i) := by
  simp [instRows, List.getD_eq_getElem?_getD, hi]

theorem links_inst {I : SInst} (hI : InstOk I) (s : Nat) {Y : Row} (hY : StartOk Y) :
    Links (instRows I s) Y := by
  intro i hi
  rw [instRows_length] at hi
  rw [instRows_getD I s hi]
  by_cases h : i + 1 < I.L
  · rw [getD_app_left (by rw [instRows_length]; exact h), instRows_getD I s h,
      show I.L - 1 - (i + 1) = (I.L - 1 - i) - 1 by omega]
    exact Step.cont I s _ hI (by omega) (by omega)
  · rw [getD_app_right (by rw [instRows_length]; omega), instRows_length,
      show i + 1 - I.L = 0 by omega, getD_single, show I.L - 1 - i = 0 by omega]
    exact Step.last I s hI Y hY

theorem links_pad (k : Nat) {Y : Row} (hY : StartOk Y) : Links (List.replicate k Row.pad) Y := by
  intro i hi
  rw [List.length_replicate] at hi
  have e : (List.replicate k Row.pad).getD i .pad = .pad := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [e]
  apply Step.pad
  by_cases h : i + 1 < k
  · rw [getD_app_left (by rw [List.length_replicate]; exact h)]
    left; simp [List.getD_eq_getElem?_getD, h]
  · rw [getD_app_right (by rw [List.length_replicate]; omega), List.length_replicate,
      show i + 1 - k = 0 by omega, getD_single]
    exact hY

theorem honestRowsFrom_cons (I : SInst) (Is : List SInst) (s : Nat) :
    honestRowsFrom (I :: Is) s = instRows I s ++ honestRowsFrom Is (s + I.L) := rfl

theorem links_full (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (s k : Nat) {Y : Row}
    (hY : StartOk Y) :
    Links (honestRowsFrom insts s ++ List.replicate k Row.pad) Y ∧
      StartOk ((honestRowsFrom insts s ++ List.replicate k Row.pad ++ [Y]).getD 0 .pad) := by
  induction insts generalizing s with
  | nil =>
    refine ⟨?_, ?_⟩
    · show Links ([] ++ List.replicate k Row.pad) Y
      rw [List.nil_append]; exact links_pad k hY
    · cases k with
      | zero => exact hY
      | succ k => exact Or.inl rfl
  | cons I Is ih =>
    have ih' := ih (fun I' h => hok I' (List.mem_cons_of_mem _ h)) (s + I.L)
    have hI := hok I List.mem_cons_self
    rw [honestRowsFrom_cons, List.append_assoc]
    refine ⟨links_append (links_inst hI s ih'.2) ih'.1, ?_⟩
    right; refine ⟨I, s, hI, ?_⟩
    have hl : 0 < (instRows I s).length := by rw [instRows_length]; exact hI.L_pos
    rw [List.append_assoc, getD_app_left hl, instRows_getD I s hI.L_pos, Nat.sub_zero]

/-! ## Rows of the honest trace -/

/-- Row `r` of the honest table. -/
def rowAt (insts : List SInst) (r : Nat) : Row := (honestRows insts).getD r .pad

theorem honestCell_eq (insts : List SInst) (r c : Nat) :
    honestCell insts r c = rowCell (rowAt insts r) r c := rfl

theorem rowAt_full (insts : List SInst) (k r : Nat) :
    (honestRows insts ++ List.replicate k Row.pad).getD r .pad = rowAt insts r := by
  unfold rowAt
  by_cases h : r < (honestRows insts).length
  · rw [getD_app_left h]
  · rw [getD_app_right (by omega)]
    have e1 : (honestRows insts).getD r .pad = .pad := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [e1, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

/-- Row `r` is position `q` of a supported instance starting at row `s`, or padding. -/
def Valid : Row → Nat → Prop
  | .pos I s q, r => InstOk I ∧ q < I.L ∧ r = s + (I.L - 1 - q)
  | .pad, _ => True

theorem rowsFrom_pos : ∀ (insts : List SInst) (s0 e : Nat) {I : SInst} {s q : Nat},
    (∀ I ∈ insts, InstOk I) → (honestRowsFrom insts s0).getD e .pad = .pos I s q →
    InstOk I ∧ q < I.L ∧ s0 + e = s + (I.L - 1 - q)
  | [], _, _, _, _, _, _, h => by simp [honestRowsFrom, List.getD_eq_getElem?_getD] at h
  | I0 :: Is, s0, e, I, s, q, hok, h => by
    rw [honestRowsFrom_cons] at h
    by_cases he : e < I0.L
    · rw [getD_app_left (by rw [instRows_length]; exact he), instRows_getD I0 s0 he] at h
      injection h with h1 h2 h3
      subst h1 h2 h3
      exact ⟨hok I0 List.mem_cons_self, by omega, by omega⟩
    · rw [getD_app_right (by rw [instRows_length]; omega), instRows_length] at h
      have := rowsFrom_pos Is (s0 + I0.L) (e - I0.L) (fun I' h' => hok I' (List.mem_cons_of_mem _ h')) h
      exact ⟨this.1, this.2.1, by omega⟩

theorem valid_rowAt (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (r : Nat) :
    Valid (rowAt insts r) r := by
  generalize hX : rowAt insts r = X
  cases X with
  | pad => trivial
  | pos I s q =>
    have := rowsFrom_pos insts 0 r hok hX
    exact ⟨this.1, this.2.1, by omega⟩

/-! ## Height -/

theorem clog2_go_ge (n : Nat) : ∀ fuel acc, n ≤ 2 ^ (acc + fuel) → n ≤ 2 ^ clog2.go n fuel acc
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · assumption
    · exact clog2_go_ge n fuel (acc + 1) (by rw [show acc + 1 + fuel = acc + (fuel + 1) by omega]; exact h)

theorem clog2_go_le (n m : Nat) (hm : n ≤ 2 ^ m) : ∀ fuel acc, acc ≤ m → clog2.go n fuel acc ≤ m
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · exact h
    · next hn =>
      apply clog2_go_le n m hm fuel (acc + 1)
      have : acc ≠ m := fun e => hn (e ▸ hm)
      omega

theorem clog2_ge (n : Nat) : n ≤ 2 ^ clog2 n :=
  clog2_go_ge n n 0 (by simpa using Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))

theorem clog2_le (n m : Nat) (hm : n ≤ 2 ^ m) : clog2 n ≤ m :=
  clog2_go_le n m hm n 0 (Nat.zero_le _)

theorem height_eq (insts : List SInst) (t : Nat) :
    (honestTrace insts).height t = 2 ^ honestLog insts := rfl

theorem len_le_height (insts : List SInst) (t : Nat) :
    (honestRows insts).length ≤ (honestTrace insts).height t := by
  rw [height_eq]
  exact Nat.le_trans (clog2_ge _) (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem log_bounds (insts : List SInst) (hrows : (honestRows insts).length ≤ 2 ^ maxLog) (t : Nat) :
    1 ≤ (honestTrace insts).log t ∧ (honestTrace insts).log t ≤ maxLog := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  show max 1 (clog2 (honestRows insts).length) ≤ maxLog
  have := clog2_le _ _ hrows
  have : 1 ≤ maxLog := by decide
  omega

theorem height_le (insts : List SInst) (hrows : (honestRows insts).length ≤ 2 ^ maxLog) (t : Nat) :
    (honestTrace insts).height t ≤ 2 ^ 20 :=
  Nat.pow_le_pow_right (by decide) (log_bounds insts hrows t).2

/-- **The transition structure**: every row and its cyclic successor form a `Step`. -/
theorem step_at (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (t r : Nat)
    (hr : r < (honestTrace insts).height t) :
    Step (rowAt insts r) (rowAt insts ((r + 1) % (honestTrace insts).height t)) := by
  have hlen := len_le_height insts t
  generalize (honestTrace insts).height t = H at hr hlen
  have hY : StartOk (rowAt insts 0) := by
    have := (links_full insts hok 0 0 (Y := .pad) (Or.inl rfl)).2
    simp only [List.replicate_zero, List.append_nil] at this
    unfold rowAt honestRows
    by_cases h0 : 0 < (honestRowsFrom insts 0).length
    · rwa [getD_app_left h0] at this
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Or.inl rfl
  obtain ⟨hL0, -⟩ := links_full insts hok 0 (H - (honestRows insts).length) hY
  have hL : Links (honestRows insts ++ List.replicate (H - (honestRows insts).length) Row.pad)
      (rowAt insts 0) := hL0
  have hlenF : (honestRows insts ++ List.replicate (H - (honestRows insts).length) Row.pad).length = H := by
    rw [List.length_append, List.length_replicate]; omega
  have := hL r (by rw [hlenF]; exact hr)
  have e := rowAt_full insts (H - (honestRows insts).length)
  rw [e] at this
  by_cases h : r + 1 < H
  · rw [Nat.mod_eq_of_lt h]
    rw [getD_app_left (by rw [hlenF]; exact h), e] at this
    exact this
  · rw [show r + 1 = H by omega, Nat.mod_self]
    rw [getD_app_right (by rw [hlenF]; omega), hlenF, show r + 1 - H = 0 by omega, getD_single] at this
    exact this

/-! ## Honest cells are `< p` -/

theorem rowCell_lt {X : Row} {r : Nat} (hX : Valid X r) (hr : r < 2 ^ 20) (c : Nat) :
    rowCell X r c < 2013265921 := by
  cases X with
  | pad =>
    show (if c = colRc then r else 0) < _
    split <;> omega
  | pos I s q =>
    obtain ⟨hI, hq, hrs⟩ := hX
    exact cell_lt hI hq (by omega) hr c

theorem rowCell_bool (X : Row) (r : Nat) {c : Nat} (hc : c ∈ boolCols) : rowCell X r c ≤ 1 := by
  cases X with
  | pad =>
    show (if c = colRc then r else 0) ≤ 1
    have : c ≠ colRc := by
      unfold boolCols at hc; have := List.mem_range'_1.mp hc; unfold colRc; omega
    rw [iteF this]; omega
  | pos I s q => exact cell_bool I s r q hc

theorem rowCell_rc (X : Row) (r : Nat) : rowCell X r colRc = r := by
  cases X <;> rfl

end ZkFormal.Chacha.Shuffle.Complete
