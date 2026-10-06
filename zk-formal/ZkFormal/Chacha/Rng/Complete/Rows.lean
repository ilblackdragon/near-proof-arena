import ZkFormal.Chacha.Rng.Complete.Basic

/-!
# ZkFormal.Chacha.Rng.Complete.Rows — the row structure of the honest `genV3` trace

* `Step X Y`: the legal (row, next row) pairs: inside a call, the last draw of a call or a
  padding row followed by a call start or padding (`StartOk`);
* `Links L Y`: consecutive rows of `L` (and its last row with `Y`) are `Step`s; closed under
  append (`links_append`), so `links_full` covers calls ++ padding;
* `step_at`: on every row `r < H`, (row `r`, row `(r+1) % H`) is a `Step` (cyclic wrap
  included); `valid_rowAt`, `row0_start`, height bounds.
-/

namespace ZkFormal.Chacha.Rng.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Gen

/-- Rows that may follow the end of a call (and row `0`): a call start or padding. -/
def StartOk (Y : Row) : Prop := Y = .pad ∨ ∃ C, Y = .draw C 0

/-- Legal (row, next row) pairs of the honest trace. -/
inductive Step : Row → Row → Prop
  | cont (C : Call) (hC : CallOk C) (d : Nat) (hd : d + 1 < nd C) : Step (.draw C d) (.draw C (d + 1))
  | last (C : Call) (hC : CallOk C) (d : Nat) (hd : d + 1 = nd C) (Y : Row) (hY : StartOk Y) :
      Step (.draw C d) Y
  | pad (Y : Row) (hY : StartOk Y) : Step .pad Y

theorem Step.valid {X Y : Row} (h : Step X Y) : Valid X := by
  cases h with
  | cont C hC d hd => exact (show CallOk C ∧ d < nd C from ⟨hC, by omega⟩)
  | last C hC d hd => exact (show CallOk C ∧ d < nd C from ⟨hC, by omega⟩)
  | pad => trivial

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

theorem callRows_length (C : Call) : (callRows C).length = nd C := by simp [callRows]

theorem callRows_getD (C : Call) {i : Nat} (hi : i < nd C) : (callRows C).getD i .pad = .draw C i := by
  simp [callRows, List.getD_eq_getElem?_getD, hi]

theorem links_call {C : Call} (hC : CallOk C) {Y : Row} (hY : StartOk Y) : Links (callRows C) Y := by
  intro i hi
  rw [callRows_length] at hi
  rw [callRows_getD C hi]
  by_cases h : i + 1 < nd C
  · rw [getD_app_left (by rw [callRows_length]; exact h), callRows_getD C h]
    exact Step.cont C hC i h
  · rw [getD_app_right (by rw [callRows_length]; omega), callRows_length,
      show i + 1 - nd C = 0 by omega, getD_single]
    exact Step.last C hC i (by omega) Y hY

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

theorem honestRows_cons (C : Call) (cs : List Call) :
    honestRows (C :: cs) = callRows C ++ honestRows cs := by
  simp [honestRows]

theorem links_full (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (k : Nat) {Y : Row}
    (hY : StartOk Y) :
    Links (honestRows calls ++ List.replicate k Row.pad) Y ∧
      StartOk ((honestRows calls ++ List.replicate k Row.pad ++ [Y]).getD 0 .pad) := by
  induction calls with
  | nil =>
    refine ⟨?_, ?_⟩
    · show Links ([] ++ List.replicate k Row.pad) Y
      rw [List.nil_append]; exact links_pad k hY
    · cases k with
      | zero => exact hY
      | succ k => exact Or.inl rfl
  | cons C cs ih =>
    have ih' := ih (fun C' h => hok C' (List.mem_cons_of_mem _ h))
    have hC := hok C List.mem_cons_self
    rw [honestRows_cons, List.append_assoc]
    refine ⟨links_append (links_call hC ih'.2) ih'.1, ?_⟩
    right; refine ⟨C, ?_⟩
    have hl : 0 < (callRows C).length := by rw [callRows_length]; exact nd_pos hC
    rw [List.append_assoc, getD_app_left hl, callRows_getD C (nd_pos hC)]

/-! ## Rows of the honest trace -/

/-- Row `r` of the honest table. -/
def rowAt (calls : List Call) (r : Nat) : Row := (honestRows calls).getD r .pad

theorem honestCell_eq (calls : List Call) (r c : Nat) :
    honestCell calls r c = rowCell (rowAt calls r) c := rfl

theorem rowAt_full (calls : List Call) (k r : Nat) :
    (honestRows calls ++ List.replicate k Row.pad).getD r .pad = rowAt calls r := by
  unfold rowAt
  by_cases h : r < (honestRows calls).length
  · rw [getD_app_left h]
  · rw [getD_app_right (by omega)]
    have e1 : (honestRows calls).getD r .pad = .pad := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [e1, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

theorem valid_rowAt (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (r : Nat) :
    Valid (rowAt calls r) := by
  unfold rowAt
  rw [List.getD_eq_getElem?_getD]
  cases h : (honestRows calls)[r]? with
  | none => trivial
  | some X =>
    have hm := List.mem_of_getElem? h
    simp only [honestRows, List.mem_flatMap] at hm
    obtain ⟨C, hC, hX⟩ := hm
    simp only [callRows, List.mem_map, List.mem_range] at hX
    obtain ⟨d, hd, rfl⟩ := hX
    exact (show CallOk C ∧ d < nd C from ⟨hok C hC, hd⟩)

theorem row0_start (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) : StartOk (rowAt calls 0) := by
  cases calls with
  | nil => exact Or.inl rfl
  | cons C cs =>
    have hC := hok C List.mem_cons_self
    right; refine ⟨C, ?_⟩
    unfold rowAt
    rw [honestRows_cons, getD_app_left (by rw [callRows_length]; exact nd_pos hC),
      callRows_getD C (nd_pos hC)]

/-! ## Height -/

theorem height_eq (calls : List Call) (t : Nat) :
    (honestTrace calls).height t = 2 ^ honestLog calls := rfl

theorem len_le_height (calls : List Call) (t : Nat) :
    (honestRows calls).length ≤ (honestTrace calls).height t := by
  rw [height_eq]
  exact Nat.le_trans (ZkFormal.Chacha.Complete.clog2_ge _)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem log_bounds (calls : List Call) (hrows : (honestRows calls).length ≤ 2 ^ Rng.Table.maxLog)
    (t : Nat) : 1 ≤ (honestTrace calls).log t ∧ (honestTrace calls).log t ≤ Rng.Table.maxLog := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  show max 1 (ZkFormal.Chacha.Gen.clog2 (honestRows calls).length) ≤ Rng.Table.maxLog
  have := ZkFormal.Chacha.Complete.clog2_le _ _ hrows
  have : 1 ≤ Rng.Table.maxLog := by decide
  omega

/-- **The transition structure**: every row and its cyclic successor form a `Step`. -/
theorem step_at (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t r : Nat)
    (hr : r < (honestTrace calls).height t) :
    Step (rowAt calls r) (rowAt calls ((r + 1) % (honestTrace calls).height t)) := by
  have hlen := len_le_height calls t
  generalize (honestTrace calls).height t = H at hr hlen
  obtain ⟨hL, -⟩ := links_full calls hok (H - (honestRows calls).length) (row0_start calls hok)
  have hlenF : (honestRows calls ++ List.replicate (H - (honestRows calls).length) Row.pad).length = H := by
    rw [List.length_append, List.length_replicate]; omega
  have := hL r (by rw [hlenF]; exact hr)
  rw [rowAt_full] at this
  by_cases h : r + 1 < H
  · rw [Nat.mod_eq_of_lt h]
    rw [getD_app_left (by rw [hlenF]; exact h), rowAt_full] at this
    exact this
  · rw [show r + 1 = H by omega, Nat.mod_self]
    rw [getD_app_right (by rw [hlenF]; omega), hlenF, show r + 1 - H = 0 by omega, getD_single] at this
    exact this

end ZkFormal.Chacha.Rng.Complete
