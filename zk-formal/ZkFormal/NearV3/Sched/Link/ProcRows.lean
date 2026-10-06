import ZkFormal.NearV3.Sched.View.ProcInst

/-!
# ZkFormal.NearV3.Sched.Link.ProcRows — the rows of one instance of `sprV3`

Global facts about the process table (from `PLocal`, height `≤ 2^22`):

* `kc_le`: every key row has `kc ≤ 15`;
* `act_prev`, `tau_mono`: active rows form a prefix, and `τ` does not decrease along them;
* `tau_blk`: a key block start `f > 0` has `τ_f = τ_{f−1} + 1`;
* `Inst tr tp f m`: the facts of `proc_rounds` for the round count `m` (`inst_exists`);
* `entRows`: the entry rows `h_i + 1 + j` (`i < m`, `j < Lr_i`) of the instance, strictly
  increasing (`entRows_nodup`);
* **`ent_iff`**: a row is an entry row of the instance iff it is an entry (`kE = 1`) with the
  instance's `τ`.
-/

namespace ZkFormal.NearV3.Sched.Proc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem act_prev (hL : PLocal tr tp pub) {w : Nat} (hw1 : w + 1 < tr.height tp)
    (ha : cv tr tp (w + 1) act = 1) : cv tr tp w act = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (kinds hL (show w < tr.height tp by omega)).1 with h | h
  · have := pad_next hL hw1 h; omega
  · exact h

/-- Every key row has `kc ≤ 15`. -/
theorem kc_le (hL : PLocal tr tp pub) :
    ∀ w, w < tr.height tp → cv tr tp w kK = 1 → cv tr tp w kc ≤ 15 := by
  intro w
  induction w with
  | zero => intro h0 _; rw [(row_first hL h0).1]; omega
  | succ w ih =>
    intro hw1 hk1
    have hw : w < tr.height tp := by omega
    have K1 := kinds hL hw1
    have ha : cv tr tp w act = 1 := act_prev hL hw1 (by omega)
    have K0 := kinds hL hw
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.1 with k0 | k0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h0 | h0
      · have hE : cv tr tp w kE = 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.2.2.2.1 with hl | hl
        · have := (round_next hL hw (Or.inr ⟨hE, hl⟩)).2.1; omega
        · rw [(blk_next hL hw (Or.inr hl) hw1 hk1).1]; omega
      · have := (round_next hL hw (Or.inl h0)).2.1; omega
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.1 with hl | hl
      · have hne : cv tr tp w kc ≠ 15 := fun h => by
          have := ((kl_iff hL hw).2 k0).2 h; omega
        have := ih hw k0
        rw [(key_next hL hw k0 hl).2.2.1]
        omega
      · rw [(blk_next hL hw (Or.inl hl) hw1 hk1).1]; omega

/-- `τ` does not decrease along active rows. -/
theorem tau_mono (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (w : Nat) :
    ∀ d, w + d < tr.height tp → cv tr tp (w + d) act = 1 → cv tr tp w tau ≤ cv tr tp (w + d) tau
  | 0, _, _ => Nat.le_refl _
  | d + 1, hd, ha => by
    have hd0 : w + d < tr.height tp := by omega
    have ha0 : cv tr tp (w + d) act = 1 := act_prev hL (by omega) ha
    have ih := tau_mono hL hH w d hd0 ha0
    have hle := tau_le hL (w + d) hd0 ha0
    rcases tau_step hL hd0 ha0 (by omega) ha with h | h <;>
      rw [show w + (d + 1) = w + d + 1 by omega, h]
    · exact ih
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem tau_mono' (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {w w' : Nat} (hww : w ≤ w')
    (hw' : w' < tr.height tp) (ha : cv tr tp w' act = 1) : cv tr tp w tau ≤ cv tr tp w' tau := by
  have := tau_mono hL hH w (w' - w) (by omega) (by rw [show w + (w' - w) = w' by omega]; exact ha)
  rwa [show w + (w' - w) = w' by omega] at this

/-- A key block start `f > 0` increments `τ`. -/
theorem tau_blk (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0) (h0 : 0 < f) :
    cv tr tp (f - 1) act = 1 ∧ cv tr tp f tau = cv tr tp (f - 1) tau + 1 := by
  have hw1 : f - 1 + 1 < tr.height tp := by omega
  have e : f - 1 + 1 = f := by omega
  have ha : cv tr tp (f - 1) act = 1 :=
    act_prev hL hw1 (by rw [e]; exact act_of hL hf (Or.inl hk))
  have hw : f - 1 < tr.height tp := by omega
  have hle := tau_le hL (f - 1) hw ha
  refine ⟨ha, ?_⟩
  have K0 := kinds hL hw
  have K1 := kinds hL hf
  have hk1 : cv tr tp (f - 1 + 1) kK = 1 := by rw [e]; exact hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.1 with k0 | k0
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h0 | h0
    · have hE : cv tr tp (f - 1) kE = 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.2.2.2.1 with hl | hl
      · have := (round_next hL hw (Or.inr ⟨hE, hl⟩)).2.1; rw [e] at this; omega
      · have := (blk_next hL hw (Or.inr hl) hw1 hk1).2
        rw [e, Nat.mod_eq_of_lt (by omega)] at this; exact this
    · have := (round_next hL hw (Or.inl h0)).2.1; rw [e] at this; omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.1 with hl | hl
    · have hne : cv tr tp (f - 1) kc ≠ 15 := fun h => by
        have := ((kl_iff hL hw).2 k0).2 h; omega
      have := kc_le hL (f - 1) hw k0
      have h2 := (key_next hL hw k0 hl).2.2.1
      rw [e, hc] at h2
      omega
    · have := (blk_next hL hw (Or.inl hl) hw1 hk1).2
      rw [e, Nat.mod_eq_of_lt (by omega)] at this; exact this

/-- Padding stays padding. -/
theorem pad_after (hL : PLocal tr tp pub) {g : Nat} (hg : cv tr tp g act = 0) :
    ∀ d, g + d < tr.height tp → cv tr tp (g + d) act = 0
  | 0, _ => hg
  | d + 1, hd => by
    have := pad_after hL hg d (by omega)
    rw [show g + (d + 1) = g + d + 1 by omega]
    exact pad_next hL (by omega) this

/-! ## The instance -/

/-- The facts of `proc_rounds` for `m` rounds. -/
structure Inst (tr : Trace Fp) (tp f m : Nat) : Prop where
  hdr : ∀ i, i < m → HI tr tp f i (hdrAt tr tp f i) ∧
    cv tr tp (hdrAt tr tp f i) T + cv tr tp (hdrAt tr tp f i) Lr < T0 + tr.height tp
  fin : BEnd tr tp f (hdrAt tr tp f m)
  first : 0 < m → cv tr tp (hdrAt tr tp f 0) T = T0 ∧ cv tr tp (hdrAt tr tp f 0) kq = 0 ∧
    cv tr tp (hdrAt tr tp f 0) Kq = KSENT ∧ cv tr tp (hdrAt tr tp f 0) zq = 0
  chain : ∀ i, i + 1 < m →
    cv tr tp (hdrAt tr tp f (i + 1)) T =
      cv tr tp (hdrAt tr tp f i) T + cv tr tp (hdrAt tr tp f i) Lr ∧
    cv tr tp (hdrAt tr tp f (i + 1)) kq = cv tr tp (hdrAt tr tp f i) kend ∧
    cv tr tp (hdrAt tr tp f (i + 1)) Kq = cv tr tp (hdrAt tr tp f i) K ∧
    cv tr tp (hdrAt tr tp f (i + 1)) zq = cv tr tp (hdrAt tr tp f i) z

theorem inst_exists (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0) :
    ∃ m, Inst tr tp f m := by
  obtain ⟨m, h1, h2, h3, h4⟩ := proc_rounds hL hH hf hk hc
  exact ⟨m, h1, h2, h3, h4⟩

theorem hdrAt_lt_succ (tr : Trace Fp) (tp f i : Nat) : hdrAt tr tp f i < hdrAt tr tp f (i + 1) := by
  rw [hdrAt_succ]; omega

theorem hdrAt_mono (tr : Trace Fp) (tp f : Nat) {i j : Nat} (h : i < j) :
    hdrAt tr tp f i < hdrAt tr tp f j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h' | h'
    · exact Nat.lt_trans (ih h') (hdrAt_lt_succ tr tp f j)
    · have : i = j := by omega
      subst this; exact hdrAt_lt_succ tr tp f i

/-- Rows between the first header and the end lie in a round. -/
theorem cover (tr : Trace Fp) (tp f : Nat) :
    ∀ m w, f + 16 ≤ w → w < hdrAt tr tp f m →
      ∃ i, i < m ∧ hdrAt tr tp f i ≤ w ∧ w < hdrAt tr tp f (i + 1)
  | 0, w, h1, h2 => by rw [hdrAt_zero] at h2; omega
  | m + 1, w, h1, h2 => by
    rcases Nat.lt_or_ge w (hdrAt tr tp f m) with h | h
    · obtain ⟨i, hi, a, b⟩ := cover tr tp f m w h1 h
      exact ⟨i, by omega, a, b⟩
    · exact ⟨m, by omega, h, h2⟩

/-- The entry rows of the instance, in order. -/
def entRows (tr : Trace Fp) (tp f m : Nat) : List Nat :=
  (List.range m).flatMap fun i =>
    (List.range (cv tr tp (hdrAt tr tp f i) Lr)).map fun j => hdrAt tr tp f i + 1 + j

theorem mem_entRows {tr : Trace Fp} {tp f m w : Nat} :
    w ∈ entRows tr tp f m ↔ ∃ i, i < m ∧ ∃ j, j < cv tr tp (hdrAt tr tp f i) Lr ∧
      w = hdrAt tr tp f i + 1 + j := by
  simp only [entRows, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨i, hi, j, hj, rfl⟩

theorem entRows_sorted (tr : Trace Fp) (tp f m : Nat) :
    (entRows tr tp f m).Pairwise (· < ·) := by
  unfold entRows
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun h => by omega)
  · refine List.pairwise_lt_range.imp ?_
    intro i i' hii x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', hj', rfl⟩ := hy
    have h1 := hdrAt_succ tr tp f i
    have h2 : hdrAt tr tp f (i + 1) ≤ hdrAt tr tp f i' := by
      rcases Nat.lt_or_ge (i + 1) i' with h | h
      · exact Nat.le_of_lt (hdrAt_mono tr tp f h)
      · rw [show i' = i + 1 by omega]; exact Nat.le_refl _
    omega

theorem entRows_nodup (tr : Trace Fp) (tp f m : Nat) : (entRows tr tp f m).Nodup :=
  (entRows_sorted tr tp f m).imp (fun h => Nat.ne_of_lt h)

/-- **The entry rows of the instance** are exactly the entries with its `τ`. -/
theorem ent_iff (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f m : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0)
    (I : Inst tr tp f m) (w : Nat) :
    (w < tr.height tp ∧ cv tr tp w kE = 1 ∧ cv tr tp w tau = cv tr tp f tau) ↔
      w ∈ entRows tr tp f m := by
  constructor
  · rintro ⟨hw, hE, ht⟩
    have Kw := kinds hL hw
    have haw : cv tr tp w act = 1 := act_of hL hw (Or.inr (Or.inr hE))
    -- before the block
    rcases Nat.lt_or_ge w f with hwf | hwf
    · obtain ⟨ha1, ht1⟩ := tau_blk hL hH hf hk hc (by omega)
      have := tau_mono' hL hH (show w ≤ f - 1 by omega) (by omega) ha1
      omega
    -- key rows
    rcases Nat.lt_or_ge w (f + 16) with hw16 | hw16
    · obtain ⟨K, -⟩ := proc_keys hL hH hf hk hc
      have := (K (w - f) (by omega)).2.1
      rw [show f + (w - f) = w by omega] at this
      omega
    -- after the end
    rcases Nat.lt_or_ge w (hdrAt tr tp f m) with hwe | hwe
    · obtain ⟨i, hi, h1, h2⟩ := cover tr tp f m w hw16 hwe
      rw [mem_entRows]
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · have := (I.hdr i hi).1.2.1
        rw [e] at this; omega
      · rw [hdrAt_succ] at h2
        exact ⟨i, hi, w - hdrAt tr tp f i - 1, by omega, by omega⟩
    · exfalso
      obtain ⟨hg, hE'⟩ := I.fin
      rcases hE' with ha | ⟨-, -, htg⟩
      · have := pad_after hL ha (w - hdrAt tr tp f m) (by omega)
        rw [show hdrAt tr tp f m + (w - hdrAt tr tp f m) = w by omega] at this
        omega
      · have := tau_mono' hL hH hwe hw haw
        omega
  · intro hw
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_entRows.1 hw
    obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := I.hdr i hi
    obtain ⟨-, -, RS⟩ := round_shape hL hH hh0 hh
    obtain ⟨⟨hw', hE, -, RC, -⟩, -⟩ := RS j hj
    exact ⟨hw', hE, by rw [RC tau (by simp [roundCols]), ht]⟩

end

end ZkFormal.NearV3.Sched.Proc
