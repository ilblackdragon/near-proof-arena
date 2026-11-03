import StateM5a.FieldWsb
import StateM5a.WsCost

/-!
# StateM5a.WsLen — the working-set entry count `wsLen` (public value 16) from the constraints

M5a-5 adds `wsLen = pub 16` and four `WSB` constraints (the last four of `Wsb.constraints`):

  `isFirst·(1 − real)·wsLen`,  `isTransition·e·(1 − real')·wsLen`,
  `(1 − e)·real·(1 − real')·(i + 1 − wsLen)`,  `e·real·(2^D − wsLen)`,

and a `WSL` constraint `act·(wsLen − 1 − i − Σ 256^k ix_k)` with `ix` bytes (`RNG`).  Proved here
over BabyBear, `W = wsLen` read as a natural `< P`:

* `wsb_last`, **`wsb_height`**: the last `WSB` row has `ph = e = 1`, so the table has exactly
  `2^(D+1)` rows; `wsb_ph0_lt`: a phase-0 row has `i < 2^D`; **`wsb_pos`**: the row
  `ph·2^D + i` (`ph ∈ {0, 1}`, `i < 2^D`) is the row of phase `ph`, index `i`
  (and `FieldWsb.wsb_row_inj`: the only one).
* **`wsb_real_iff`**: on every row, `real = 1 ↔ i < W` (and `real ∈ {0, 1}`), in both phases;
  **`wsb_wsLen_le`**: `W ≤ 2^D`.  Neither needs the prefix constraint
  `isTransition·(1 − e)·real'·(1 − real)`: `real = 1 ⇒ i < W` by induction towards the phase end
  (the last real row fixes `W = i + 1`, or `W = 2^D` at the phase end), `real = 0 ⇒ W ≤ i` by
  induction from the phase start (`W = 0` when a phase starts with padding).
* **`wsb_leaves`** (the consequence): in each phase the leaf rows are, index by index,
  `wsLen` real leaves followed by `2^D − wsLen` padding rows whose digest limbs are all `0`.
* **`wsl_ix`**: an active `WSL` row with `ix` bytes has `i < W` or `i ≥ P − 2^24` (the field
  equation `i ≡ W − 1 − Σ 256^k ix_k` wraps exactly when `Σ ≥ W`); **`wsl_lt_wsLen`**: a touched
  leaf at a tree position (`i < 2^20 ≤ P − 2^24`; `WsDecode.wsl_i_lt` proves `i < 2^D` from the
  `PT` traffic) is a real entry, `i < W` — so a touched leaf is never a padding position.
-/

namespace StateM5a.WsLen

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldRows2
open StateM5a.FieldWsb

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-- The public entry count as a natural. -/
def wsLen (pub : List Fp) : Nat := (pub.getD PUB_WSLEN 0).toNat

theorem ev_wsLen (r : Nat) : ev tr t r pub wsLenE = wsLen pub := rfl

theorem wsLen_lt : wsLen pub < P := Fp.toNat_lt _

theorem ev_isLast (r : Nat) : ev tr t r pub .isLast = if r + 1 = tr.height t then 1 else 0 := by
  unfold ev Expr.eval
  simp only [Expr.evalWith, rowEnv]
  split <;> rfl

theorem ev_one_mul {r : Nat} {a b : Expr} (ha : ev tr t r pub a = 1) (hb : ev tr t r pub b = 1) :
    ev tr t r pub (a * b) = 1 := by
  rw [ev_hmul, ha, hb]

theorem one_sub_eq0 {r : Nat} {x : Expr} (h : ev tr t r pub (1 - x) = 0) : ev tr t r pub x = 1 := by
  rw [ev_sub, ev_one] at h
  have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  omega

/-! ## Constraint membership -/

section
variable {D : Nat}

theorem m_c1 : Expr.isFirst * (1 - Wsb.c "real") * wsLenE ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_c2 : Expr.isTransition * Wsb.c "e" * (1 - Wsb.nx "real") * wsLenE ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_c3 : (1 - Wsb.c "e") * Wsb.c "real" * (1 - Wsb.nx "real") * (Wsb.c "i" + 1 - wsLenE) ∈
    Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_c4 : Wsb.c "e" * Wsb.c "real" * (K (2 ^ D) - wsLenE) ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_real : bool (Wsb.c "real") ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_last_e : Expr.isLast * (1 - Wsb.c "e") ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_last_ph : Expr.isLast * (1 - Wsb.c "ph") ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_dg (j : Nat) (hj : j < 18) : (1 - Wsb.c "real") * Wsb.c "dg" j ∈ Wsb.constraints D := by
  unfold Wsb.constraints
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨j, hj, rfl⟩)

end

/-! ## Layout of the table -/

section
variable {D : Nat} (hc : ∀ r, r < tr.height t → ∀ e ∈ (Wsb.table D).constraints, e.eval tr t r pub = 0)
  (hlog : tr.log t ≤ 20) (hD : D ≤ 30)
include hc

theorem real_bool {r : Nat} (hr : r < tr.height t) :
    ev tr t r pub (Wsb.c "real") = 0 ∨ ev tr t r pub (Wsb.c "real") = 1 :=
  ev_bool (wsb_h hc hr m_real)

/-- `e = 1` fixes the index: `i = 2^D − 1`. -/
theorem e_index (hD : D ≤ 30) {r : Nat} (hr : r < tr.height t) (he : ev tr t r pub (Wsb.c "e") = 1) :
    ev tr t r pub (Wsb.c "i") = 2 ^ D - 1 := by
  have := eq_of_sub (wsb_gate he (wsb_h hc hr (m_e (D := D))))
  have h1 := Nat.one_le_two_pow (n := D)
  have h2 : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
  rw [this, show K (2 ^ D - 1) = Expr.const (2 ^ D - 1) from rfl, ev_const, Nat.mod_eq_of_lt (by omega)]

theorem wsb_last : ev tr t (tr.height t - 1) pub (Wsb.c "e") = 1 ∧
    ev tr t (tr.height t - 1) pub (Wsb.c "ph") = 1 := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have hr : tr.height t - 1 < tr.height t := by omega
  have g : ev tr t (tr.height t - 1) pub .isLast = 1 := by
    rw [ev_isLast]; split <;> omega
  exact ⟨one_sub_eq0 (wsb_gate g (wsb_h hc hr m_last_e)), one_sub_eq0 (wsb_gate g (wsb_h hc hr m_last_ph))⟩

include hlog hD in
/-- **The `WSB` height is `2^(D+1)`.** -/
theorem wsb_height : tr.height t = 2 ^ (D + 1) := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have hr : tr.height t - 1 < tr.height t := by omega
  obtain ⟨he, hp⟩ := wsb_last hc
  have hi := e_index hc hD hr he
  rcases wsb_index hc hlog hD _ hr with ⟨a, _⟩ | ⟨_, b⟩
  · omega
  · have := Nat.one_le_two_pow (n := D)
    rw [Nat.pow_succ]; omega

include hlog hD in
/-- A phase-0 row has `i < 2^D` (its phase must end at `i = 2^D − 1`, the last row being phase 1). -/
theorem wsb_ph0_lt : ∀ n r, r + n + 1 = tr.height t → ev tr t r pub (Wsb.c "ph") = 0 →
    ev tr t r pub (Wsb.c "i") < 2 ^ D
  | 0, r, hr, hp => by
    have := (wsb_last hc).2
    rw [show r = tr.height t - 1 by omega] at hp
    omega
  | n + 1, r, hr, hp => by
    have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
    have hr' : r < tr.height t := by omega
    rcases wsb_bool hc "e" (by simp) hr' with he | he
    · have hiP : ev tr t r pub (Wsb.c "i") + 1 < P := by
        rcases wsb_index hc hlog hD r hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      obtain ⟨s0, -, sp⟩ := wsb_step hc (r := r) (by omega) hiP
      have ih := wsb_ph0_lt n (r + 1) (by omega) (by rw [sp, hp, he])
      rw [s0 he] at ih; omega
    · rw [e_index hc hD hr' he]
      have := Nat.one_le_two_pow (n := D); omega

include hlog hD in
/-- **Row of a position**: for `ph ∈ {0, 1}` and `i < 2^D`, row `ph·2^D + i` has phase `ph`
and index `i`. -/
theorem wsb_pos (ph i : Nat) (hph : ph ≤ 1) (hi : i < 2 ^ D) :
    ph * 2 ^ D + i < tr.height t ∧ ev tr t (ph * 2 ^ D + i) pub (Wsb.c "ph") = ph ∧
      ev tr t (ph * 2 ^ D + i) pub (Wsb.c "i") = i := by
  have hH := wsb_height hc hlog hD
  have hr : ph * 2 ^ D + i < tr.height t := by
    rw [hH, Nat.pow_succ]
    rcases (show ph = 0 ∨ ph = 1 by omega) with rfl | rfl <;> omega
  refine ⟨hr, ?_⟩
  rcases wsb_index hc hlog hD _ hr with ⟨a, b⟩ | ⟨a, b⟩
  · have := wsb_ph0_lt hc hlog hD (tr.height t - (ph * 2 ^ D + i) - 1) _ (by omega) a
    rcases (show ph = 0 ∨ ph = 1 by omega) with rfl | rfl
    · simp only [Nat.zero_mul, Nat.zero_add] at a b ⊢; exact ⟨a, b⟩
    · omega
  · rcases (show ph = 0 ∨ ph = 1 by omega) with rfl | rfl
    · omega
    · simp only [Nat.one_mul] at a b ⊢; exact ⟨a, by omega⟩

/-! ## `real ↔ i < wsLen` -/

/-- The last real row of a phase (not its end): `W = i + 1`. -/
theorem cA {r : Nat} (hr : r + 1 < tr.height t) (he : ev tr t r pub (Wsb.c "e") = 0)
    (h1 : ev tr t r pub (Wsb.c "real") = 1) (h0 : ev tr t (r + 1) pub (Wsb.c "real") = 0)
    (hiP : ev tr t r pub (Wsb.c "i") + 1 < P) :
    wsLen pub = ev tr t r pub (Wsb.c "i") + 1 := by
  have hr' : r < tr.height t := by omega
  have g0 : ev tr t r pub (1 - Wsb.nx "real") = 1 := by
    rw [ev_sub, ev_one, show Wsb.nx "real" = Expr.col (Wsb.T.L.off "real" + 0) true from rfl,
      ev_next r _ hr]
    change (1 + (P - ev tr t (r + 1) pub (Wsb.c "real")) % P) % P = 1
    rw [h0]
  have g : ev tr t r pub ((1 - Wsb.c "e") * Wsb.c "real" * (1 - Wsb.nx "real")) = 1 :=
    ev_one_mul (ev_one_mul (ev_one_sub0 he) h1) g0
  have := eq_of_sub (wsb_gate g (wsb_h hc hr' (m_c3 (D := D))))
  rw [ev_hadd, ev_one, Nat.mod_eq_of_lt hiP, ev_wsLen] at this
  exact this.symm

include hD in
/-- A real row at a phase end: `W = 2^D`. -/
theorem cB {r : Nat} (hr : r < tr.height t) (he : ev tr t r pub (Wsb.c "e") = 1)
    (h1 : ev tr t r pub (Wsb.c "real") = 1) : wsLen pub = 2 ^ D := by
  have := eq_of_sub (wsb_gate (ev_one_mul he h1) (wsb_h hc hr (m_c4 (D := D))))
  have h2 : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
  rw [show K (2 ^ D) = Expr.const (2 ^ D) from rfl, ev_const, Nat.mod_eq_of_lt (by omega),
    ev_wsLen] at this
  exact this.symm

/-- Phase 0 starts with padding: `W = 0`. -/
theorem cC0 (h0 : ev tr t 0 pub (Wsb.c "real") = 0) : wsLen pub = 0 := by
  have hr : 0 < tr.height t := Nat.two_pow_pos _
  have g : ev tr t 0 pub (.isFirst * (1 - Wsb.c "real")) = 1 :=
    ev_one_mul (by rw [ev_isFirst]; rfl) (ev_one_sub0 h0)
  have := wsb_gate g (wsb_h hc hr (m_c1 (D := D)))
  rwa [ev_wsLen] at this

/-- Phase 1 starts with padding: `W = 0`. -/
theorem cC1 {r : Nat} (hr : r + 1 < tr.height t) (he : ev tr t r pub (Wsb.c "e") = 1)
    (h0 : ev tr t (r + 1) pub (Wsb.c "real") = 0) : wsLen pub = 0 := by
  have hr' : r < tr.height t := by omega
  have g0 : ev tr t r pub (1 - Wsb.nx "real") = 1 := by
    rw [ev_sub, ev_one, show Wsb.nx "real" = Expr.col (Wsb.T.L.off "real" + 0) true from rfl,
      ev_next r _ hr]
    change (1 + (P - ev tr t (r + 1) pub (Wsb.c "real")) % P) % P = 1
    rw [h0]
  have gt : ev tr t r pub .isTransition = 1 := by
    rw [ev_isTransition]; split <;> omega
  have g : ev tr t r pub (.isTransition * Wsb.c "e" * (1 - Wsb.nx "real")) = 1 :=
    ev_one_mul (ev_one_mul gt he) g0
  have := wsb_gate g (wsb_h hc hr' (m_c2 (D := D)))
  rwa [ev_wsLen] at this

include hlog hD in
theorem real_lt : ∀ n r, r + n + 1 = tr.height t → ev tr t r pub (Wsb.c "real") = 1 →
    ev tr t r pub (Wsb.c "i") < wsLen pub
  | 0, r, hr, h1 => by
    have hr' : r < tr.height t := by omega
    have he := (wsb_last hc).1
    rw [show tr.height t - 1 = r by omega] at he
    rw [cB hc hD hr' he h1, e_index hc hD hr' he]
    have := Nat.one_le_two_pow (n := D); omega
  | n + 1, r, hr, h1 => by
    have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
    have hr' : r < tr.height t := by omega
    have hiP : ev tr t r pub (Wsb.c "i") + 1 < P := by
      have := Nat.one_le_two_pow (n := D)
      rcases wsb_index hc hlog hD r hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    rcases wsb_bool hc "e" (by simp) hr' with he | he
    · obtain ⟨s0, -, -⟩ := wsb_step hc (r := r) (by omega) hiP
      rcases real_bool hc (r := r + 1) (by omega) with h0 | h0
      · rw [cA hc (by omega) he h1 h0 hiP]; omega
      · have := real_lt n (r + 1) (by omega) h0
        rw [s0 he] at this; omega
    · rw [cB hc hD hr' he h1, e_index hc hD hr' he]
      have := Nat.one_le_two_pow (n := D); omega

include hlog hD in
theorem real_ge : ∀ r, r < tr.height t → ev tr t r pub (Wsb.c "real") = 0 →
    wsLen pub ≤ ev tr t r pub (Wsb.c "i")
  | 0, _, h0 => by rw [cC0 hc h0]; omega
  | r + 1, hr, h0 => by
    have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
    have hr' : r < tr.height t := by omega
    have hiP : ev tr t r pub (Wsb.c "i") + 1 < P := by
      have := Nat.one_le_two_pow (n := D)
      rcases wsb_index hc hlog hD r hr' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    obtain ⟨s0, -, -⟩ := wsb_step hc (r := r) hr hiP
    rcases wsb_bool hc "e" (by simp) hr' with he | he
    · rw [s0 he]
      rcases real_bool hc hr' with h0' | h1
      · have := real_ge r hr' h0'; omega
      · rw [cA hc hr he h1 h0 hiP]; omega
    · rw [cC1 hc hr he h0]; omega

include hlog hD in
/-- **`real ↔ i < wsLen`** on every `WSB` row (both phases). -/
theorem wsb_real_iff {r : Nat} (hr : r < tr.height t) :
    (ev tr t r pub (Wsb.c "real") = 0 ∨ ev tr t r pub (Wsb.c "real") = 1) ∧
      (ev tr t r pub (Wsb.c "real") = 1 ↔ ev tr t r pub (Wsb.c "i") < wsLen pub) := by
  refine ⟨real_bool hc hr, fun h1 => real_lt hc hlog hD (tr.height t - r - 1) r (by omega) h1, fun hl => ?_⟩
  rcases real_bool hc hr with h0 | h1
  · have := real_ge hc hlog hD r hr h0; omega
  · exact h1

include hlog hD in
/-- **`wsLen ≤ 2^D`.** -/
theorem wsb_wsLen_le : wsLen pub ≤ 2 ^ D := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have hr : tr.height t - 1 < tr.height t := by omega
  have he := (wsb_last hc).1
  rcases real_bool hc hr with h | h
  · have h1 := real_ge hc hlog hD _ hr h
    have := Nat.one_le_two_pow (n := D)
    rw [e_index hc hD hr he] at h1; omega
  · exact Nat.le_of_eq (cB hc hD hr he h)

include hlog hD in
/-- **The leaf rows of a phase**: for `ph ∈ {0, 1}` and every index `i < 2^D`, the row of
`(ph, i)` (unique: `FieldWsb.wsb_row_inj`) is real iff `i < wsLen`, and a padding row's digest is
zero: `wsLen` real leaves followed by `2^D − wsLen` zero leaves. -/
theorem wsb_leaves (ph i : Nat) (hph : ph ≤ 1) (hi : i < 2 ^ D) :
    ∃ r, r < tr.height t ∧ ev tr t r pub (Wsb.c "ph") = ph ∧ ev tr t r pub (Wsb.c "i") = i ∧
      (ev tr t r pub (Wsb.c "real") = 1 ↔ i < wsLen pub) ∧
      (wsLen pub ≤ i → ev tr t r pub (Wsb.c "real") = 0 ∧ ∀ j < 18, ev tr t r pub (Wsb.c "dg" j) = 0) := by
  obtain ⟨hr, hp, hix⟩ := wsb_pos hc hlog hD ph i hph hi
  obtain ⟨hb, hiff⟩ := wsb_real_iff hc hlog hD hr
  rw [hix] at hiff
  refine ⟨_, hr, hp, hix, hiff, fun hle => ?_⟩
  have h0 : ev tr t (ph * 2 ^ D + i) pub (Wsb.c "real") = 0 := by
    rcases hb with h | h
    · exact h
    · have := hiff.1 h; omega
  exact ⟨h0, fun j hj => wsb_gate (ev_one_sub0 h0) (wsb_h hc hr (m_dg (D := D) j hj))⟩

end

/-! ## `WSL`: a touched leaf is a real entry -/

theorem wsl_mem_ix : Wsl.c "act" * (wsLenE - 1 - Wsl.c "i" -
    sumE ((List.range IX_BYTES).map fun k => K (256 ^ k) * Wsl.c "ix" k)) ∈ Wsl.constraints := by
  unfold Wsl.constraints; simp

/-- **`WSL` index bytes**: on an active row with `ix` bytes, `i ≡ W − 1 − Σ 256^k ix_k`, so
`i < W`, or the equation wrapped and `i ≥ P − 2^24`. -/
theorem wsl_ix {r : Nat} (hc : ∀ e ∈ Wsl.table.constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub (Wsl.c "act") = 1) (hix : ∀ k < IX_BYTES, ev tr t r pub (Wsl.c "ix" k) < 256) :
    ev tr t r pub (Wsl.c "i") < wsLen pub ∨ P - 2 ^ 24 ≤ ev tr t r pub (Wsl.c "i") := by
  have h := hold rfl hc wsl_mem_ix
  change ev tr t r pub (Expr.mul _ _) = 0 at h
  rw [ev_mul_gate _ hact] at h
  have h' := eq_of_sub h
  rw [ev_sub, ev_sub, ev_sumE, ev_wsLen, ev_one] at h'
  have d0 := hix 0 (by decide); have d1 := hix 1 (by decide); have d2 := hix 2 (by decide)
  have hW := wsLen_lt (pub := pub)
  have hi := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Wsl.c "i")
  simp only [IX_BYTES, List.range, List.range.loop, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ev_hmul, K, ev_const, Nat.reducePow, Nat.reduceMod, Nat.add_zero] at h'
  generalize ev tr t r pub (Wsl.c "ix" 0) = y0 at d0 h'
  generalize ev tr t r pub (Wsl.c "ix" 1) = y1 at d1 h'
  generalize ev tr t r pub (Wsl.c "ix" 2) = y2 at d2 h'
  generalize ev tr t r pub (Wsl.c "i") = a at hi h' ⊢
  generalize wsLen pub = W at hW h' ⊢
  simp only [Nat.one_mul] at h'
  rw [Nat.mod_eq_of_lt (show y0 < P by omega), Nat.mod_eq_of_lt (show 256 * y1 < P by omega),
    Nat.mod_eq_of_lt (show 65536 * y2 < P by omega),
    Nat.mod_eq_of_lt (show y0 + (256 * y1 + 65536 * y2) < P by omega)] at h'
  omega

/-- **A touched leaf at a tree position is a real entry**: `i < 2^20` (a tree position, `D ≤ 20`)
excludes the wrapped case, so `i < wsLen`. -/
theorem wsl_lt_wsLen {r : Nat} (hc : ∀ e ∈ Wsl.table.constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub (Wsl.c "act") = 1) (hix : ∀ k < IX_BYTES, ev tr t r pub (Wsl.c "ix" k) < 256)
    (hpos : ev tr t r pub (Wsl.c "i") < 2 ^ 20) : ev tr t r pub (Wsl.c "i") < wsLen pub := by
  rcases wsl_ix hc hact hix with h | h
  · exact h
  · omega

end StateM5a.WsLen
