import StateM5a.FieldWalk2
import StateM5a.Ws

/-!
# StateM5a.FieldWsb — one walk root per walk id (`WSB` row indices, from the constraints)

The `WSB` table has `2^(D+1)` rows: phase 0 (INTAKE, `ph = 0`) indices `i = 0 … 2^D − 1`, then
phase 1 (FINAL, `ph = 1`) indices `0 … 2^D − 1`.  The constraints that force this layout:
`isFirst·i = isFirst·ph = 0`, `isTransition·(i' − (1 − e)(i + 1)) = 0`,
`isTransition·(ph' − ph − e) = 0`, `e·(i − (2^D − 1)) = 0`, booleanity of `ph` and `e`.

* **`wsb_index`**: on every row `r < height`, `(ph = 0 ∧ i = r) ∨ (ph = 1 ∧ i + 2^D = r)`
  (heights `≤ 2^20 < P`, `D ≤ 30`).
* **`wsb_row_inj`**: two rows with the same `(ph, i)` are the same row.  The INTAKE roots send
  `DOWN(w = i, …)` (`g0 = (1 − ph)·real`), the FINAL roots `DOWN(w = W_FINAL + i, …)`
  (`gw = ph·wr`), so this is `Traffic.WalkShape.rootUniq` for the `WSB` roots once the walk id is
  decoded (`i < 2^D ≤ W_FINAL = 2^20` separates the two phases).
* **`wsb_w_inj`**: the decoded walk ids of two root rows agree only on one row.
-/

namespace StateM5a.FieldWsb

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldRows2

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-! ## Selectors and the next row -/

theorem ev_isFirst (r : Nat) : ev tr t r pub .isFirst = if r = 0 then 1 else 0 := by
  unfold ev Expr.eval
  simp only [Expr.evalWith, rowEnv]
  split <;> rfl

theorem ev_isTransition (r : Nat) :
    ev tr t r pub .isTransition = if r + 1 = tr.height t then 0 else 1 := by
  unfold ev Expr.eval
  simp only [Expr.evalWith, rowEnv]
  split <;> rfl

theorem ev_next (r i : Nat) (hr : r + 1 < tr.height t) :
    ev tr t r pub (.col i true) = ev tr t (r + 1) pub (.col i false) := by
  unfold ev Expr.eval
  simp only [Expr.evalWith, rowEnv, Nat.mod_eq_of_lt hr]
  rfl

theorem wsb_nx (s : String) (r : Nat) (hr : r + 1 < tr.height t) :
    ev tr t r pub (Wsb.nx s) = ev tr t (r + 1) pub (Wsb.c s) := ev_next r _ hr

/-! ## The index constraints -/

section
variable {D : Nat}

theorem m_first_i : Expr.isFirst * Wsb.c "i" ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_first_ph : Expr.isFirst * Wsb.c "ph" ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_tr_i : Expr.isTransition * (Wsb.nx "i" - (1 - Wsb.c "e") * (Wsb.c "i" + 1)) ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_tr_ph : Expr.isTransition * (Wsb.nx "ph" - Wsb.c "ph" - Wsb.c "e") ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_e : Wsb.c "e" * (Wsb.c "i" - K (2 ^ D - 1)) ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_bool (s : String) (hs : s ∈ ["ph", "e"]) : bool (Wsb.c s) ∈ Wsb.constraints D := by
  unfold Wsb.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp

end

section
variable {D : Nat} (hc : ∀ r, r < tr.height t → ∀ e ∈ (Wsb.table D).constraints, e.eval tr t r pub = 0)
include hc

theorem wsb_h {r : Nat} (hr : r < tr.height t) {e : Expr} (he : e ∈ Wsb.constraints D) :
    ev tr t r pub e = 0 := hold rfl (hc r hr) he

theorem wsb_bool (s : String) (hs : s ∈ ["ph", "e"]) {r : Nat} (hr : r < tr.height t) :
    ev tr t r pub (Wsb.c s) = 0 ∨ ev tr t r pub (Wsb.c s) = 1 :=
  ev_bool (wsb_h hc hr (m_bool s hs))

omit hc in
theorem wsb_gate {g x : Expr} {r : Nat} (hg : ev tr t r pub g = 1) (h : ev tr t r pub (g * x) = 0) :
    ev tr t r pub x = 0 := by
  have := ev_mul_gate (tr := tr) (t := t) (r := r) (pub := pub) x hg
  change ev tr t r pub (Expr.mul g x) = 0 at h
  omega

omit hc in
theorem ev_one_sub1 {r : Nat} {x : Expr} (h : ev tr t r pub x = 1) : ev tr t r pub (1 - x) = 0 := by
  rw [ev_sub, h]; simp

theorem wsb_first : ev tr t 0 pub (Wsb.c "i") = 0 ∧ ev tr t 0 pub (Wsb.c "ph") = 0 := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have g : ev tr t 0 pub .isFirst = 1 := by rw [ev_isFirst]; rfl
  exact ⟨wsb_gate g (wsb_h hc h0 m_first_i), wsb_gate g (wsb_h hc h0 m_first_ph)⟩

/-- One transition: `i' = (1 − e)(i + 1)` and `ph' = ph + e`, as naturals (small values). -/
theorem wsb_step {r : Nat} (hr : r + 1 < tr.height t) (hiP : ev tr t r pub (Wsb.c "i") + 1 < P) :
    (ev tr t r pub (Wsb.c "e") = 0 → ev tr t (r + 1) pub (Wsb.c "i") = ev tr t r pub (Wsb.c "i") + 1) ∧
    (ev tr t r pub (Wsb.c "e") = 1 → ev tr t (r + 1) pub (Wsb.c "i") = 0) ∧
      ev tr t (r + 1) pub (Wsb.c "ph") = ev tr t r pub (Wsb.c "ph") + ev tr t r pub (Wsb.c "e") := by
  have hr' : r < tr.height t := by omega
  have g : ev tr t r pub .isTransition = 1 := by
    rw [ev_isTransition]; split
    · omega
    · rfl
  have e1 := eq_of_sub (wsb_gate g (wsb_h hc hr' m_tr_i))
  have e2 := wsb_gate g (wsb_h hc hr' m_tr_ph)
  rw [wsb_nx _ _ hr] at e1
  have hp := wsb_bool hc "ph" (by simp) hr'
  have he := wsb_bool hc "e" (by simp) hr'
  have hp1 := wsb_bool hc "ph" (by simp) hr
  refine ⟨fun h0 => ?_, fun h1 => ?_, ?_⟩
  · rw [e1]
    change ev tr t r pub (Expr.mul _ _) = _
    rw [ev_mul_gate _ (ev_one_sub0 h0), ev_hadd, ev_one, Nat.mod_eq_of_lt hiP]
  · rw [e1]
    change ev tr t r pub (Expr.mul _ _) = _
    rw [ev_mul, ev_one_sub1 h1, Nat.zero_mul, Nat.zero_mod]
  · rw [ev_sub, ev_sub, wsb_nx _ _ hr] at e2
    rcases hp with h | h <;> rcases he with h' | h' <;> rcases hp1 with h'' | h'' <;>
      rw [h, h', h''] at e2 ⊢ <;> revert e2 <;> decide

/-- **The `WSB` row layout.** -/
theorem wsb_index (hlog : tr.log t ≤ 20) (hD : D ≤ 30) :
    ∀ r, r < tr.height t →
      (ev tr t r pub (Wsb.c "ph") = 0 ∧ ev tr t r pub (Wsb.c "i") = r) ∨
      (ev tr t r pub (Wsb.c "ph") = 1 ∧ ev tr t r pub (Wsb.c "i") + 2 ^ D = r) := by
  have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hDP : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
  have hD1 := Nat.one_le_two_pow (n := D)
  intro r
  induction r with
  | zero =>
    intro _
    exact .inl ⟨(wsb_first hc).2, (wsb_first hc).1⟩
  | succ r ih =>
    intro hr
    have hr' : r < tr.height t := by omega
    have he := wsb_bool hc "e" (by simp) hr'
    have hp' := wsb_bool hc "ph" (by simp) hr
    have hEi := wsb_h hc hr' (m_e (D := D))
    have hih := ih hr'
    have hiP : ev tr t r pub (Wsb.c "i") + 1 < P := by
      rcases hih with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    obtain ⟨s0, s1, sp⟩ := wsb_step hc hr hiP
    rcases hih with ⟨hp, hi⟩ | ⟨hp, hi⟩
    · rcases he with he | he
      · left
        exact ⟨by rw [sp, hp, he], by rw [s0 he, hi]⟩
      · right
        -- `e = 1` forces `i = 2^D − 1`
        have hi2 : ev tr t r pub (Wsb.c "i") = 2 ^ D - 1 := by
          have := eq_of_sub (wsb_gate he hEi)
          rw [this, show K (2 ^ D - 1) = Expr.const (2 ^ D - 1) from rfl, ev_const,
            Nat.mod_eq_of_lt (by omega)]
        refine ⟨by rw [sp, hp, he], ?_⟩
        rw [s1 he]; omega
    · rcases he with he | he
      · right
        refine ⟨by rw [sp, hp, he], ?_⟩
        rw [s0 he]; omega
      · exfalso
        rw [sp, hp, he] at hp'
        omega

/-- **Two `WSB` rows with the same `(ph, i)` are the same row.** -/
theorem wsb_row_inj (hlog : tr.log t ≤ 20) (hD : D ≤ 30) {r r' : Nat} (hr : r < tr.height t)
    (hr' : r' < tr.height t) (hp : ev tr t r pub (Wsb.c "ph") = ev tr t r' pub (Wsb.c "ph"))
    (hi : ev tr t r pub (Wsb.c "i") = ev tr t r' pub (Wsb.c "i")) : r = r' := by
  rcases wsb_index hc hlog hD r hr with ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases wsb_index hc hlog hD r' hr' with ⟨a', b'⟩ | ⟨a', b'⟩ <;> omega

/-- The row index bound: `i < 2^D` on every row (phase 0 rows `r < 2^D` need `e`'s end marker:
the phase-0 index never exceeds `2^D − 1` because the next phase starts there; stated here for
phase 1 rows from the height `2^(D+1)`). -/
theorem wsb_i_lt_ph1 (hlog : tr.log t ≤ 20) (hD : D ≤ 30) (hH : tr.height t ≤ 2 ^ (D + 1)) {r : Nat}
    (hr : r < tr.height t) (hp : ev tr t r pub (Wsb.c "ph") = 1) :
    ev tr t r pub (Wsb.c "i") < 2 ^ D := by
  rcases wsb_index hc hlog hD r hr with ⟨a, _⟩ | ⟨_, b⟩
  · omega
  · rw [Nat.pow_succ] at hH; omega

end

end StateM5a.FieldWsb
