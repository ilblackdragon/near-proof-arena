import StateM5a.FieldWsb
import StateM5a.Tmpl

/-!
# StateM5a.FieldWsx — B-T1: the `WSX` row layout from its constraints (field level)

`WSX` (`Tmpl.Wsx`, both variants have the same constraints) must hold the extension rows
`lvl = D, …, 23` and nothing else.  From the constraints alone (over BabyBear, heights `≤ 2^20`,
`D ≤ 23`):

* **`wsx_layout`**: row `r` is active iff `r ≤ 23 − D` (so the table has at least `24 − D` rows),
  an active row has `lvl = D + r`, and `top` is set exactly on row `23 − D`;
* **`wsx_link`**: consecutive active rows chain `z' = zo`, `a' = ao`, `b' = bo` (limb by limb);
* **`wsx_first_z`**: the first row's `z` is the constant `Z_D` (`Tmpl.zeroLimbs D`);
* **`wsx_top_pub`**: on the top row `ao` / `bo` are the public roots A / B.

With the chip contract (`Sha512If.comp_node` on each row's three compressions) these are the
premises of `Merkle.wsxChain_out` (`zo = H z z`, `ao = H a z`): the public root is `extUp` of the
first row's `a` — the depth-24 `wsRoot` (`TmplView.wsRoot_ext`).  The bus-level step (the rows'
compressions are in the chip's list, `IF384` balance) is open, as for the other tables' rows.
-/

namespace StateM5a.FieldWsx

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldRows2
open StateM5a.FieldWsb (ev_isFirst ev_isTransition ev_next)

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

local notation "P" => 2013265921

theorem ev_isLast (r : Nat) : ev tr t r pub .isLast = if r + 1 = tr.height t then 1 else 0 := by
  unfold ev Expr.eval
  simp only [Expr.evalWith, rowEnv]
  split <;> rfl

theorem wsx_nx (s : String) (j r : Nat) (hr : r + 1 < tr.height t) :
    ev tr t r pub (Wsx.nx s j) = ev tr t (r + 1) pub (Wsx.c s j) := ev_next r _ hr

/-! ## Membership of the constraints used -/

section
variable {D : Nat}
theorem m_bool_act : bool (Wsx.c "act") ∈ Wsx.constraints D := by unfold Wsx.constraints; simp
theorem m_bool_top : bool (Wsx.c "top") ∈ Wsx.constraints D := by unfold Wsx.constraints; simp
theorem m_first_act : Expr.isFirst * (1 - Wsx.c "act") ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_first_lvl : Expr.isFirst * (Wsx.c "lvl" - K D) ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_prefix : Expr.isTransition * Wsx.nx "act" * (1 - Wsx.c "act") ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_top_tr : Expr.isTransition * (Wsx.c "top" - Wsx.c "act" * (1 - Wsx.nx "act")) ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_top_last : Expr.isLast * (Wsx.c "top" - Wsx.c "act") ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_lvl : Expr.isTransition * Wsx.nx "act" * (Wsx.nx "lvl" - Wsx.c "lvl" - 1) ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp
theorem m_top_lvl : Wsx.c "top" * (Wsx.c "lvl" - K (WS_DEPTH - 1)) ∈ Wsx.constraints D := by
  unfold Wsx.constraints; simp

theorem m_limb {j : Nat} (hj : j < 18) (e : Expr)
    (he : e ∈ [.isFirst * (Wsx.c "z" j - K ((zeroLimbs D).getD j 0)),
     .isTransition * Wsx.nx "act" * (Wsx.nx "z" j - Wsx.c "zo" j),
     .isTransition * Wsx.nx "act" * (Wsx.nx "a" j - Wsx.c "ao" j),
     .isTransition * Wsx.nx "act" * (Wsx.nx "b" j - Wsx.c "bo" j),
     Wsx.c "top" * (Wsx.c "ao" j - .pub (PUB_WSA + j)),
     Wsx.c "top" * (Wsx.c "bo" j - .pub (PUB_WSB + j))]) : e ∈ Wsx.constraints D := by
  unfold Wsx.constraints
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, he⟩)
end

/-! ## Row facts -/

section
variable {D : Nat} {T : Table} (hT : T.constraints = Wsx.constraints D)
  (hc : ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0)
include hT hc

theorem wsx_h {r : Nat} (hr : r < tr.height t) {e : Expr} (he : e ∈ Wsx.constraints D) :
    ev tr t r pub e = 0 := hold hT (hc r hr) he

omit hT hc in
theorem gate {g x : Expr} {r : Nat} (hg : ev tr t r pub g = 1) (h : ev tr t r pub (g * x) = 0) :
    ev tr t r pub x = 0 := by
  have := ev_mul_gate (tr := tr) (t := t) (r := r) (pub := pub) x hg
  change ev tr t r pub (Expr.mul g x) = 0 at h
  omega

omit hT hc in
theorem tr1 {r : Nat} (hr : r + 1 < tr.height t) : ev tr t r pub .isTransition = 1 := by
  rw [ev_isTransition]; split
  · omega
  · rfl

theorem act_bool {r : Nat} (hr : r < tr.height t) :
    ev tr t r pub (Wsx.c "act") = 0 ∨ ev tr t r pub (Wsx.c "act") = 1 :=
  ev_bool (wsx_h hT hc hr m_bool_act)

theorem top_bool {r : Nat} (hr : r < tr.height t) :
    ev tr t r pub (Wsx.c "top") = 0 ∨ ev tr t r pub (Wsx.c "top") = 1 :=
  ev_bool (wsx_h hT hc hr m_bool_top)

theorem wsx_first (hD : D < P) : ev tr t 0 pub (Wsx.c "act") = 1 ∧ ev tr t 0 pub (Wsx.c "lvl") = D := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have g : ev tr t 0 pub .isFirst = 1 := by rw [ev_isFirst]; rfl
  have a := gate g (wsx_h hT hc h0 m_first_act)
  have l := eq_of_sub (gate g (wsx_h hT hc h0 (m_first_lvl (D := D))))
  rw [ev_sub, ev_one] at a
  have := ev_lt (tr := tr) (t := t) (r := 0) (pub := pub) (Wsx.c "act")
  refine ⟨by omega, ?_⟩
  rw [l, show K D = Expr.const D from rfl, ev_const, Nat.mod_eq_of_lt hD]

/-- An active row's predecessor is active. -/
theorem wsx_prefix {r : Nat} (hr : r + 1 < tr.height t) (h1 : ev tr t (r + 1) pub (Wsx.c "act") = 1) :
    ev tr t r pub (Wsx.c "act") = 1 := by
  have hr' : r < tr.height t := by omega
  have e := wsx_h hT hc hr' m_prefix
  rw [show Expr.isTransition * Wsx.nx "act" * (1 - Wsx.c "act") =
      Expr.mul (Expr.mul .isTransition (Wsx.nx "act")) (1 - Wsx.c "act") from rfl] at e
  have g : ev tr t r pub (Expr.mul .isTransition (Wsx.nx "act")) = 1 := by
    rw [ev_mul, tr1 hr, wsx_nx _ _ _ hr, h1]
  have := gate g e
  rw [ev_sub, ev_one] at this
  rcases act_bool hT hc hr' with h | h
  · rw [h] at this; exact absurd this (by decide)
  · exact h

theorem wsx_lvl_step {r : Nat} (hr : r + 1 < tr.height t) (h1 : ev tr t (r + 1) pub (Wsx.c "act") = 1) :
    ev tr t (r + 1) pub (Wsx.c "lvl") = (ev tr t r pub (Wsx.c "lvl") + 1) % P := by
  have hr' : r < tr.height t := by omega
  have e := wsx_h hT hc hr' m_lvl
  rw [show Expr.isTransition * Wsx.nx "act" * (Wsx.nx "lvl" - Wsx.c "lvl" - 1) =
      Expr.mul (Expr.mul .isTransition (Wsx.nx "act")) (Wsx.nx "lvl" - Wsx.c "lvl" - 1) from rfl] at e
  have g : ev tr t r pub (Expr.mul .isTransition (Wsx.nx "act")) = 1 := by
    rw [ev_mul, tr1 hr, wsx_nx _ _ _ hr, h1]
  have := eq_of_sub (gate g e)
  rw [ev_sub, wsx_nx _ _ _ hr, ev_one] at this
  have l1 := ev_lt (tr := tr) (t := t) (r := r + 1) (pub := pub) (Wsx.c "lvl")
  have l0 := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Wsx.c "lvl")
  omega

theorem wsx_top_tr {r : Nat} (hr : r + 1 < tr.height t) (ha : ev tr t r pub (Wsx.c "act") = 1) :
    ev tr t r pub (Wsx.c "top") = 1 - ev tr t (r + 1) pub (Wsx.c "act") := by
  have hr' : r < tr.height t := by omega
  have := eq_of_sub (gate (tr1 hr) (wsx_h hT hc hr' m_top_tr))
  rw [ev_hmul, ha, Nat.one_mul, ev_sub, ev_one, wsx_nx _ _ _ hr] at this
  rcases act_bool hT hc hr with h | h <;> rw [h] at this ⊢ <;> simpa using this

theorem wsx_top_last {r : Nat} (hr : r + 1 = tr.height t) :
    ev tr t r pub (Wsx.c "top") = ev tr t r pub (Wsx.c "act") := by
  have g : ev tr t r pub .isLast = 1 := by rw [ev_isLast]; simp [hr]
  exact eq_of_sub (gate g (wsx_h hT hc (by omega) m_top_last))

theorem wsx_top_lvl {r : Nat} (hr : r < tr.height t) (h1 : ev tr t r pub (Wsx.c "top") = 1) :
    ev tr t r pub (Wsx.c "lvl") = 23 := by
  have := eq_of_sub (gate h1 (wsx_h hT hc hr (m_top_lvl (D := D))))
  rw [this, show K (WS_DEPTH - 1) = Expr.const 23 from rfl, ev_const]

/-- **The `WSX` layout.** -/
theorem wsx_layout (hD : D ≤ 23) (hlog : tr.log t ≤ 20) :
    23 - D < tr.height t ∧
    ∀ r, r < tr.height t →
      (ev tr t r pub (Wsx.c "act") = 1 ↔ r ≤ 23 - D) ∧
      (r ≤ 23 - D → ev tr t r pub (Wsx.c "lvl") = D + r ∧
        (ev tr t r pub (Wsx.c "top") = 1 ↔ r = 23 - D)) := by
  have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  obtain ⟨a0, l0⟩ := wsx_first hT hc (D := D) (by omega)
  -- active rows have `lvl = D + r`
  have hlvl : ∀ r, r < tr.height t → ev tr t r pub (Wsx.c "act") = 1 → ev tr t r pub (Wsx.c "lvl") = D + r := by
    intro r
    induction r with
    | zero => intro _ _; simpa using l0
    | succ r ih =>
      intro hr ha
      rw [wsx_lvl_step hT hc hr ha, ih (by omega) (wsx_prefix hT hc hr ha)]
      apply Nat.mod_eq_of_lt; omega
  -- an active row with `top` is row `23 − D`
  have htop : ∀ r, r < tr.height t → ev tr t r pub (Wsx.c "act") = 1 → ev tr t r pub (Wsx.c "top") = 1 →
      r = 23 - D := by
    intro r hr ha ht
    have := wsx_top_lvl hT hc hr ht
    rw [hlvl r hr ha] at this; omega
  -- rows up to `23 − D` (within the height) are active
  have hup : ∀ r, r ≤ 23 - D → r < tr.height t → ev tr t r pub (Wsx.c "act") = 1 := by
    intro r
    induction r with
    | zero => intro _ _; exact a0
    | succ r ih =>
      intro hr hh
      have ha := ih (by omega) (by omega)
      have ht := wsx_top_tr hT hc hh ha
      rcases act_bool hT hc hh with h | h
      · exfalso
        rw [h] at ht
        exact absurd (htop r (by omega) ha ht) (by omega)
      · exact h
  have hlen : 23 - D < tr.height t := by
    refine Nat.lt_of_not_le fun hc' => ?_
    have h0 : 0 < tr.height t := Nat.two_pow_pos _
    have hl := hup (tr.height t - 1) (by omega) (by omega)
    have := htop _ (by omega) hl (by rw [wsx_top_last hT hc (by omega)]; exact hl)
    omega
  -- no active row past `23 − D`: such a row would make every later row active, and the last row
  -- (top) would sit at level 23
  have hdown : ∀ r, r < tr.height t → 23 - D < r → ev tr t r pub (Wsx.c "act") = 0 := by
    intro r hr hgt
    rcases act_bool hT hc hr with h | h
    · exact h
    · exfalso
      have fwd : ∀ k, r + k < tr.height t → ev tr t (r + k) pub (Wsx.c "act") = 1 := by
        intro k
        induction k with
        | zero => intro _; simpa using h
        | succ k ih =>
          intro hk
          have ha := ih (by omega)
          have ht := wsx_top_tr hT hc (show r + k + 1 < tr.height t by omega) ha
          rcases act_bool hT hc (show r + k + 1 < tr.height t by omega) with h' | h'
          · rw [h'] at ht
            have := htop (r + k) (by omega) ha ht
            omega
          · simpa [Nat.add_assoc] using h'
      have hl := fwd (tr.height t - 1 - r) (by omega)
      rw [show r + (tr.height t - 1 - r) = tr.height t - 1 by omega] at hl
      have := htop _ (by omega) hl (by rw [wsx_top_last hT hc (by omega)]; exact hl)
      omega
  refine ⟨hlen, fun r hr => ⟨⟨fun ha => ?_, fun hle => hup r hle hr⟩, fun hle => ?_⟩⟩
  · refine Nat.le_of_not_lt fun hn => ?_
    rw [hdown r hr hn] at ha; exact absurd ha (by decide)
  · have ha := hup r hle hr
    refine ⟨hlvl r hr ha, ⟨fun ht => htop r hr ha ht, fun he => ?_⟩⟩
    subst he
    by_cases hn : 23 - D + 1 < tr.height t
    · rw [wsx_top_tr hT hc hn ha, hdown _ hn (by omega)]
    · rw [wsx_top_last hT hc (by omega), ha]

theorem wsx_link {r j : Nat} (hj : j < 18) (hr : r + 1 < tr.height t)
    (h1 : ev tr t (r + 1) pub (Wsx.c "act") = 1) :
    ev tr t (r + 1) pub (Wsx.c "z" j) = ev tr t r pub (Wsx.c "zo" j) ∧
    ev tr t (r + 1) pub (Wsx.c "a" j) = ev tr t r pub (Wsx.c "ao" j) ∧
    ev tr t (r + 1) pub (Wsx.c "b" j) = ev tr t r pub (Wsx.c "bo" j) := by
  have hr' : r < tr.height t := by omega
  have g : ev tr t r pub (Expr.mul .isTransition (Wsx.nx "act")) = 1 := by
    rw [ev_mul, tr1 hr, wsx_nx _ _ _ hr, h1]
  have k (s o : String) (he : Expr.isTransition * Wsx.nx "act" * (Wsx.nx s j - Wsx.c o j) ∈ Wsx.constraints D) :
      ev tr t (r + 1) pub (Wsx.c s j) = ev tr t r pub (Wsx.c o j) := by
    have := eq_of_sub (gate g (wsx_h hT hc hr' he))
    rwa [wsx_nx _ _ _ hr] at this
  exact ⟨k "z" "zo" (m_limb hj _ (by simp)), k "a" "ao" (m_limb hj _ (by simp)),
    k "b" "bo" (m_limb hj _ (by simp))⟩

theorem wsx_first_z {j : Nat} (hj : j < 18) :
    ev tr t 0 pub (Wsx.c "z" j) = (zeroLimbs D).getD j 0 % P := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  have g : ev tr t 0 pub .isFirst = 1 := by rw [ev_isFirst]; rfl
  have e1 : Expr.isFirst * (Wsx.c "z" j - K ((zeroLimbs D).getD j 0)) ∈ Wsx.constraints D :=
    m_limb hj _ (by simp)
  have := eq_of_sub (gate g (wsx_h hT hc h0 e1))
  rw [this]; exact ev_const _

theorem wsx_top_pub {r j : Nat} (hj : j < 18) (hr : r < tr.height t)
    (h1 : ev tr t r pub (Wsx.c "top") = 1) :
    ev tr t r pub (Wsx.c "ao" j) = ev tr t r pub (.pub (PUB_WSA + j)) ∧
    ev tr t r pub (Wsx.c "bo" j) = ev tr t r pub (.pub (PUB_WSB + j)) :=
  ⟨eq_of_sub (gate h1 (wsx_h hT hc hr (m_limb (D := D) hj (Wsx.c "top" * (Wsx.c "ao" j - .pub (PUB_WSA + j)))
      (by simp)))),
   eq_of_sub (gate h1 (wsx_h hT hc hr (m_limb (D := D) hj (Wsx.c "top" * (Wsx.c "bo" j - .pub (PUB_WSB + j)))
      (by simp))))⟩

end

end StateM5a.FieldWsx
