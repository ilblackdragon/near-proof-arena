import StateM5a.St
import StateM5a.KeyDigest

/-!
# StateM5a.StSoundA — the `STB` runs (M5a-7, STATE rows soundness, part 1)

Row facts of the `STB` table (`St.lean`) proved from its constraints over BabyBear, for any table
index `t` whose rows satisfy `Stb.constraints` and whose height is `≤ 2^20` (`Stb.table.maxLog`):

* **`stb_inv`**: on an active row `r`, `m ≤ r` and `j ≤ r` (no value wraps);
* **`stb_run`**: from an active row `r₁` to an active row `r₁ + d`, `m` does not decrease, and if it
  is unchanged then no row in between closed a run: `ts`, `base` are those of `r₁` and
  `j(r₁ + d) = j(r₁) + d`;
* **`stb_same`**: two active rows with the same message number `m`, the second one closing its run
  (`last = 1`), are in order and share `ts` and `base` — so every row of message `m` carries the
  `ts`/`base` of the `DESC(m, ts, base, len)` its closing row sends.

Message ids are not assumed consecutive or distinct from the outside: these lemmas only use the
transition constraints (`m' = m + last`, `j' = (1 − last)(j + 1)`, `ts`/`base` constant while
`last = 0`, active rows a prefix).
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.KeyDecode

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## `STB` constraint membership -/

theorem m_bool_act : bool (Stb.c "act") ∈ Stb.constraints := by unfold Stb.constraints; simp
theorem m_bool_last : bool (Stb.c "last") ∈ Stb.constraints := by unfold Stb.constraints; simp
theorem m_last_act : (1 - Stb.c "act") * Stb.c "last" ∈ Stb.constraints := by
  unfold Stb.constraints; simp
theorem m_first_m : Expr.isFirst * Stb.c "m" ∈ Stb.constraints := by unfold Stb.constraints; simp
theorem m_first_j : Expr.isFirst * Stb.c "j" ∈ Stb.constraints := by unfold Stb.constraints; simp
theorem m_tr_act : Expr.isTransition * Stb.nx "act" * (1 - Stb.c "act") ∈ Stb.constraints := by
  unfold Stb.constraints; simp
theorem m_tr_m : Expr.isTransition * Stb.nx "act" * (Stb.nx "m" - Stb.c "m" - Stb.c "last") ∈
    Stb.constraints := by unfold Stb.constraints; simp
theorem m_tr_j : Expr.isTransition * Stb.nx "act" *
    (Stb.nx "j" - (1 - Stb.c "last") * (Stb.c "j" + 1)) ∈ Stb.constraints := by
  unfold Stb.constraints; simp
theorem m_tr_ts : Expr.isTransition * Stb.nx "act" * (1 - Stb.c "last") * (Stb.nx "ts" - Stb.c "ts") ∈
    Stb.constraints := by unfold Stb.constraints; simp
theorem m_tr_base : Expr.isTransition * Stb.nx "act" * (1 - Stb.c "last") *
    (Stb.nx "base" - Stb.c "base") ∈ Stb.constraints := by unfold Stb.constraints; simp

/-! ## Row facts -/

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- Column `s` of `STB` row `r` (table `t`) as a natural. -/
abbrev sv (tr : Trace Fp) (t r : Nat) (pub : List Fp) (s : String) : Nat := ev tr t r pub (Stb.c s)

theorem stb_nx (s : String) {r : Nat} (hr : r + 1 < tr.height t) :
    ev tr t r pub (Stb.nx s) = sv tr t (r + 1) pub s := FieldWsb.ev_next r _ hr

theorem ev_one_sub0 {x : Expr} {r : Nat} (h : ev tr t r pub x = 0) : ev tr t r pub (1 - x) = 1 := by
  rw [ev_sub, ev_one, h]

theorem ev_one_sub1 {x : Expr} {r : Nat} (h : ev tr t r pub x = 1) : ev tr t r pub (1 - x) = 0 := by
  rw [ev_sub, ev_one, h]

theorem stb_tr_gate {r : Nat} (hr1 : r + 1 < tr.height t) (hna : sv tr t (r + 1) pub "act" = 1) :
    ev tr t r pub (Expr.isTransition * Stb.nx "act") = 1 := by
  rw [ev_hmul, FieldWsb.ev_isTransition, if_neg (by omega), stb_nx "act" hr1, hna]

variable (hc : ∀ r, r < tr.height t → ∀ e ∈ Stb.table.constraints, e.eval tr t r pub = 0)
include hc

theorem stb_h {r : Nat} (hr : r < tr.height t) {e : Expr} (he : e ∈ Stb.constraints) :
    ev tr t r pub e = 0 := hold rfl (hc r hr) he

theorem stb_last_le {r : Nat} (hr : r < tr.height t) : sv tr t r pub "last" ≤ 1 :=
  bool_le (stb_h hc hr m_bool_last)

theorem stb_last_act {r : Nat} (hr : r < tr.height t) (hl : sv tr t r pub "last" = 1) :
    sv tr t r pub "act" = 1 := gate_of_one (stb_h hc hr m_last_act) hl

theorem stb_prev_act {r : Nat} (hr1 : r + 1 < tr.height t) (hna : sv tr t (r + 1) pub "act" = 1) :
    sv tr t r pub "act" = 1 :=
  ev_one_minus (FieldWsb.wsb_gate (stb_tr_gate hr1 hna) (stb_h hc (by omega) m_tr_act))

theorem stb_step_m {r : Nat} (hr1 : r + 1 < tr.height t) (hna : sv tr t (r + 1) pub "act" = 1) :
    sv tr t (r + 1) pub "m" = (sv tr t r pub "m" + sv tr t r pub "last") % P := by
  have h := eq_of_sub (FieldWsb.wsb_gate (stb_tr_gate hr1 hna) (stb_h hc (by omega) m_tr_m))
  have h3 := sub_val h
  rw [stb_nx "m" hr1] at h3
  exact h3

theorem stb_step_j {r : Nat} (hr1 : r + 1 < tr.height t) (hna : sv tr t (r + 1) pub "act" = 1) :
    (sv tr t r pub "last" = 1 → sv tr t (r + 1) pub "j" = 0) ∧
    (sv tr t r pub "last" = 0 → sv tr t (r + 1) pub "j" = (sv tr t r pub "j" + 1) % P) := by
  have h := eq_of_sub (FieldWsb.wsb_gate (stb_tr_gate hr1 hna) (stb_h hc (by omega) m_tr_j))
  rw [stb_nx "j" hr1, ev_hmul] at h
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · rw [ev_one_sub1 hl, Nat.zero_mul] at h
    exact h
  · rw [ev_one_sub0 hl, Nat.one_mul, ev_hadd, ev_one, Nat.mod_mod] at h
    exact h

theorem stb_step_ts {r : Nat} (hr1 : r + 1 < tr.height t) (hna : sv tr t (r + 1) pub "act" = 1)
    (hl : sv tr t r pub "last" = 0) :
    sv tr t (r + 1) pub "ts" = sv tr t r pub "ts" ∧ sv tr t (r + 1) pub "base" = sv tr t r pub "base" := by
  have hg : ev tr t r pub (Expr.isTransition * Stb.nx "act" * (1 - Stb.c "last")) = 1 := by
    rw [ev_hmul, stb_tr_gate hr1 hna, ev_one_sub0 hl]
  have h1 := eq_of_sub (FieldWsb.wsb_gate hg (stb_h hc (by omega) m_tr_ts))
  have h2 := eq_of_sub (FieldWsb.wsb_gate hg (stb_h hc (by omega) m_tr_base))
  rw [stb_nx "ts" hr1] at h1
  rw [stb_nx "base" hr1] at h2
  exact ⟨h1, h2⟩

theorem stb_act_down {r : Nat} : ∀ d, r + d < tr.height t → sv tr t (r + d) pub "act" = 1 →
    sv tr t r pub "act" = 1
  | 0, _, h => h
  | d + 1, hr, h => stb_act_down d (by omega) (stb_prev_act hc (r := r + d) (by omega) h)

/-- **On an active row, `m ≤ r` and `j ≤ r`.** -/
theorem stb_inv (hH : tr.height t ≤ 2 ^ 20) :
    ∀ r, r < tr.height t → sv tr t r pub "act" = 1 → sv tr t r pub "m" ≤ r ∧ sv tr t r pub "j" ≤ r
  | 0, hr, _ => by
    have g : ev tr t 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
    exact ⟨Nat.le_of_eq (FieldWsb.wsb_gate g (stb_h hc hr m_first_m)),
      Nat.le_of_eq (FieldWsb.wsb_gate g (stb_h hc hr m_first_j))⟩
  | r + 1, hr, ha => by
    have ha0 := stb_prev_act hc hr ha
    obtain ⟨ih1, ih2⟩ := stb_inv hH r (by omega) ha0
    have hm := stb_step_m hc hr ha
    have hl := stb_last_le hc (r := r) (by omega)
    obtain ⟨hj1, hj0⟩ := stb_step_j hc hr ha
    refine ⟨by rw [hm]; omega, ?_⟩
    rcases (show sv tr t r pub "last" = 0 ∨ sv tr t r pub "last" = 1 by omega) with h | h
    · rw [hj0 h]; omega
    · rw [hj1 h]; omega

/-- **A run.**  From active row `r₁` to active row `r₁ + d`, `m` does not decrease; if it is
unchanged, `ts`/`base` are unchanged and `j` advanced by `d`. -/
theorem stb_run (hH : tr.height t ≤ 2 ^ 20) (r1 : Nat) :
    ∀ d, r1 + d < tr.height t → sv tr t (r1 + d) pub "act" = 1 →
      sv tr t r1 pub "m" ≤ sv tr t (r1 + d) pub "m" ∧
      (sv tr t (r1 + d) pub "m" = sv tr t r1 pub "m" →
        sv tr t (r1 + d) pub "ts" = sv tr t r1 pub "ts" ∧
        sv tr t (r1 + d) pub "base" = sv tr t r1 pub "base" ∧
        sv tr t (r1 + d) pub "j" = sv tr t r1 pub "j" + d)
  | 0, _, _ => ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl, rfl⟩⟩
  | d + 1, hr, ha => by
    have e : r1 + (d + 1) = r1 + d + 1 := by omega
    rw [e] at hr ha ⊢
    have ha0 := stb_prev_act hc hr ha
    obtain ⟨ih1, ih2⟩ := stb_run hH r1 d (by omega) ha0
    obtain ⟨hmd, hjd⟩ := stb_inv hc hH (r1 + d) (by omega) ha0
    have hm := stb_step_m hc hr ha
    have hl := stb_last_le hc (r := r1 + d) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)] at hm
    refine ⟨by omega, fun heq => ?_⟩
    have hl0 : sv tr t (r1 + d) pub "last" = 0 := by omega
    obtain ⟨i1, i2, i3⟩ := ih2 (by omega)
    obtain ⟨t1, t2⟩ := stb_step_ts hc hr ha hl0
    have hj := (stb_step_j hc hr ha).2 hl0
    refine ⟨by rw [t1, i1], by rw [t2, i2], ?_⟩
    rw [hj, i3, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Rows of one message share the closing row's `ts`/`base`.** -/
theorem stb_same (hH : tr.height t ≤ 2 ^ 20) {r1 r2 : Nat} (h1 : r1 < tr.height t) (h2 : r2 < tr.height t)
    (ha1 : sv tr t r1 pub "act" = 1) (hm : sv tr t r1 pub "m" = sv tr t r2 pub "m")
    (hl : sv tr t r2 pub "last" = 1) :
    r1 ≤ r2 ∧ sv tr t r1 pub "ts" = sv tr t r2 pub "ts" ∧ sv tr t r1 pub "base" = sv tr t r2 pub "base" := by
  have ha2 := stb_last_act hc h2 hl
  by_cases hle : r1 ≤ r2
  · obtain ⟨-, h⟩ := stb_run hc hH r1 (r2 - r1) (by omega) (by rw [Nat.add_sub_cancel' hle]; exact ha2)
    rw [Nat.add_sub_cancel' hle] at h
    obtain ⟨e1, e2, -⟩ := h hm.symm
    exact ⟨hle, e1.symm, e2.symm⟩
  · exfalso
    have hr2 : r2 + 1 < tr.height t := by omega
    have hd : r2 + 1 + (r1 - (r2 + 1)) = r1 := by omega
    have ha3 : sv tr t (r2 + 1) pub "act" = 1 :=
      stb_act_down hc (r1 - (r2 + 1)) (by omega) (by rw [hd]; exact ha1)
    have hm3 := stb_step_m hc hr2 ha3
    obtain ⟨hmb, -⟩ := stb_inv hc hH r2 h2 ha2
    rw [hl, Nat.mod_eq_of_lt (by omega)] at hm3
    obtain ⟨h, -⟩ := stb_run hc hH (r2 + 1) (r1 - (r2 + 1)) (by omega) (by rw [hd]; exact ha1)
    rw [hd] at h
    omega

end

end StateM5a.StSound
