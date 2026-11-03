import StateM5a.FieldRows2

/-!
# StateM5a.SnContHead — the head of a continued key (`SN` row with `cont = 1`)

From the `SN` constraints alone, on a row with `act = 1`, `cont = 1`:

* `a_j = 1` for `j ≤ 61`, `a_62 = odd`, `a_63 = 0` (the head holds stream nibbles `2..63`);
* `ha_m = [m < 32]` (`m < 33`): the head carries `hp` bytes `0..31`;
* `hplen = 32 + rl/2` when `rl` is even and small (`rl` = the nibbles of the `SNC` chunks);
* the node is hashed on both sides: `gold ⇒ gsha`, `gnew ⇒ nref = 0` (so `gfin = gnew`).
-/

namespace StateM5a.SnContHead

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldVer
open StateM5a.FieldRows2

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem ev_one_minus' {x : Expr} (h : ev tr t r pub (1 - x) = 0) : ev tr t r pub x = 1 := by
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rw [ev_sub, ev_one] at h
  omega

theorem sub_val' {a b : Expr} {v : Nat} (h : ev tr t r pub (a - b) = v) :
    ev tr t r pub a = (ev tr t r pub b + v) % P := by
  rw [ev_sub] at h
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  omega

/-- `2·H ≡ 64 + L (mod Q)`, `Q` odd, `L` even and small: `H = 32 + L/2`.  (Variable `Q`, so
that no tactic evaluates `% 2013265921`.) -/
theorem half_rl (Q H L : Nat) (hQ : Q % 2 = 1) (hQ2 : 2 ^ 29 < Q) (hH : H < Q) (hev : L % 2 = 0)
    (hlt : L < 2 ^ 28) (h2 : 2 * H % Q = (64 + L) % Q) : H = 32 + L / 2 := by
  rw [Nat.mod_eq_of_lt (show 64 + L < Q by omega)] at h2
  rcases Nat.lt_or_ge (2 * H) Q with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h2
    omega
  · rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (show 2 * H - Q < Q by omega)] at h2
    omega

section
variable (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
include hc

theorem ch_gate {e : Expr} (hcont : ev tr t r pub (Sn.c "cont") = 1)
    (he : Sn.c "cont" * e ∈ Sn.constraints) : ev tr t r pub e = 0 := by
  have h := sn_hold hc he
  change ev tr t r pub (Expr.mul _ _) = 0 at h
  rwa [ev_mul_gate _ hcont] at h

theorem ch_a61 (hcont : ev tr t r pub (Sn.c "cont") = 1) : ev tr t r pub (Sn.c "a" 61) = 1 := by
  have h := ch_gate hc hcont (e := 1 - Sn.a 61) (by unfold Sn.constraints; simp)
  rw [sn_a_lt 61 (by decide)] at h
  exact ev_one_minus' h

theorem ch_a63 (hcont : ev tr t r pub (Sn.c "cont") = 1) : ev tr t r pub (Sn.c "a" 63) = 0 := by
  have h := ch_gate hc hcont (e := Sn.a 63) (by unfold Sn.constraints; simp)
  rwa [sn_a_lt 63 (by decide)] at h

theorem ch_a62 (hcont : ev tr t r pub (Sn.c "cont") = 1) :
    ev tr t r pub (Sn.c "a" 62) = ev tr t r pub (Sn.c "odd") := by
  have h := ch_gate hc hcont (e := Sn.a 62 - Sn.c "odd") (by unfold Sn.constraints; simp)
  rw [sn_a_lt 62 (by decide)] at h
  exact eq_of_sub h

theorem ch_a_low (hcont : ev tr t r pub (Sn.c "cont") = 1) :
    ∀ d j, j + d = 61 → ev tr t r pub (Sn.c "a" j) = 1
  | 0, j, h => by rw [show j = 61 by omega]; exact ch_a61 hc hcont
  | d + 1, j, h => sn_a_mono hc j (by omega) (ch_a_low hcont d (j + 1) (by omega))

/-- The head's prefix flags. -/
def af (O j : Nat) : Nat := if j ≤ 61 then 1 else if j = 62 then O else 0

theorem ch_a (hcont : ev tr t r pub (Sn.c "cont") = 1) (j : Nat) :
    ev tr t r pub (Sn.a j) = af (ev tr t r pub (Sn.c "odd")) j := by
  unfold af
  rcases Nat.lt_or_ge j 64 with hj | hj
  · rw [sn_a_lt j hj]
    by_cases h1 : j ≤ 61
    · rw [if_pos h1]; exact ch_a_low hc hcont (61 - j) j (by omega)
    by_cases h2 : j = 62
    · subst h2; rw [if_neg h1, if_pos rfl]; exact ch_a62 hc hcont
    · rw [if_neg h1, if_neg h2, show j = 63 by omega]; exact ch_a63 hc hcont
  · rw [sn_a_ge j hj, if_neg (by omega), if_neg (by omega)]; simp

set_option maxHeartbeats 2000000 in
/-- **`ha_m = [m < 32]`** on a continued head. -/
theorem ch_ha (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 1)
    (m : Nat) (hm : m < 33) : ev tr t r pub (Sn.c "ha" m) = if m < 32 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h := sn_hold hc (e := Sn.c "ha" 0 - Sn.c "act") (by unfold Sn.constraints; simp)
    rw [eq_of_sub h, hA]; simp
  · have h0 : m ≠ 0 := by omega
    have h := sn_hold hc (e := Sn.c "ha" m - Sn.c "odd" * Sn.a (2 * m) -
        (1 - Sn.c "odd") * Sn.a (2 * m - 1)) (by
      unfold Sn.constraints
      simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      mem_search m hm)
    have h' := eq_of_sub h
    have ho := sn_bool hc "odd" (by simp)
    simp only [ev_sub, ev_hmul, ev_one, ch_a hc hcont] at h'
    have hha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Sn.c "ha" m)
    generalize ev tr t r pub (Sn.c "ha" m) = H at h' hha ⊢
    generalize ev tr t r pub (Sn.c "odd") = O at h' ho ⊢
    have ea : af O (2 * m) = (if m ≤ 30 then 1 else if m = 31 then O else 0) := by
      unfold af; (repeat' split) <;> omega
    have eb : af O (2 * m - 1) = (if m ≤ 31 then 1 else 0) := by
      unfold af; (repeat' split) <;> omega
    rw [ea, eb] at h'
    clear h ea eb
    rcases (by omega : O = 0 ∨ O = 1) with rfl | rfl <;> (repeat' split at h') <;> (repeat' split) <;>
      simp (config := { failIfUnchanged := false }) at h' <;> omega

/-- `Σ_{m<33} ha_m = 32`. -/
theorem ch_sum_ha (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 1) :
    ((List.range HPMAX).map fun m => ev tr t r pub (Sn.c "ha" m)).sum = 32 := by
  have hs : ((List.range HPMAX).map fun m => ev tr t r pub (Sn.c "ha" m)) =
      (List.range 33).map fun m => if m < 32 then 1 else 0 := by
    simp only [HPMAX]
    apply List.map_congr_left
    intro m hm; simp only [List.mem_range] at hm
    exact ch_ha hc hA hcont m hm
  rw [hs, sum_ind_le _ _ (by decide)]

set_option maxHeartbeats 2000000 in
/-- **`hplen = 32 + rl/2`** on a continued head whose `rl` is even and small. -/
theorem ch_hplen (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 1)
    (hev : ev tr t r pub (Sn.c "rl") % 2 = 0) (hlt : ev tr t r pub (Sn.c "rl") < 2 ^ 28) :
    ev tr t r pub (Sn.c "hplen") = 32 + ev tr t r pub (Sn.c "rl") / 2 := by
  have h := sn_hold hc (e := sm 2 (Sn.c "hplen") -
      sm 2 (sumE ((List.range HPMAX).map fun m => Sn.c "ha" m)) - Sn.c "rl") (by
    unfold Sn.constraints; simp)
  have h1 := eq_of_sub h
  have h2 := sub_val' (v := ev tr t r pub (Sn.c "rl")) h1
  have e1 : ev tr t r pub (sm 2 (Sn.c "hplen")) = 2 * ev tr t r pub (Sn.c "hplen") % P := by
    change ev tr t r pub (Expr.mul (.const 2) _) = _
    rw [ev_mul, ev_const, show 2 % P = 2 from rfl]
  have e2 : ev tr t r pub (sm 2 (sumE ((List.range HPMAX).map fun m => Sn.c "ha" m))) = 64 := by
    change ev tr t r pub (Expr.mul (.const 2) _) = _
    rw [ev_mul, ev_const, show 2 % P = 2 from rfl, ev_sumE, List.map_map]
    have := ch_sum_ha hc hA hcont
    simp only [Function.comp_def] at this ⊢
    rw [this]
  rw [e1, e2] at h2
  exact half_rl P _ _ (by decide) (by decide) (ev_lt _) hev hlt h2

/-- `gold ⇒ gsha` on a continued head. -/
theorem ch_gsha (hcont : ev tr t r pub (Sn.c "cont") = 1) (hg : ev tr t r pub (Sn.c "gold") = 1) :
    ev tr t r pub (Sn.c "gsha") = 1 := by
  have h := ch_gate hc hcont (e := Sn.c "gold" - Sn.c "gsha") (by unfold Sn.constraints; simp)
  rw [← eq_of_sub h, hg]

/-- `nref = 0` on a continued head. -/
theorem ch_nref (hcont : ev tr t r pub (Sn.c "cont") = 1) : ev tr t r pub (Sn.c "nref") = 0 :=
  ch_gate hc hcont (e := Sn.c "nref") (by unfold Sn.constraints; simp)

/-- `gnew ⇒ gfin` on a continued head. -/
theorem ch_gfin (hcont : ev tr t r pub (Sn.c "cont") = 1) (hg : ev tr t r pub (Sn.c "gnew") = 1) :
    ev tr t r pub Sn.gfin = 1 := by
  unfold Sn.gfin
  rw [ev_sub, hg, ch_nref hc hcont]

end

end StateM5a.SnContHead
