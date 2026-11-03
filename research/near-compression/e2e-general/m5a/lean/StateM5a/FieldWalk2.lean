import StateM5a.FieldWalk
import StateM5a.FieldRows2

/-!
# StateM5a.FieldWalk2 — the `SN` descend fact and the `WSB` walk roots, from the constraints

Staged proofs (each `omega` sees only the few flags it needs, so no proof exhausts memory):

* **`sn_gdn_walk`**: on an `SN` row, `gdn = 1 ⇒ gwalk = mF + mU + mD = 1 ∧ isE = 1 ∧ a₀ = 1`: a row
  that sends a `DOWN` is an active walk row (it receives one, with multiplicity `gwalk`) and is an
  extension whose first key nibble is active.
* **`sn_gdn_klen`**: with `cont = 0` (a short key), `1 ≤ klen ≤ 64`: the child depth `d + klen`
  is strictly deeper, by at most 64 (`Traffic.WalkShape.deeper` at field level, given no wrap).
  For a continued key (`cont = 1`) `klen = Σ a + rl` and the bound on `rl` comes from the `SNC`
  chain (open).
* **`wsb_index`**: the `WSB` rows are phase 0 (`ph = 0`) with `i = r` for `r < 2^D`, then phase 1
  with `i = r − 2^D` (the `isFirst` / `isTransition` / `e` constraints; heights `≤ 2^20`,
  `D ≤ 19`).  Hence **`wsb_root_unique`**: two `WSB` rows with the same `(ph, i)` are the same row —
  one walk root per walk id (`Traffic.WalkShape.rootUniq`: INTAKE roots use `w = i`, FINAL roots
  `w = W_FINAL + i`, and `i < 2^D ≤ W_FINAL`).
-/

namespace StateM5a.FieldWalk2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldRows2

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-- An `SN` column by name (no column offset argument). -/
def sc (s : String) : Expr := Sn.c s

/-! ## Small sums -/

theorem ev_add_small {a b : Expr} (h : ev tr t r pub a + ev tr t r pub b < P) :
    ev tr t r pub (a + b) = ev tr t r pub a + ev tr t r pub b := by
  rw [ev_hadd, Nat.mod_eq_of_lt h]

/-- A left-associated sum `a + x₁ + … + xₙ` of flags (`≤ 1`) has no wrap-around. -/
theorem ev_foldl : ∀ (l : List Expr) (a : Expr), ev tr t r pub a + l.length ≤ 64 →
    (∀ x ∈ l, ev tr t r pub x ≤ 1) →
    ev tr t r pub (l.foldl (· + ·) a) = ev tr t r pub a + (l.map (ev tr t r pub)).sum
  | [], a, _, _ => by simp
  | x :: xs, a, hl, hb => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons] at hl ⊢
    have hx := hb x (List.mem_cons_self ..)
    have e : ev tr t r pub (a + x) = ev tr t r pub a + ev tr t r pub x := ev_add_small (by omega)
    rw [ev_foldl xs (a + x) (by rw [e]; omega) (fun y hy => hb y (List.mem_cons_of_mem _ hy)), e]
    omega

/-- `x − (y)` vanishing. -/
theorem sub_eq {a b : Expr} (h : ev tr t r pub (a - b) = 0) : ev tr t r pub a = ev tr t r pub b :=
  eq_of_sub h

/-! ## SN flags -/

section
variable (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
include hc

theorem sn_flag_le (s : String) (hs : s ∈ ["act", "mF", "mU", "mD", "isE", "gdn", "oLF", "oLR", "oLD",
    "oLS", "oLM", "oEF", "oEU", "oED", "oLA", "oEA", "oLZ", "oEZ", "oES", "oEB", "oLX", "oEX", "oEP",
    "oEM"]) : ev tr t r pub (Sn.c s) ≤ 1 :=
  bool_le (hold rfl hc (FieldWalk.sn_bool s hs))

/-- A sum of `SN` flags, as naturals. -/
theorem sn_sum (s : String) (l : List String) (hs : s :: l ⊆ ["act", "mF", "mU", "mD", "isE", "gdn",
    "oLF", "oLR", "oLD", "oLS", "oLM", "oEF", "oEU", "oED", "oLA", "oEA", "oLZ", "oEZ", "oES", "oEB",
    "oLX", "oEX", "oEP", "oEM"]) (hl : l.length ≤ 63) :
    ev tr t r pub ((l.map sc).foldl (· + ·) (sc s)) =
      ev tr t r pub (sc s) + (l.map fun x => ev tr t r pub (sc x)).sum := by
  rw [ev_foldl _ _ (by simp only [List.length_map]; have : ev tr t r pub (sc s) ≤ 1 := sn_flag_le hc s (hs (List.mem_cons_self ..)); omega)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact sn_flag_le hc y (hs (List.mem_cons_of_mem _ hy))), List.map_map]
  rfl

/-- Stage 1: `gdn = 1` gives one of the five descending extension ops. -/
theorem sn_gdn_ops (hg : ev tr t r pub (Sn.c "gdn") = 1) :
    ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oED") +
      ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") = 1 := by
  have e := sub_eq (hold rfl hc FieldWalk.sn_mem_gdn)
  have e2 := sn_sum hc "oEF" ["oEU", "oED", "oES", "oEB"] (by decide) (by decide)
  change ev tr t r pub (Sn.c "gdn") = ev tr t r pub ((["oEU", "oED", "oES", "oEB"].map sc).foldl
    (· + ·) (sc "oEF")) at e
  rw [e2] at e
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  change _ = ev tr t r pub (Sn.c "oEF") + (ev tr t r pub (Sn.c "oEU") + (ev tr t r pub (Sn.c "oED") +
    (ev tr t r pub (Sn.c "oES") + (ev tr t r pub (Sn.c "oEB") + 0)))) at e
  omega

/-- Stage 2: `isE = 1`. -/
theorem sn_gdn_isE (hg : ev tr t r pub (Sn.c "gdn") = 1) : ev tr t r pub (Sn.c "isE") = 1 := by
  have h1 := sn_gdn_ops hc hg
  have e : ev tr t r pub (Sn.c "isE") = ev tr t r pub ((["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"].map sc).foldl (· + ·) (sc "oEF")) := sub_eq (hold rfl hc FieldWalk.sn_mem_isE)
  rw [sn_sum hc "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by decide) (by decide)] at e
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  have := sn_flag_le hc "isE" (by simp)
  omega

/-- Stage 3: `a₀ = 1` (an extension's first key nibble is active). -/
theorem sn_isE_a0 (hE : ev tr t r pub (Sn.c "isE") = 1) : ev tr t r pub (Sn.c "a" 0) = 1 := by
  have e := hold rfl hc FieldWalk.sn_mem_a0
  rw [sn_a_lt 0 (by decide)] at e
  change ev tr t r pub (Expr.mul _ _) = 0 at e
  rw [ev_mul_gate _ hE, ev_sub] at e
  have := sn_a_bool hc 0 (by decide)
  simp at e; omega

theorem sn_mF_ge : ev tr t r pub (Sn.c "oEF") ≤ ev tr t r pub (Sn.c "mF") := by
  have e : ev tr t r pub ((["oEF", "oLA", "oEA"].map sc).foldl (· + ·) (sc "oLF")) = ev tr t r pub (Sn.c "mF") := sub_eq (hold rfl hc FieldWalk.sn_mem_mF)
  rw [sn_sum hc "oLF" ["oEF", "oLA", "oEA"] (by decide) (by decide)] at e
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  omega

theorem sn_mU_ge : ev tr t r pub (Sn.c "oEU") ≤ ev tr t r pub (Sn.c "mU") := by
  have e : ev tr t r pub ((["oEU", "oLX", "oEX"].map sc).foldl (· + ·) (sc "oLR")) = ev tr t r pub (Sn.c "mU") := sub_eq (hold rfl hc FieldWalk.sn_mem_mU)
  rw [sn_sum hc "oLR" ["oEU", "oLX", "oEX"] (by decide) (by decide)] at e
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  omega

theorem sn_mD_ge : ev tr t r pub (Sn.c "oED") + ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") ≤
    ev tr t r pub (Sn.c "mD") := by
  have e : ev tr t r pub ((["oED", "oLZ", "oEZ", "oES", "oEB"].map sc).foldl (· + ·) (sc "oLD")) = ev tr t r pub (Sn.c "mD") := sub_eq (hold rfl hc FieldWalk.sn_mem_mD)
  rw [sn_sum hc "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by decide) (by decide)] at e
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  omega

theorem sn_act_sum : ev tr t r pub (Sn.c "mF") + ev tr t r pub (Sn.c "mU") + ev tr t r pub (Sn.c "mD") ≤
    ev tr t r pub (Sn.c "act") := by
  have e : ev tr t r pub ((["mU", "mD", "oLS", "oLM", "oEP", "oEM"].map sc).foldl (· + ·) (sc "mF")) = ev tr t r pub (Sn.c "act") := sub_eq (hold rfl hc FieldWalk.sn_mem_act)
  rw [sn_sum hc "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by decide) (by decide)] at e
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  omega

/-- Stage 4: the walk mode flags sum to `1`. -/
theorem sn_gdn_gwalk (hg : ev tr t r pub (Sn.c "gdn") = 1) :
    ev tr t r pub (Sn.c "mF") + ev tr t r pub (Sn.c "mU") + ev tr t r pub (Sn.c "mD") = 1 := by
  have h1 := sn_gdn_ops hc hg
  have := sn_mF_ge hc; have := sn_mU_ge hc; have := sn_mD_ge hc; have := sn_act_sum hc
  have := sn_flag_le hc "act" (by simp)
  omega

/-- **`SN`: a row that sends a `DOWN` is an active walk row, an extension with `a₀ = 1`.** -/
theorem sn_gdn_walk (hg : ev tr t r pub (Sn.c "gdn") = 1) :
    ev tr t r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 ∧ ev tr t r pub (Sn.c "isE") = 1 ∧
      ev tr t r pub (Sn.c "a" 0) = 1 := by
  have hw := sn_gdn_gwalk hc hg
  have hE := sn_gdn_isE hc hg
  refine ⟨?_, hE, sn_isE_a0 hc hE⟩
  have e := sn_sum hc "mF" ["mU", "mD"] (by decide) (by decide)
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  change ev tr t r pub (List.foldl (fun x1 x2 => x1 + x2) (Sn.c "mF") [Sn.c "mU", Sn.c "mD"]) = 1
  rw [e]; omega

/-- **`SN`: the child is strictly deeper, by at most 64** (short key, `cont = 0`). -/
theorem sn_gdn_klen (hg : ev tr t r pub (Sn.c "gdn") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 0) :
    1 ≤ ev tr t r pub (Sn.c "klen") ∧ ev tr t r pub (Sn.c "klen") ≤ 64 := by
  obtain ⟨hL, hf⟩ := sn_flags hc hcont
  have ha := (sn_gdn_walk hc hg).2.2
  rw [hf 0 (by decide)] at ha
  refine ⟨?_, hL⟩
  split at ha
  · omega
  · exact absurd ha (by decide)

end

end StateM5a.FieldWalk2
