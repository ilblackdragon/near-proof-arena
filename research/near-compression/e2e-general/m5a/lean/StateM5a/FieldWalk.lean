import StateM5a.FieldRows

/-!
# StateM5a.FieldWalk — the walk-shape facts of `Traffic.WalkShape` from the constraints

`Traffic.walk_unique` needs (i) a row that sends a `DOWN` is an active walk row (it receives
one: the multiplicity of its `DOWN` send is `gdn`, of its receive `gold` / `gwalk`), and (ii) the
child depth is strictly greater (`BR`: `d + 1`; `SN`: `d + klen` with `klen ≥ 1`, since only
extensions descend and an extension's first key nibble is active).  From the tables' constraints
over BabyBear (one-hot op bundles, booleanity):

* `br_gdn_gold`: on a `BR` row, `gdn = 1 ⇒ gold = 1`;
* `SN`: the booleanity of the op flags (`sn_bool`) and the one-hot / `isE·(1 − a₀)` constraint
  memberships (`sn_mem_*`).  The `SN` analogue (`gdn = 1 ⇒ gwalk = 1 ∧ isE = 1 ∧ a₀ = 1`, then
  `1 ≤ klen` via `FieldRows2.sn_flags`) is open: the direct `omega` proof exhausts memory on the
  24-flag bundle and needs a staged proof.
-/

namespace StateM5a.FieldWalk

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-! ## BR -/

set_option maxHeartbeats 4000000 in
theorem br_bool (s : String) (hs : s ∈ ["act", "mF", "mU", "mD", "gdn", "oFD", "oFA", "oUD", "oUN",
    "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"]) :
    bool (Br.c s) ∈ Br.constraints := by
  unfold Br.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Br.ops]


theorem br_mem_act : Br.c "mF" + Br.c "mU" + Br.c "mD" + Br.c "oSL" - Br.c "act" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_mF : Br.c "oFD" + Br.c "oFA" + Br.c "oFV" - Br.c "mF" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_mU : Br.c "oUD" + Br.c "oUN" + Br.c "oUV" - Br.c "mU" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_mD : Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDA" + Br.c "oDS" +
    Br.c "oDV" + Br.c "oDZ" - Br.c "mD" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_gdn : Br.c "gdn" - (Br.c "oFD" + Br.c "oUD" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" +
    Br.c "oD1" + Br.c "oDS") ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

set_option maxHeartbeats 4000000 in
/-- **`BR`: a row that sends a `DOWN` is an active walk row** (`gdn = 1 ⇒ gold = act − oSL = 1`;
the one-hot op bundles). -/
theorem br_gdn_gold (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Br.c "gdn") = 1) : ev tr t r pub Br.gold = 1 := by
  have hb : ∀ s ∈ ["act", "mF", "mU", "mD", "gdn", "oFD", "oFA", "oUD", "oUN",
      "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"],
      ev tr t r pub (Br.c s) ≤ 1 := fun s hs => bool_le (hold rfl hc (br_bool s hs))
  have e1 := eq_of_sub (hold rfl hc br_mem_act)
  have e2 := eq_of_sub (hold rfl hc br_mem_mF)
  have e3 := eq_of_sub (hold rfl hc br_mem_mU)
  have e4 := eq_of_sub (hold rfl hc br_mem_mD)
  have e5 := eq_of_sub (hold rfl hc br_mem_gdn)
  simp only [ev_hadd] at e1 e2 e3 e4 e5
  unfold Br.gold; rw [ev_sub]
  have hSL := hb "oSL" (by simp)
  have := hb "act" (by simp); have := hb "mF" (by simp); have := hb "mU" (by simp)
  have := hb "mD" (by simp); have := hb "oFD" (by simp); have := hb "oFA" (by simp)
  have := hb "oUD" (by simp); have := hb "oUN" (by simp); have := hb "oDH" (by simp)
  have := hb "oDL" (by simp); have := hb "oDN" (by simp); have := hb "oD1" (by simp)
  have := hb "oFV" (by simp); have := hb "oDA" (by simp); have := hb "oDS" (by simp)
  have := hb "oSL" (by simp); have := hb "oUV" (by simp); have := hb "oDV" (by simp)
  have := hb "oDZ" (by simp)
  simp (disch := omega) only [Nat.mod_eq_of_lt] at e1 e2 e3 e4 e5
  rcases (by omega : ev tr t r pub (Br.c "oSL") = 0 ∨ ev tr t r pub (Br.c "oSL") = 1) with h | h <;>
    rw [h] <;> simp (disch := omega) only [Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt] <;>
    omega


/-! ## SN -/
theorem sn_mem_mF : Sn.c "oLF" + Sn.c "oEF" + Sn.c "oLA" + Sn.c "oEA" - Sn.c "mF" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_mU : Sn.c "oLR" + Sn.c "oEU" + Sn.c "oLX" + Sn.c "oEX" - Sn.c "mU" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_mD : Sn.c "oLD" + Sn.c "oED" + Sn.c "oLZ" + Sn.c "oEZ" + Sn.c "oES" + Sn.c "oEB" -
    Sn.c "mD" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_act : Sn.c "mF" + Sn.c "mU" + Sn.c "mD" + Sn.c "oLS" + Sn.c "oLM" + Sn.c "oEP" +
    Sn.c "oEM" - Sn.c "act" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_isE : Sn.c "isE" - (Sn.c "oEF" + Sn.c "oEU" + Sn.c "oED" + Sn.c "oEA" + Sn.c "oEZ" +
    Sn.c "oES" + Sn.c "oEB" + Sn.c "oEX" + Sn.c "oEP" + Sn.c "oEM") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gdn : Sn.c "gdn" - (Sn.c "oEF" + Sn.c "oEU" + Sn.c "oED" + Sn.c "oES" + Sn.c "oEB") ∈
    Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_a0 : Sn.c "isE" * (1 - Sn.a 0) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp


set_option maxHeartbeats 4000000 in
theorem sn_bool (s : String) (hs : s ∈ ["act", "mF", "mU", "mD", "isE", "gdn", "oLF", "oLR", "oLD",
    "oLS", "oLM", "oEF", "oEU", "oED", "oLA", "oEA", "oLZ", "oEZ", "oES", "oEB", "oLX", "oEX", "oEP",
    "oEM"]) : bool (Sn.c s) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Sn.ops]

end StateM5a.FieldWalk
