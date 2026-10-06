import ZkFormal.V2.Np.Main

/-!
# ZkFormal.V2.G.Defs — P2: `auxGroup ∈ {1,2,3}` for `np-udr-stark-v2`

v1's L3 (and v2's copy of it) requires `prm = Params.default`, whose `auxGroup` is 1: every
running-product column accumulates one interaction.  P2 (V3-D0-DESIGN §5.3) allows
`prm = pg g := {Params.default with auxGroup := g}` for `1 ≤ g ≤ 3` in v2.  Nothing in v1
changes: v1 keeps `NpOk` (`prm = Params.default = pg 1`).

* `pg g` — the parameter set; every field other than `auxGroup` is v1's, so all numerics
  (`logBlowup = 4`, `maxLogLde = 26`, …) reduce by `rfl`.
* `NpOkG A prm` — v1's `NpOk` with `prm = Params.default` relaxed to `∃ g, prm = pg g ∧ 1 ≤ g ≤ 3`.
* `NpOkPg AP prm` — v2's `NpOkP` with `NpOkG` in place of `NpOk`.
* round obligations `MsgAtPg`, `ChalAtPg`, `QueryStmtPg` (v2's with `NpOkPg`).
* `chunksOf` facts: for `g ≥ 1` the groups partition the list (`chunksOf_flatten`), there are
  `numGroups` of them (`chunksOf_length`), each of length `≤ g`, and `chunksOf` commutes with `map`.

The table-degree side condition `Table.degree t g ≤ 2^logBlowup` is part of v1's
`headerOk` (checked by the verifier) and so needs no extra hypothesis.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

/-- v1's deployed parameters with `auxGroup := g`. -/
def pg (g : Nat) : Params := { Params.default with auxGroup := g }

@[simp] theorem pg_auxGroup (g : Nat) : (pg g).auxGroup = g := rfl
theorem pg_one : pg 1 = Params.default := rfl

/-- v1's `NpOk` with the group size relaxed to `1 ≤ g ≤ 3`. -/
def NpOkG (A : Air) (prm : Params) : Prop :=
  (∃ g, prm = pg g ∧ 1 ≤ g ∧ g ≤ 3) ∧
  (∀ T ∈ A.tables, T.allConstraints.length + 2 * T.auxCount prm.auxGroup + 3 * T.interactions.length
    ≤ 2 ^ 20) ∧
  A.numBuses < 2 ^ 30

theorem npOkG_of_npOk {A : Air} {prm : Params} (h : NpOk A prm) : NpOkG A prm :=
  ⟨⟨1, h.1, Nat.le_refl 1, by decide⟩, h.2⟩

/-- v2's side conditions with `auxGroup ∈ {1,2,3}`. -/
def NpOkPg (AP : AirP) (prm : Params) : Prop :=
  NpOkG AP.toAir prm ∧ AP.wf (2 ^ prm.logBlowup) = true

theorem npOkPg_of_npOkP {AP : AirP} {prm : Params} (h : NpOkP AP prm) : NpOkPg AP prm :=
  ⟨npOkG_of_npOk h.1, h.2⟩

/-- A message transition at `E = k` (for claims whose segments fit). -/
def MsgAtPg (k : Nat) : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkPg AP prm → ∀ (τ : PTn) m, ¬ PubBad AP τ →
    Shaped (VnpP AP prm) (τ.push m) → (VnpP AP prm).NextIsProver τ → τ.entries.length = k →
    StageP AP prm τ → StageP AP prm (τ.push m)

/-- A challenge transition at `E = k` (for claims whose segments fit). -/
def ChalAtPg (k : Nat) : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkPg AP prm → ∀ τ : PTn, ¬ PubBad AP τ →
    Shaped (VnpP AP prm) τ → (VnpP AP prm).NextIsChal τ → τ.entries.length = k → StageP AP prm τ →
    count Fp8.all (fun c => Shaped (VnpP AP prm) (τ.pushChal c) ∧ ¬ StageP AP prm (τ.pushChal c)) ≤
      badBudget

def QueryStmtPg : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkPg AP prm → ∀ τ : PTn,
    StageP AP prm τ → (VnpP AP prm).AtQuery τ → Shaped (VnpP AP prm) τ →
    (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true →
    count (List.range ((VnpP AP prm).domSize τ))
      (fun x => (VnpP AP prm).ChecksPass τ x ((VnpP AP prm).trueOpenings τ x)) ≤
      agreeUdr prm.logBlowup ((VnpP AP prm).domSize τ)

/-! ## `chunksOf` -/

section
variable {α β : Type}

theorem chunksOf_go_map (g : Nat) (f : α → β) : ∀ (n : Nat) (l : List α),
    chunksOf.go g n (l.map f) = (chunksOf.go g n l).map (List.map f)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => by
    have ih := chunksOf_go_map g f n ((a :: l).drop g)
    simp only [List.map_cons] at ih ⊢
    show List.take g ((a :: l).map f) :: chunksOf.go g n (List.drop g ((a :: l).map f)) =
      (List.take g (a :: l) :: chunksOf.go g n (List.drop g (a :: l))).map (List.map f)
    rw [← List.map_drop, ih]; simp only [List.map_cons, List.map_take]

theorem chunksOf_map (g : Nat) (f : α → β) (l : List α) :
    chunksOf g (l.map f) = (chunksOf g l).map (List.map f) := by
  unfold chunksOf; rw [List.length_map]; exact chunksOf_go_map g f _ l

theorem chunksOf_go_flatten {g : Nat} (hg : 1 ≤ g) : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (chunksOf.go g n l).flatten = l
  | 0, l, h => by rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | _ + 1, [], _ => rfl
  | n + 1, a :: l, h => by
    simp only [chunksOf.go, List.flatten_cons]
    rw [chunksOf_go_flatten hg n _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega)]
    exact List.take_append_drop _ _

theorem chunksOf_flatten {g : Nat} (hg : 1 ≤ g) (l : List α) : (chunksOf g l).flatten = l :=
  chunksOf_go_flatten hg _ l (Nat.le_refl _)

theorem numGroups_succ {g : Nat} (hg : 1 ≤ g) (m : Nat) :
    numGroups (m + 1) g = numGroups (m + 1 - g) g + 1 := by
  unfold numGroups
  rw [Nat.max_eq_left hg]
  by_cases h : m + 1 ≤ g
  · have e1 : (m + 1 + g - 1) / g = 1 := by
      rw [show m + 1 + g - 1 = m + g by omega, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt (by omega)]
    have e2 : (m + 1 - g + g - 1) / g = 0 := Nat.div_eq_of_lt (by omega)
    rw [e1, e2]
  · rw [show m + 1 + g - 1 = m + g by omega, show m + 1 - g + g - 1 = m by omega,
      Nat.add_div_right _ (by omega)]

theorem chunksOf_go_length {g : Nat} (hg : 1 ≤ g) : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (chunksOf.go g n l).length = numGroups l.length g
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    simp only [chunksOf.go, List.length_nil, numGroups, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | _ + 1, [], _ => by
    simp only [chunksOf.go, List.length_nil, numGroups, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | n + 1, a :: l, h => by
    simp only [chunksOf.go, List.length_cons]
    rw [chunksOf_go_length hg n _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega),
      List.length_drop, List.length_cons, numGroups_succ hg]

theorem chunksOf_length {g : Nat} (hg : 1 ≤ g) (l : List α) :
    (chunksOf g l).length = numGroups l.length g :=
  chunksOf_go_length hg _ l (Nat.le_refl _)

theorem chunksOf_go_le (g : Nat) : ∀ (n : Nat) (l : List α), ∀ c ∈ chunksOf.go g n l, c.length ≤ g
  | 0, _, c, h => by simp [chunksOf.go] at h
  | _ + 1, [], c, h => by simp [chunksOf.go] at h
  | n + 1, a :: l, c, h => by
    simp only [chunksOf.go, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.length_take_le _ _
    · exact chunksOf_go_le g n _ c h

theorem chunksOf_le (g : Nat) (l : List α) : ∀ c ∈ chunksOf g l, c.length ≤ g :=
  chunksOf_go_le g _ l

theorem chunksOf_go_sub (g : Nat) : ∀ (n : Nat) (l : List α), ∀ c ∈ chunksOf.go g n l, ∀ a ∈ c, a ∈ l
  | 0, _, c, h, _, _ => by simp [chunksOf.go] at h
  | _ + 1, [], c, h, _, _ => by simp [chunksOf.go] at h
  | n + 1, b :: l, c, h, a, ha => by
    simp only [chunksOf.go, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_of_mem_take ha
    · exact List.mem_of_mem_drop (chunksOf_go_sub g n _ c h a ha)

theorem numGroups_le {g : Nat} (hg : 1 ≤ g) (n : Nat) : numGroups n g ≤ n := by
  unfold numGroups
  rw [Nat.max_eq_left hg]
  cases n with
  | zero => exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
  | succ m =>
    refine Nat.div_le_of_le_mul ?_
    have : m ≤ g * m := Nat.le_mul_of_pos_left m (by omega)
    rw [Nat.mul_succ]; omega

end

end ZkFormal.V2.G
