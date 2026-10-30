import NearSpecV3.Wasm.Exec

/-!
# W12 — two-run commutation of host programs with an interpreter-state flag (O2/O3 groundwork)

`St.curveHosts` and `St.globalActions` are read-only flags of the interpreter state: set once at
instantiation, read only at named sites. For a state map `φ` that changes only such a flag,
`CR φ x y` says: running `y` from `φ s` is running `x` from `s` with `φ` applied to every resulting
state (`mapR`), values and errors unchanged. `CR φ x x` is "`x` does not observe the flag".

The step lemmas mirror `FuelHost`'s `HOR` lemmas (`pure`, `throw`, `bind`, `get`, `set`, `modify`,
`if`, `forIn`), so the per-arm theorems can be generated the same way.
-/

namespace NearSpecV3.Wasm

/-- Apply a state map to a host result. -/
def mapR {α : Type} (φ : St → St) : EStateM.Result String St α → EStateM.Result String St α
  | .ok a s => .ok a (φ s)
  | .error e s => .error e (φ s)

/-- Two-run commutation: `y` from `φ s` is `x` from `s`, mapped by `φ`. -/
def CR {α : Type} (φ : St → St) (x y : HM α) : Prop := ∀ s, y.run (φ s) = mapR φ (x.run s)

section
variable {φ : St → St}

theorem CR_pure {α : Type} (a a' : α) (h : a = a') : CR φ (pure a : HM α) (pure a') := by
  subst h; intro s; rfl

theorem CR_throw {α : Type} (e e' : String) (h : e = e') : CR φ (throw e : HM α) (throw e') := by
  subst h; intro s; rfl

theorem CR_bind {α β : Type} {x y : HM α} {f g : α → HM β} (h1 : CR φ x y) (h2 : ∀ a, CR φ (f a) (g a)) :
    CR φ (x >>= f) (y >>= g) := by
  intro s
  show EStateM.bind y g (φ s) = mapR φ (EStateM.bind x f s)
  unfold EStateM.bind
  have := h1 s
  simp only [EStateM.run] at this
  rw [this]
  cases x s with
  | ok a s' => exact h2 a s'
  | error e s' => rfl

theorem CR_get_bind {β : Type} {f g : St → HM β} (h : ∀ t, CR φ (f t) (g (φ t))) :
    CR φ (get >>= f) (get >>= g) := by
  intro s
  exact h s s

theorem CR_set (u u' : St) (h : u' = φ u) : CR φ (set u : HM PUnit) (set u') := by
  subst h; intro s; rfl

theorem CR_modify (f g : St → St) (h : ∀ s, g (φ s) = φ (f s)) : CR φ (modify f : HM PUnit) (modify g) := by
  intro s
  show EStateM.Result.ok () (g (φ s)) = EStateM.Result.ok () (φ (f s))
  rw [h]

theorem CR_ite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x y x' y' : HM α}
    (h1 : CR φ x x') (h2 : CR φ y y') : CR φ (if c then x else y) (if c' then x' else y') := by
  subst hc
  by_cases hh : c <;> simp only [hh, ite_true, ite_false] <;> assumption

theorem CR_forIn_list {β : Type} (l : List Nat) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR φ (f i b) (g i b)) : CR φ (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact CR_pure b b rfl
  | cons a l ih =>
    simp only [List.forIn_cons]
    apply CR_bind (h a b); intro x
    cases x with
    | done b' => exact CR_pure b' b' rfl
    | yield b' => exact ih b'

theorem CR_forIn {β : Type} (rg : Std.Legacy.Range) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR φ (f i b) (g i b)) : CR φ (forIn rg b f) (forIn rg b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']; exact CR_forIn_list _ b f g h

end

/-! ## The curve-host flag -/

/-- Set the curve-host selector. -/
def setCH (b : Bool) (s : St) : St := { s with curveHosts := b }

/-- One step of the two-run walk. -/
macro "cr_step" : tactic => `(tactic| first
  | ((apply CR_get_bind); intro _; dsimp only [setCH])
  | (apply CR_pure; rfl)
  | (apply CR_throw; rfl)
  | (apply CR_set; rfl)
  | (apply CR_modify; intro _; rfl)
  | (apply CR_ite; rfl)
  | (apply CR_forIn; intro _ _)
  | (apply CR_bind)
  | (intro _)
  | split)

macro "cr" : tactic => `(tactic| repeat (any_goals cr_step))

theorem CR_payBaseH (b : Bool) (c : Cost) : CR (setCH b) (payBaseH c) (payBaseH c) := by
  unfold payBaseH withGas
  cr

theorem CR_payPerH (b : Bool) (c : Cost) (n : Nat) : CR (setCH b) (payPerH c n) (payPerH c n) := by
  unfold payPerH withGas
  cr

theorem CR_payActionH (b : Bool) (x y z : Nat) :
    CR (setCH b) (payActionH x y z) (payActionH x y z) := by
  unfold payActionH withGas
  cr

theorem CR_burnH (b : Bool) (x : Nat) : CR (setCH b) (burnH x) (burnH x) := by
  unfold burnH withGas
  cr

#print axioms CR_payBaseH
#print axioms CR_payActionH

end NearSpecV3.Wasm
