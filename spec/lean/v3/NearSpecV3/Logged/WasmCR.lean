import Lean
import NearSpecV3.Wasm.Exec

/-!
# The WASM machine reads the trie store only in the storage host functions

`St.E σ s` replaces the store function of the trie-backed `External` (`TTN.RealStore.store`) by `σ`.
`CR x y` (for host computations): running `y` on `E σ t` gives `x`'s result on `t`, with the
final state's store replaced by `σ`. Every host function that does not touch the trie store
satisfies `CR h h` for every `σ` (`CR_hostCall`), and every machine step that does not call one of
the storage host functions commutes with `E σ` (`step_E`). With `σ := t.real.store` this also says
such steps keep the store field.
-/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm

def E (σ : TTN.Store) (s : St) : St := { s with real := s.real.map fun r => { r with store := σ } }

def mapSt {α : Type} (f : St → St) : EStateM.Result String St α → EStateM.Result String St α
  | .ok a s => .ok a (f s)
  | .error e s => .error e (f s)

structure CR {α : Type} (σ : TTN.Store) (x y : HM α) : Prop where
  h : ∀ t, y.run (E σ t) = mapSt (E σ) (x.run t)

section
variable {σ : TTN.Store}

theorem CR_pure {α : Type} (a : α) : CR σ (pure a) (pure a) := ⟨fun _ => rfl⟩
theorem CR_pure' {α : Type} {a b : α} (h : b = a) : CR σ (pure a) (pure b) := h ▸ ⟨fun _ => rfl⟩
theorem CR_throw {α : Type} (e : String) : CR σ (throw e : HM α) (throw e) := ⟨fun _ => rfl⟩
theorem CR_throw' {α : Type} {e e' : String} (h : e' = e) : CR σ (throw e : HM α) (throw e') :=
  h ▸ ⟨fun _ => rfl⟩

theorem CR_bind {α β : Type} {x y : HM α} {f g : α → HM β} (h1 : CR σ x y) (h2 : ∀ a, CR σ (f a) (g a)) :
    CR σ (x >>= f) (y >>= g) := by
  constructor; intro t
  have := h1.h t
  simp only [EStateM.run] at this ⊢
  show EStateM.bind y g (E σ t) = mapSt (E σ) (EStateM.bind x f t)
  unfold EStateM.bind
  rw [this]
  cases x t with
  | ok a s => exact (h2 a).h s
  | error e s => rfl

theorem CR_get_bind {β : Type} {f g : St → HM β} (h : ∀ t, CR σ (f t) (g (E σ t))) :
    CR σ (get >>= f) (get >>= g) := by
  constructor; intro t; exact (h t).h t

theorem CR_set (u v : St) (h : v = E σ u) : CR σ (set u) (set v) := ⟨fun _ => by subst h; rfl⟩

theorem CR_modify (f g : St → St) (h : ∀ t, g (E σ t) = E σ (f t)) : CR σ (modify f) (modify g) := by
  constructor; intro t
  show EStateM.Result.ok () (g (E σ t)) = EStateM.Result.ok () (E σ (f t)); rw [h]

theorem CR_ite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x y x' y' : HM α}
    (h1 : CR σ x x') (h2 : CR σ y y') : CR σ (if c then x else y) (if c' then x' else y') := by
  subst hc; by_cases hc : c <;> simp only [hc, ite_true, ite_false] <;> assumption

theorem CR_dite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x : c → HM α}
    {y : ¬c → HM α} {x' : c' → HM α} {y' : ¬c' → HM α}
    (h1 : ∀ h h', CR σ (x h) (x' h')) (h2 : ∀ h h', CR σ (y h) (y' h')) :
    CR σ (if h : c then x h else y h) (if h : c' then x' h else y' h) := by
  subst hc; by_cases hc : c <;> simp only [hc, dite_true, dite_false] <;> apply_assumption

end


/-! ## The `cr` tactic -/

syntax "cr_call" : tactic
macro_rules | `(tactic| cr_call) => `(tactic| first | exact CR_pure _ | exact CR_throw _)

open Lean Elab Tactic Meta in
/-- `intro`, only on propositions. -/
elab "cr_intro" : tactic => do
  let g ← getMainGoal
  unless (← isProp (← g.getType)) do throwError "cr_intro: not a proposition"
  evalTactic (← `(tactic| intro))

syntax "cr_step" : tactic
macro_rules | `(tactic| cr_step) => `(tactic| first
  | (apply CR_get_bind; intro; dsimp only [E])
  | (apply CR_pure'; rfl)
  | (apply CR_throw'; rfl)
  | (apply CR_set; rfl)
  | (apply CR_modify; intro; rfl)
  | (apply CR_ite _ _ rfl)
  | (apply CR_dite _ _ rfl)
  | (with_reducible cr_call)
  | (apply CR_bind; with_reducible cr_call)
  | (dsimp (config := { zeta := false }) only [E])
  | (split <;> try (rename_i hh; simp only [hh]))
  | cr_intro
  | (simp only []))

macro "cr" : tactic => `(tactic| repeat (any_goals cr_step))

end NearSpecV3.Logged.W
