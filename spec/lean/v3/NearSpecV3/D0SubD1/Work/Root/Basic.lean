import NearSpecV3.ChunkValidationD1
import NearSpecV3.ChunkValidationD1Out

/-!
# `NearSpecV3.D0SubD1.Work.Root.Basic` — helpers for the D0 ⊆ D1 lockstep

Small, name-stable facts used by the root assembly (`NearSpecV3.D0SubD1.relD0_imp_relD1`) and by its
children.  Everything here is about `Except`, `check` and `NearSpec.Bytes` lists: no new
mathematics.
-/

namespace NearSpecV3.D0SubD1.Work.Root

open NearSpec NearSpecV3

/-! ## `Except` plumbing -/

theorem bind_assoc {α β γ} (x : Except String α) (f : α → Except String β)
    (g : β → Except String γ) : (x >>= f) >>= g = x >>= fun v => f v >>= g := by
  cases x <;> rfl

theorem bind_ok {α β} (a : α) (f : α → Except String β) : (Except.ok a >>= f) = f a := rfl

theorem bind_error {α β} (e : String) (f : α → Except String β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem map_ok_iff {α β} (x : Except String α) (b : β) :
    x.map (fun _ => b) = .ok b ↔ ∃ a, x = .ok a := by
  cases x <;> simp [Except.map, Except.mapError]

theorem map_ok_of_ok {α β} (x : Except String α) (a : α) (f : α → β) (h : x = .ok a) :
    x.map f = .ok (f a) := by rw [h]; rfl

theorem mapError_eq_ok_iff {α} (x : Except String α) (f : String → String) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-- Peel one `bind` off a successful computation: the first component succeeded and so did the
continuation at its value.  This is the workhorse of the lockstep: it needs no case analysis on
the *shape* of the scrutinee, only on its value. -/
theorem bind_ok_exists {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => nomatch h

/-- A `check` succeeds exactly when its boolean is true. -/
theorem check_ok_iff (b : Bool) (m : String) : check b m = .ok () ↔ b = true := by
  unfold check; cases b <;> simp

theorem check_eq_true {b : Bool} {m : String} (h : check b m = .ok ()) : b = true :=
  (check_ok_iff b m).1 h

theorem check_of_true {b : Bool} (m : String) (h : b = true) : check b m = .ok () :=
  (check_ok_iff b m).2 h

/-- The `check` expression, written as the `if` it is, for the lockstep. -/
theorem check_def' (b : Bool) (m : String) : check b m = if b then .ok () else .error m := rfl

/-- Facts coming out of a `check` chain: the boolean is `true`. -/
theorem of_beq {a b : Bytes} (h : (a == b) = true) : a = b := by simpa using h

/-! ## `List` facts used at the D1-only steps -/

theorem append_nil {α : Type} (xs : List α) : xs ++ [] = xs := List.append_nil xs

theorem map_nil {α β : Type} (f : α → β) : ([] : List α).map f = [] := rfl

theorem isEmpty_eq_true_iff {α : Type} {xs : List α} : xs.isEmpty = true ↔ xs = [] := by
  cases xs <;> simp [List.isEmpty]

theorem eq_nil_of_isEmpty {α : Type} {xs : List α} (h : xs.isEmpty = true) : xs = [] :=
  isEmpty_eq_true_iff.1 h

theorem length_eq_zero_of_isEmpty {α : Type} {xs : List α} (h : xs.isEmpty = true) :
    xs.length = 0 := by
  rw [eq_nil_of_isEmpty h]; rfl

theorem nil_zip {α β : Type} (ys : List β) : ([] : List α).zip ys = [] := rfl

theorem zip_nil {α β : Type} (xs : List α) : xs.zip ([] : List β) = [] := by
  cases xs <;> rfl

end NearSpecV3.D0SubD1.Work.Root
