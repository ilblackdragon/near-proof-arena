import NearSpecV3.ChunkValidationV0
import ReexecV3D0.Size

/-!
# `RelD0` ignores the validator-ignored transition field `block_hash`

`norm s` replaces every `ChunkStateTransition.block_hash` of a decoded witness by
32 zero bytes. `checkD0` never reads those fields (nor the chunk header's
`height_included` / signature, which the decoder already drops), so a witness file
whose state witness decodes to `norm s` and is no longer than the original is
accepted whenever the original is (`checkD0_norm`).
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

def zeroHash : Bytes := List.replicate 32 0

def zt (t : Transition) : Transition := { t with blockHash := zeroHash }

def norm (s : StateWitness) : StateWitness :=
  { s with main := zt s.main, implicit := s.implicit.map zt }

theorem forIn_zip_map_zt {α β : Type} (xs : List α) (ys : List Transition) (init : β)
    (f : α × Transition → β → Except String (ForInStep β))
    (hf : ∀ M T b, f (M, zt T) b = f (M, T) b) :
    forIn (xs.zip (ys.map zt)) init f = forIn (xs.zip ys) init f := by
  induction xs generalizing ys init with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zip_cons_cons, List.forIn_cons, hf]
      congr 1
      funext r
      cases r with
      | done b => rfl
      | yield b => exact ih ys b

theorem forIn_zip_norm {α β : Type} (xs : List α) (s : StateWitness) (init : β)
    (f : α × Transition → β → Except String (ForInStep β)) :
    forIn (xs.zip (norm s).implicit) init f =
      forIn (xs.zip s.implicit) init (fun p b => f (p.1, zt p.2) b) := by
  show forIn (xs.zip (s.implicit.map zt)) init f = _
  rw [List.zip_map_right, List.forIn_map]
  rfl

@[simp] theorem norm_implicit_length (s : StateWitness) :
    (norm s).implicit.length = s.implicit.length := by simp [norm]

theorem check_true (m : String) : NearSpecV3.check true m = .ok () := rfl

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

set_option maxHeartbeats 1000000 in
theorem checkD0_norm {cb w w' sw sw' : Bytes} {s : StateWitness}
    (hw : decodeWitnessFile w = .ok (sw, [])) (hw' : decodeWitnessFile w' = .ok (sw', []))
    (hl : lenT sw' ≤ lenT sw)
    (hs : decodeStateWitness sw = .ok s) (hs' : decodeStateWitness sw' = .ok (norm s))
    (h : checkD0 cb w = .ok ()) : checkD0 cb w' = .ok () := by
  unfold checkD0 at h ⊢
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [hc, ok_bind]
  rw [hw, ok_bind] at h
  rw [hw', ok_bind]
  simp only [List.isEmpty_nil, check_true, ok_bind] at h ⊢
  obtain ⟨u2, h2, h⟩ := bind_ok h
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  have hlen' : lenT sw' ≤ 8388608 := Nat.le_trans hl hlen
  rw [decide_eq_true hlen', check_true, ok_bind]
  rw [hs, ok_bind] at h
  rw [hs', ok_bind]
  simp only [forIn_zip_norm, norm_implicit_length]
  exact h

end ReexecV3D0
