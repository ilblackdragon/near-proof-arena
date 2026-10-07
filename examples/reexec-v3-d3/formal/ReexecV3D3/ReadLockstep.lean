import ReexecV3D3.ReadControl
import ReexecV3D3.Logged.API
import ReexecV3D3.Lockstep

/-! Re-encoding control-flow simulation, separate from read-store restriction. -/
namespace ReexecV3D3.Read

open NearSpec NearSpecV3 NearSpecV3.D2 Logged

variable {K : Type}

theorem checkK_mono (b b' : Bool) (message : String) (h : b = true → b' = true) :
    Refines (checkK (K := K) b message) (checkK b' message) := by
  cases b with
  | false => exact .err message _
  | true => rw [h rfl]; exact .ok ()

/-- Re-encoding implicit values preserves the post-state roots and transition
indices observed by the logged checker. No equality of whole stores is assumed. -/
theorem forIn_implV_post {α β : Type}
    (f : (α × Transition) × Nat → β → SM K (ForInStep β))
    (hf : ∀ a T T' k b, T'.postStateRoot = T.postStateRoot →
      f ((a, T'), k) b = f ((a, T), k) b) :
    ∀ (xs : List α) (iv : List (List Bytes)) (ys : List Transition) (start : Nat) (b : β),
      forIn ((xs.zip (implV iv ys)).zipIdx start) b f =
      forIn ((xs.zip ys).zipIdx start) b f
  | [], _, _, _, _ => by simp
  | _ :: _, _, [], _, _ => by simp [implV]
  | a :: xs, iv, T :: ys, start, b => by
    simp only [implV, List.zip_cons_cons, List.zipIdx_cons, List.forIn_cons]
    rw [hf a T (trV (iv.headD []) T) start b rfl]
    congr 1
    funext step
    cases step with
    | done b => rfl
    | yield b => exact forIn_implV_post f hf xs iv.tail ys (start + 1) b

end ReexecV3D3.Read
