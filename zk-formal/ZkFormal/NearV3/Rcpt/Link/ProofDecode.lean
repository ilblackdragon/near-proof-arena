import ZkFormal.V3.RefundCodec
import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3
open NearSpec NearSpecV3 Sched

/-- Successful vector decoding preserves any pointwise parser invariant. -/
theorem pMany_pred {α : Type} (p : P α) (Q : α → Prop)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → Q a) :
    ∀ n bs xs rest, pMany p n bs = .ok (xs, rest) → ∀ a ∈ xs, Q a := by
  intro n
  induction n with
  | zero => intro bs xs rest h; cases h; simp
  | succ n ih =>
    intro bs xs rest h
    unfold pMany at h
    obtain ⟨⟨a, tail⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨ys, tail'⟩, hs, h⟩ := bind_ok h
    cases h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp _ _ _ ha
    · exact ih _ _ _ hs x hx

theorem pVec_pred {α : Type} (p : P α) (Q : α → Prop)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → Q a)
    {w : String} {bs rest : Bytes} {xs : List α} (h : pVec w p bs = .ok (xs, rest)) :
    ∀ a ∈ xs, Q a := by
  unfold pVec at h
  obtain ⟨⟨n, tail⟩, hn, h⟩ := bind_ok h
  exact pMany_pred p Q hp n tail xs rest h

/-- The actual witness parser enforces 32-byte siblings and binary path directions. -/
theorem pPathItem_shape {bs rest : Bytes} {step : Bytes × Nat}
    (h : pPathItem bs = .ok (step, rest)) :
    step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1) := by
  unfold pPathItem at h
  obtain ⟨⟨hash, tail⟩, hh, h⟩ := bind_ok h
  obtain ⟨⟨d, tail'⟩, hd, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, he, _⟩ := bind_ok h
    cases he
  · rename_i hn
    cases h
    exact ⟨V3.pHash_len hh, by omega⟩

/-- The concrete decoded proof entry supplies the source renderer's path-width premises. -/
theorem pEntry_path_shape {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e, rest)) :
    ∀ step ∈ e.proof.path, step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1) := by
  unfold pEntry at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (dsimp only at h))
  cases h
  apply pVec_pred pPathItem (fun step => step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1))
    (fun _ _ _ hh => pPathItem_shape hh) (by assumption)

end ZkFormal.NearV3
