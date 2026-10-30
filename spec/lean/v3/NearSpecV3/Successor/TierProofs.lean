import NearSpecV3.Successor.Config

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — refinement between checker configurations, shell level

`Refines x y` says: `x` is an exclusion (`out of domain …`), or `x = y` — so wherever `x` decides
(accept or reject, error string included), `y` returns the same result. Every lemma here is proved by
`refines_lockstep`, which walks the two elaborated checker bodies together: identical subterms by
reflexivity, binds/`if`s/`match`es by congruence, an exclusion guard present only on the left by
`check_bind_left`, and a numeric exclusion bound weakened on the right by `check_le`. No definition
is changed; the lemmas are about the existing terms.

Per-feature lemmas for each whole-state shell (`checkD2CoreWithObs`, `checkD2CoreGWith`,
`checkReshardCoreObs`) and the signed cores (`checkD2CoreObs`, `checkD2CoreG`):

* `*_segment_mono` — lifting `c.segment` (`segmentUnbounded := true`);
* `*_gas_mono` — weakening the per-chunk gas bound (`CapLe`).

The configuration-level and tier-level theorems are in `TierMono.lean`.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Refinement of checker results -/

/-- `Refines x y`: `x` is an exclusion, or `x = y`. -/
def Refines {α : Type} (x y : Except String α) : Prop :=
  x = y ∨ ∃ e, x = .error e ∧ isExclusion e = true

namespace Refines

theorem refl {α : Type} (x : Except String α) : Refines x x := Or.inl rfl

theorem trans {α : Type} {x y z : Except String α} (h₁ : Refines x y) (h₂ : Refines y z) :
    Refines x z := by
  rcases h₁ with rfl | h
  · exact h₂
  · exact Or.inr h

theorem bind {α β : Type} {x y : Except String α} {f g : α → Except String β}
    (hxy : Refines x y) (hfg : ∀ a, Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  rcases hxy with rfl | ⟨e, rfl, he⟩
  · cases x with
    | error e => exact Or.inl rfl
    | ok a => exact hfg a
  · exact Or.inr ⟨e, rfl, he⟩

theorem bind' {α β : Type} {x y : Except String α} {f g : α → Except String β}
    (hxy : x = y) (hfg : ∀ a, Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  subst hxy; exact bind (refl _) hfg

theorem throw_bind {α β : Type} (e : String) (f g : α → Except String β) :
    Refines ((Except.error e : Except String α) >>= f) ((Except.error e : Except String α) >>= g) :=
  Or.inl rfl

theorem map {α β : Type} {x y : Except String α} (f : α → β) (h : Refines x y) :
    Refines (x.map f) (y.map f) := by
  rcases h with rfl | ⟨e, rfl, he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e, rfl, he⟩

theorem ite_congr {β : Type} (c : Prop) [Decidable c] {t t' e e' : Except String β}
    (ht : c → Refines t t') (he : ¬c → Refines e e') :
    Refines (if c then t else e) (if c then t' else e') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

/-- A flag-guarded check whose two branches share the continuation (the elaborated form of
`if flag then check A else check B` followed by the rest of the checker): the continuation is
walked once, not once per branch. Without this, every configuration flag guard doubles the walk. -/
theorem ite_bind_join {β : Type} (c : Prop) [Decidable c] (x₁ x₂ : Except String Unit)
    {K K' : Unit → Except String β} (hK : ∀ u, Refines (K u) (K' u)) :
    Refines (if c then x₁ >>= K else x₂ >>= K) (if c then x₁ >>= K' else x₂ >>= K') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact bind (refl _) hK
  · simp only [hc, ite_false]; exact bind (refl _) hK

/-- The same for `if flag then check A` with no `else`: the else branch is the continuation. -/
theorem ite_bind_skip {β : Type} (c : Prop) [Decidable c] (x : Except String Unit)
    {K K' : Except String β} (hK : Refines K K') :
    Refines (if c then x >>= (fun _ => K) else K) (if c then x >>= (fun _ => K') else K') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact bind (refl _) fun _ => hK
  · simp only [hc, ite_false]; exact hK

/-- An exclusion guard on the left that the right does not have. -/
theorem check_bind_left {β : Type} (b : Bool) (m : String) (hm : isExclusion m = true)
    {f : Unit → Except String β} {g : Except String β} (hfg : ∀ u, Refines (f u) g) :
    Refines (check b m >>= f) g := by
  unfold check; cases b
  · exact Or.inr ⟨m, rfl, hm⟩
  · exact hfg ()

/-- A weaker numeric exclusion bound on the right. -/
theorem check_le (x a b : Nat) (m m' : String) (hab : a ≤ b) (hm : isExclusion m = true) :
    Refines (check (decide (x ≤ a)) m) (check (decide (x ≤ b)) m') := by
  unfold check
  by_cases hx : x ≤ a
  · have : x ≤ b := Nat.le_trans hx hab
    simp only [hx, this, decide_true]; exact Or.inl rfl
  · simp only [hx, decide_false]; exact Or.inr ⟨m, rfl, hm⟩

theorem check_pure (b : Bool) (m : String) (hm : isExclusion m = true) :
    Refines (check b m) (pure ()) := by
  unfold check; cases b
  · exact Or.inr ⟨m, rfl, hm⟩
  · exact Or.inl rfl

/-- A guard whose condition implies the right guard's (for example `1 ≤ n && n ≤ 64` ⇒ `1 ≤ n`). -/
theorem check_and_left (p q : Bool) (m m' : String) (hm : isExclusion m = true) :
    Refines (check (p && q) m) (check p m') := by
  unfold check
  cases p <;> cases q <;> first | exact Or.inl rfl | exact Or.inr ⟨m, rfl, hm⟩

/-- A loop whose bodies refine pointwise refines. -/
theorem forIn_congr {α σ : Type} (l : List α) (b : σ)
    {f g : α → σ → Except String (ForInStep σ)} (h : ∀ a s, Refines (f a s) (g a s)) :
    Refines (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact refl _
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine bind (h a b) fun r => ?_
    cases r with
    | done s => exact refl _
    | yield s => exact ih s

/-- The narrower legacy tiers' storage-proof precondition (`withStorageExclusion`) preserves
refinement. -/
theorem storage {r r' : Except String Unit} (w : Bytes) (h : Refines r r') :
    Refines (withStorageExclusion r w) (withStorageExclusion r' w) := by
  rcases h with rfl | ⟨e, rfl, he⟩
  · exact refl _
  · exact Or.inr ⟨e, by simp [withStorageExclusion, he], he⟩

/-- Refinement fixes every decided verdict. -/
theorem verdict {x y : Except String Unit} (h : Refines x y)
    (hd : (Verdict.ofExcept x).inDomain = true) : Verdict.ofExcept y = Verdict.ofExcept x := by
  rcases h with rfl | ⟨e, rfl, he⟩
  · rfl
  · simp [Verdict.ofExcept, he, Verdict.inDomain] at hd

end Refines

theorem isExclusion_append {s : String} (t : String) (h : isExclusion s = true) :
    isExclusion (s ++ t) = true := by
  unfold isExclusion at *
  have hlen : oodPrefix.length ≤ s.toList.length := by
    have h' := beq_iff_eq.mp h
    have := congrArg List.length h'
    rw [List.length_take] at this
    omega
  rw [String.toList_append, List.take_append_of_le_length hlen]
  exact h

/-- Close `isExclusion m = true` for literal and interpolated exclusion messages. -/
macro "ood_tac" : tactic => `(tactic| ((repeat (apply isExclusion_append)); decide))

/-- Walk two checker bodies in lockstep: identical subterms by reflexivity, binds, `if`s and
`match`es by congruence, an exclusion guard present only on the left by `check_bind_left`, and a
numeric exclusion bound weakened on the right by `check_le`. -/
macro "refines_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | (with_reducible assumption)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.check_le _ _ _ _ _ (by assumption) (by ood_tac)) fun _ => ?_);
        try dsimp only)
    | ((refine Refines.bind (Refines.check_and_left _ _ _ _ (by ood_tac)) fun _ => ?_); try dsimp only)
    | (refine Refines.check_bind_left _ _ (by ood_tac) fun _ => ?_)
    | ((refine Refines.bind (Refines.check_pure _ _ (by ood_tac)) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

/-! ## Per-feature lemmas: `c.segment` -/

theorem checkD2CoreWithObs_segment_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g)
      (checkD2CoreWithObs { d with segmentUnbounded := true } h a c w g) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases seg
  · unfold checkD2CoreWithObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkD2CoreWith_segment_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g)
      (checkD2CoreWith { d with segmentUnbounded := true } h a c w g) :=
  Refines.map _ (checkD2CoreWithObs_segment_mono d h a c w g)

theorem checkD2CoreGWith_segment_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g)
      (checkD2CoreGWith { d with segmentUnbounded := true } h a c w g) := by
  have hW := checkD2CoreWith_segment_mono d h a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases seg
  · dsimp only at hW
    unfold checkD2CoreGWith
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkReshardCoreObs_segment_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCoreObs d h a c w g)
      (checkReshardCoreObs { d with segmentUnbounded := true } h a c w g) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases seg
  · unfold checkReshardCoreObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

/-! ## Per-feature lemmas: the per-chunk gas bound -/

/-- The gas-bound order: a larger bound, or no bound, is weaker. -/
def CapLe : Option Nat → Option Nat → Prop
  | some a, some b => a ≤ b
  | _, none => True
  | none, some _ => False

theorem checkD2CoreObs_gas_mono (h : ActionHooks) (a : Bool) (c w : Bytes) (g₁ g₂ : Option Nat)
    (hg : CapLe g₁ g₂) :
    Refines (checkD2CoreObs h a c w g₁) (checkD2CoreObs h a c w g₂) := by
  cases g₁ <;> cases g₂ <;> simp only [CapLe] at hg
  · exact Refines.refl _
  all_goals
    unfold checkD2CoreObs
    dsimp only
    refines_lockstep

theorem checkD2Core_gas_mono (h : ActionHooks) (a : Bool) (c w : Bytes) (g₁ g₂ : Option Nat)
    (hg : CapLe g₁ g₂) :
    Refines (checkD2Core h a c w g₁) (checkD2Core h a c w g₂) :=
  Refines.map _ (checkD2CoreObs_gas_mono h a c w g₁ g₂ hg)

-- One declaration per case: the merged whole-state shell is large enough that the three cases
-- together exceed one declaration's heartbeat budget.
theorem checkD2CoreWithObs_gas_mono_some (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x y : Nat) (hg : x ≤ y) :
    Refines (checkD2CoreWithObs d h a c w (some x)) (checkD2CoreWithObs d h a c w (some y)) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkD2CoreWithObs
  dsimp only
  refines_lockstep

theorem checkD2CoreWithObs_gas_mono_none (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x : Nat) :
    Refines (checkD2CoreWithObs d h a c w (some x)) (checkD2CoreWithObs d h a c w none) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkD2CoreWithObs
  dsimp only
  refines_lockstep

theorem checkD2CoreWithObs_gas_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g₁ g₂ : Option Nat) (hg : CapLe g₁ g₂) :
    Refines (checkD2CoreWithObs d h a c w g₁) (checkD2CoreWithObs d h a c w g₂) := by
  cases g₁ <;> cases g₂ <;> simp only [CapLe] at hg
  · exact Refines.refl _
  · exact checkD2CoreWithObs_gas_mono_none d h a c w _
  · exact checkD2CoreWithObs_gas_mono_some d h a c w _ _ hg

theorem checkD2CoreWith_gas_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g₁ g₂ : Option Nat) (hg : CapLe g₁ g₂) :
    Refines (checkD2CoreWith d h a c w g₁) (checkD2CoreWith d h a c w g₂) :=
  Refines.map _ (checkD2CoreWithObs_gas_mono d h a c w g₁ g₂ hg)

theorem checkD2CoreGWith_gas_mono_some (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x y : Nat) (hg : x ≤ y) :
    Refines (checkD2CoreGWith d h a c w (some x)) (checkD2CoreGWith d h a c w (some y)) := by
  have hW := checkD2CoreWith_gas_mono d h a c w (some x) (some y) hg
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkD2CoreGWith
  dsimp only
  refines_lockstep

theorem checkD2CoreGWith_gas_mono_none (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x : Nat) :
    Refines (checkD2CoreGWith d h a c w (some x)) (checkD2CoreGWith d h a c w none) := by
  have hW := checkD2CoreWith_gas_mono d h a c w (some x) none trivial
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkD2CoreGWith
  dsimp only
  refines_lockstep

theorem checkD2CoreGWith_gas_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g₁ g₂ : Option Nat) (hg : CapLe g₁ g₂) :
    Refines (checkD2CoreGWith d h a c w g₁) (checkD2CoreGWith d h a c w g₂) := by
  cases g₁ <;> cases g₂ <;> simp only [CapLe] at hg
  · exact Refines.refl _
  · exact checkD2CoreGWith_gas_mono_none d h a c w _
  · exact checkD2CoreGWith_gas_mono_some d h a c w _ _ hg

theorem checkD2CoreG_gas_mono (h : ActionHooks) (a : Bool) (c w : Bytes) (g₁ g₂ : Option Nat)
    (hg : CapLe g₁ g₂) :
    Refines (checkD2CoreG h a c w g₁) (checkD2CoreG h a c w g₂) :=
  checkD2CoreGWith_gas_mono legacyDriver h a c w g₁ g₂ hg

theorem checkReshardCoreObs_gas_mono_some (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x y : Nat) (hg : x ≤ y) :
    Refines (checkReshardCoreObs d h a c w (some x)) (checkReshardCoreObs d h a c w (some y)) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkReshardCoreObs
  dsimp only
  refines_lockstep

theorem checkReshardCoreObs_gas_mono_none (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (x : Nat) :
    Refines (checkReshardCoreObs d h a c w (some x)) (checkReshardCoreObs d h a c w none) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  unfold checkReshardCoreObs
  dsimp only
  refines_lockstep

theorem checkReshardCoreObs_gas_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g₁ g₂ : Option Nat) (hg : CapLe g₁ g₂) :
    Refines (checkReshardCoreObs d h a c w g₁) (checkReshardCoreObs d h a c w g₂) := by
  cases g₁ <;> cases g₂ <;> simp only [CapLe] at hg
  · exact Refines.refl _
  · exact checkReshardCoreObs_gas_mono_none d h a c w _
  · exact checkReshardCoreObs_gas_mono_some d h a c w _ _ hg

/-! ## Per-feature lemmas: the witness-size and layout bounds (Gate-B lifts)

`witnessUnbounded` replaces the 8 MiB serialized-witness bound by `compressedSafeWitnessBytes`
(50,000,000 bytes, a weaker bound); `layoutUnbounded` drops `numShards ≤ 64` from `c.layout`. -/

theorem witnessBound_le : 8388608 ≤ compressedSafeWitnessBytes := by
  unfold compressedSafeWitnessBytes; decide

theorem checkD2CoreWithObs_witness_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g)
      (checkD2CoreWithObs { d with witnessUnbounded := true } h a c w g) := by
  have hb := witnessBound_le
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases wu
  · unfold checkD2CoreWithObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkD2CoreWith_witness_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g)
      (checkD2CoreWith { d with witnessUnbounded := true } h a c w g) :=
  Refines.map _ (checkD2CoreWithObs_witness_mono d h a c w g)

theorem checkD2CoreGWith_witness_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g)
      (checkD2CoreGWith { d with witnessUnbounded := true } h a c w g) := by
  have hb := witnessBound_le
  have hW := checkD2CoreWith_witness_mono d h a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases wu
  · dsimp only at hW
    unfold checkD2CoreGWith
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkReshardCoreObs_witness_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCoreObs d h a c w g)
      (checkReshardCoreObs { d with witnessUnbounded := true } h a c w g) := by
  have hb := witnessBound_le
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases wu
  · unfold checkReshardCoreObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkD2CoreWithObs_layout_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g)
      (checkD2CoreWithObs { d with layoutUnbounded := true } h a c w g) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases lu
  · unfold checkD2CoreWithObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkD2CoreWith_layout_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g)
      (checkD2CoreWith { d with layoutUnbounded := true } h a c w g) :=
  Refines.map _ (checkD2CoreWithObs_layout_mono d h a c w g)

theorem checkD2CoreGWith_layout_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g)
      (checkD2CoreGWith { d with layoutUnbounded := true } h a c w g) := by
  have hW := checkD2CoreWith_layout_mono d h a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases lu
  · dsimp only at hW
    unfold checkD2CoreGWith
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

theorem checkReshardCoreObs_layout_mono (d : ExecutionDriver) (h : ActionHooks) (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCoreObs d h a c w g)
      (checkReshardCoreObs { d with layoutUnbounded := true } h a c w g) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  cases lu
  · unfold checkReshardCoreObs
    dsimp only
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refines_lockstep
  · exact Refines.refl _

end NearSpecV3.Successor
