import NearSpecV3.Successor.Config

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W10 — genesis checker vs non-genesis checker: the overlap

`checkD2CoreGWith` (the genesis-capable shell) runs the same prefix as `checkD2CoreWithObs` up to the
main block `B2` and then, for a non-genesis `B2`, returns a *fresh* run of `checkD2CoreWith`. The
theorem `checkD2CoreGWith_overlap` closes the gap the delegation leaves: the prefix is walked in
lockstep while tracking that the non-genesis checker's full result `W` still equals its remaining
computation (`Overlap`), so at the delegation point the fresh run is `W` itself. For the signed pair
(`checkD2CoreG`, `checkD2Core`) it is `checkD2CoreG_overlap`.

The driver must keep the resharding guards (`resharding = false`): with them lifted, the
non-genesis shell decides layout changes the genesis-capable prefix still excludes.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-- The non-genesis checker's genesis exclusion. -/
def notGenesisError : String := "out of domain (c.not_genesis)"

/-- Tracked overlap relation. `W` is the non-genesis checker's full result; `y` is the non-genesis
checker's remaining computation at the current program point, and `x` the genesis-capable
checker's. Whenever `W` is still `y`, the genesis-capable result is `W`'s verdict, or `W` is the
genesis exclusion. -/
def Overlap (W : Except String Observable) (x : Except String Unit) (y : Except String Observable) :
    Prop :=
  W = y → x = W.map (fun _ => ()) ∨ W = .error notGenesisError

namespace Overlap

theorem bind {α : Type} {W : Except String Observable} {p : Except String α}
    {k₁ : α → Except String Unit} {k₂ : α → Except String Observable}
    (hk : ∀ a, Overlap W (k₁ a) (k₂ a)) : Overlap W (p >>= k₁) (p >>= k₂) := by
  intro hW
  cases p with
  | error e => left; subst hW; rfl
  | ok a => exact hk a hW

theorem bind' {α : Type} {W : Except String Observable} {p₁ p₂ : Except String α}
    {k₁ : α → Except String Unit} {k₂ : α → Except String Observable} (hp : p₁ = p₂)
    (hk : ∀ a, Overlap W (k₁ a) (k₂ a)) : Overlap W (p₁ >>= k₁) (p₂ >>= k₂) := by
  subst hp; exact bind hk

/-- The delegation point: the genesis-capable checker returns the non-genesis checker's full
result on a non-genesis main block; the non-genesis checker excludes a genesis one. -/
theorem diverge {W : Except String Observable} (gen : Bool) {GEN : Except String Unit}
    {REST : Unit → Except String Observable} (X : Except String Unit)
    (hX : X = W.map (fun _ => ())) :
    Overlap W (if (!gen) = true then X else GEN)
      (check (!gen) notGenesisError >>= REST) := by
  intro hW
  cases gen
  · left; exact hX
  · right; rw [hW]; rfl

theorem error_both {W : Except String Observable} {x : Except String Unit}
    {y : Except String Observable} (e : String) (hx : x = .error e) (hy : y = .error e) :
    Overlap W x y := by
  intro hW; left; rw [hx, hW, hy]; rfl

theorem ite_congr {W : Except String Observable} (c : Prop) [Decidable c]
    {t₁ e₁ : Except String Unit} {t₂ e₂ : Except String Observable}
    (ht : c → Overlap W t₁ t₂) (he : ¬c → Overlap W e₁ e₂) :
    Overlap W (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

end Overlap

macro "overlap_lockstep" : tactic => `(tactic|
  repeat (first
    | (refine Overlap.diverge _ _ (by subst_vars; rfl))
    | ((refine Overlap.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Overlap.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Overlap.error_both _ rfl rfl)
    | ((refine Overlap.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Overlap.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (refine Overlap.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

/-- **W10 overlap, including the common prefix.** For a driver that keeps the resharding guards
(`resharding = false`: the signed, D2 and every non-resharding successor driver), the
genesis-capable checker returns exactly the non-genesis checker's result, unless the non-genesis
checker excludes the claim as a genesis main block. The prefix before the delegation (decoding,
epoch table, layout, segment, hash links, the walk to `B2`) is shown equal step by step: both
checkers fail there with the same error, or both reach `B2`. -/
theorem checkD2CoreGWith_overlap (d : ExecutionDriver) (hd : d.resharding = false) (h : ActionHooks)
    (a : Bool) (c w : Bytes) (g : Option Nat) :
    checkD2CoreGWith d h a c w g = checkD2CoreWith d h a c w g ∨
      checkD2CoreWithObs d h a c w g = .error notGenesisError := by
  have key : ∀ W, W = checkD2CoreWithObs d h a c w g →
      Overlap W (checkD2CoreGWith d h a c w g) (checkD2CoreWithObs d h a c w g) := by
    intro W hWfull
    obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, bl, ik, sa⟩ := d
    cases hd
    unfold checkD2CoreGWith checkD2CoreWithObs
    dsimp only
    simp only [Bool.not_false, ↓reduceIte]
    overlap_lockstep
  exact key _ rfl rfl

theorem checkD2CoreObs_eq_legacy (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    checkD2CoreWithObs legacyDriver h a c w g = checkD2CoreObs h a c w g := rfl

/-- The signed genesis checker (`checkD2CoreG`, the `.genesis` tier's core) and the signed
non-genesis core (`checkD2Core`, `checkD3`'s core) agree except where `checkD2Core` excludes a
genesis main block. -/
theorem checkD2CoreG_overlap (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    checkD2CoreG h a c w g = checkD2Core h a c w g ∨
      checkD2CoreObs h a c w g = .error notGenesisError :=
  checkD2CoreGWith_overlap legacyDriver rfl h a c w g

/-- The overlap as a non-genesis-side characterization: on every claim whose main block is not
genesis — i.e. every claim the non-genesis checker does not exclude as genesis — the two checkers
return the same result, error string included. -/
theorem checkD2CoreGWith_eq_of_not_genesis (d : ExecutionDriver) (hd : d.resharding = false)
    (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat)
    (hng : checkD2CoreWithObs d h a c w g ≠ .error notGenesisError) :
    checkD2CoreGWith d h a c w g = checkD2CoreWith d h a c w g :=
  (checkD2CoreGWith_overlap d hd h a c w g).resolve_right hng

#print axioms checkD2CoreGWith_overlap
#print axioms checkD2CoreG_overlap

end NearSpecV3.Successor
