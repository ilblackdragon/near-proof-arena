import NearSpecV3.D2SubD3.WasmGas
import NearSpecV3.Successor.TierHooks
import NearSpecV3.ChunkValidationD1a
import NearSpecV3.D0SubD1

/-!
# D2 ⊂ D3 (`relD2_relD3 : RelD2 cb w → RelD3 cb w`)

`checkD2 = checkD2Core d2Hooks false · · none` and
`checkD3 = checkD2Core (d3Hooks pv86) true · · (some G_α)`: the same pipeline with three differences,
each a refinement (`Successor.Refines`: wherever the left side is not an exclusion, the right side
returns the same result):

1. **The gas cap** (`checkD2CoreObs_cap_free`): `none → some cap` refines under a gas-free hook, because
   the chunk's `wasmGas` is 0 (`D2.applyNewChunkD2_wasmGas`, the uncaught-hook argument: only the
   `FunctionCall` hook sets `gas_burnt_for_function_call`, and `d2Hooks` never succeeds on it).
2. **Code blobs** (`checkD2CoreObs_codes_mono`): `allowCodes := false → true` only removes the
   `w.no_code` exclusion.
3. **The hook** (`d2Hooks_refine_d3Hooks` + W12's `checkD2CoreObs_hooks_mono`): `d2Hooks` answers every
   `FunctionCall` with the exclusion `out of domain (e.wasm)`, so any hook refines it, and the legacy
   pipeline binds the hook's result without catching it.

A D2 accept is not an exclusion, so it survives all three steps unchanged: `relD2_relD3`.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

set_option maxRecDepth 20000

theorem Refines.bind_post {α β : Type} {x : Except String α} {f g : α → Except String β}
    {Q : α → Prop} (hx : PostE x Q) (hfg : ∀ a, Q a → Refines (f a) (g a)) :
    Refines (x >>= f) (x >>= g) := by
  cases h : x with
  | error e => exact Or.inl rfl
  | ok a => exact hfg a (hx a h)

theorem Refines.check_true_right {β : Type} (b : Bool) (m : String) (hb : b = true)
    {K : Except String β} {K' : Unit → Except String β} (hK : Refines K (K' ())) :
    Refines K (check b m >>= K') := by
  subst hb; exact hK

/-- `refines_lockstep` (`TierProofs.lean`) with the gas-cap rules in front. -/
macro "cap_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | ((refine Refines.bind_post (applyNewChunkD2_wasmGas _ ‹GasFree _› _ _ _ _ _ _ _ _) fun _ _ => ?_);
        try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.check_true_right _ _ ?_ ?_; focus (simp_all; done))
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

set_option maxHeartbeats 8000000 in
theorem checkD2CoreObs_cap_free (h : ActionHooks) (hg : GasFree h) (a : Bool) (c w : Bytes)
    (cap : Nat) : Refines (checkD2CoreObs h a c w none) (checkD2CoreObs h a c w (some cap)) := by
  unfold checkD2CoreObs
  dsimp only
  cap_lockstep


set_option maxHeartbeats 8000000 in
/-- `allowCodes := false → true` only drops the `w.no_code` exclusion. -/
theorem checkD2CoreObs_codes_mono (h : ActionHooks) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreObs h false c w g) (checkD2CoreObs h true c w g) := by
  unfold checkD2CoreObs
  dsimp only
  refines_lockstep
  all_goals first
    | (refine Refines.check_bind_left _ _ (by decide) fun _ => ?_; refines_lockstep)
    | skip

theorem d2Hooks_refine (h : ActionHooks) : HooksRefine d2Hooks h :=
  fun _ _ _ _ => Or.inr ⟨_, rfl, by decide⟩

/-- **D2 ⊂ D3 at the level of results**: wherever `checkD2` is not an exclusion, `checkD3` returns
the same result. -/
theorem checkD3_refines_checkD2 (c w : Bytes) : Refines (checkD2 c w) (D3.checkD3 c w) := by
  unfold checkD2 D3.checkD3 checkD2Core
  apply Refines.map
  exact ((checkD2CoreObs_cap_free d2Hooks d2Hooks_gasFree false c w D3.gAlpha).trans
    (checkD2CoreObs_codes_mono d2Hooks c w _)).trans
    (checkD2CoreObs_hooks_mono (d2Hooks_refine _) true c w _)

/-- **D2 ⊂ D3**: every chunk the D2 relation accepts, the D3 relation accepts, on the same bytes. -/
theorem relD2_relD3 (c w : Bytes) (h : RelD2 c w) : D3.RelD3 c w := by
  have h2 : checkD2 c w = .ok () := by
    unfold RelD2 acceptsD2 at h; split at h
    · assumption
    · cases h
  rcases checkD3_refines_checkD2 c w with he | ⟨e, he, _⟩
  · show D3.checkD3 c w = .ok (); rw [← he]; exact h2
  · rw [h2] at he; cases he

/-- info: 'NearSpecV3.Successor.relD2_relD3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relD2_relD3


/-! ## The ladder, and what `WitnessLift` now reduces to

`D0 ⊂ D1` (`relD0_relD1`) and `D2 ⊂ D3` (`relD2_relD3`) are proved, `D1a ⊂ D1` is a projection
(`relD1a_relD1`). The one missing rung is `D1 ⊂ D2`. `WitnessLift B cb w := RelD1a B cb w →
∃ w2, RelD3 cb w2` (`zk-formal/ZkFormal/PQ/Join/Coverage.lean`) therefore follows, with the identity
witness `w2 = w`, from that rung alone.

**The rung is false as stated** (2026-10-30, `Examples/D1NotSubD2.lean`, kernel-checked):
D0/D1 never compare the `epoch_start_after` flags with the headers, D2/D3 require
`!b.isGenesis || flag = 1`, so a claim whose segment ends at the genesis block with a false flag 0
is in `RelD0`, `RelD1` and `RelD1a B0` but not in `RelD2`/`RelD3` (`not_d1_sub_d2`,
`not_d1a_sub_d3`). The two lemmas below stay true but their hypothesis does not hold; closing
`WitnessLift` needs either D2's genesis rule in D0/D1 or a claim condition (evidence:
`docs/evidence/lean-chunk-completion/proof-debt/d1-genesis-flag/`). -/

theorem relD1a_relD3_of_d1_d2 (hd12 : ∀ cb w, RelD1 cb w → RelD2 cb w) {B : Nat} {cb w : Bytes}
    {W Dp N : Nat} (h : RelD1a B cb w W Dp N) : D3.RelD3 cb w :=
  relD2_relD3 cb w (hd12 cb w (relD1a_relD1 h))

theorem relD0_relD3_of_d1_d2 (hd12 : ∀ cb w, RelD1 cb w → RelD2 cb w) (cb w : Bytes)
    (h : RelD0 cb w) : D3.RelD3 cb w :=
  relD2_relD3 cb w (hd12 cb w (relD0_relD1 cb w h))

end NearSpecV3.Successor
