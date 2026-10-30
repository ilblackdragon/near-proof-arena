import NearSpecV3.Successor.TierWholeWalk
import NearSpecV3.Successor.TierStoreAuth

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O7 at chunk level — the complete-code policy is the cold one on every whole-state checker

The code policy is a parameter of the recorder engine (`StorageExecution.Flags`, refactor
2026-10-30, `TierFlagsEq.lean`) read only by `resolveCodeBytes` inside the recorded call
(`resOf`). On an environment whose store is content-addressed (`HStore.Auth`) the two policies
resolve every call identically (`complete_eq_cold`), so the recorded calls are equal
(`functionCallRecorded_policy_eq`) and the engine walk (`run_rec_mono`, with the environment
predicate `StoreAuth`) gives `run` at either policy refining `run` at the other.

Every whole-state shell builds its main-transition store as `mkHStore merged` (`mkHStore_auth`), so
the shells refine under the weaker `ApplyRefineA` (refinement on authenticated stores only):
`checkD2CoreWithObsA_apply_mono`, `checkD2CoreGWithA_apply_mono`, `checkReshardCoreObsA_apply_mono`.

Result: `Lift.completeCode` — on every whole-state configuration the complete-code flag moves no
verdict, in either direction; in particular `.completeCodeGlobal ⊑ .globalActions` and
`.globalActions ⊑ .completeCodeGlobal` (`relSuccessor_completeCodeGlobal_globalActions`,
`relSuccessor_globalActions_completeCodeGlobal`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution

/-- The environment predicate of O7: the code store is content-addressed. -/
def StoreAuth (e : Env) : Prop := e.store.Auth

/-- On a content-addressed store both policies resolve every call the same way. -/
theorem resOf_policy_eq (ga : Bool) (p p' : CodeWitnessPolicy) (c : ActCtx) (h : StoreAuth c.env) :
    resOf ⟨ga, p⟩ c = resOf ⟨ga, p'⟩ c := by
  have hc : ∀ q : CodeWitnessPolicy, resOf ⟨ga, q⟩ c = resOf ⟨ga, .coldPartial⟩ c := by
    intro q
    funext cur com att pre hash t
    cases q
    · rfl
    · exact complete_eq_cold _ pre hash t (fun code hcode => HStore.Auth.get h hash code hcode)
  rw [hc p, hc p']

theorem functionCallRecorded_policy_eq (ga : Bool) (p p' : CodeWitnessPolicy) (cfg : NearCfg)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (h : StoreAuth c.env) :
    functionCallRecorded ⟨ga, p⟩ cfg c st ar b = functionCallRecorded ⟨ga, p'⟩ cfg c st ar b := by
  rw [functionCallRecorded_eq_with, functionCallRecorded_eq_with, resOf_policy_eq ga p p' c h]

theorem recRefine_policy (ga : Bool) (p p' : CodeWitnessPolicy) (cfg : NearCfg) :
    RecRefine StoreAuth ga p cfg p' cfg := by
  intro c st ar b h
  rw [functionCallRecorded_policy_eq ga p p' cfg c st ar b h]
  exact MRef.refl _

/-- **O7, engine level.** On a content-addressed store the recorder engine at one code policy refines
the engine at the other. -/
theorem run_policy_mono (cfg : NearCfg) (p p' : CodeWitnessPolicy) (prims : Prims) (env : Env)
    (t : PTrie) (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (congestion : Congestion) (ga : Bool) (h : StoreAuth env) :
    Refines (StorageExecution.run cfg prims env t vu props incoming txs congestion ga p)
      (StorageExecution.run cfg prims env t vu props incoming txs congestion ga p') :=
  run_rec_mono (recRefine_policy ga p p' cfg) rfl prims env t vu props incoming txs congestion h

/-! ## Shells, on authenticated stores -/

/-- `ApplyRefine` restricted to environments with a content-addressed store. -/
def ApplyRefineA (ap ap' : ApplyFn) (h h' : ActionHooks) : Prop :=
  ∀ p e t vu ps rs txs cg, StoreAuth e → Refines (ap h p e t vu ps rs txs cg) (ap' h' p e t vu ps rs txs cg)

macro "shellA_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | ((refine Refines.bind (‹ApplyRefineA _ _ _ _› _ _ _ _ _ _ _ _ (mkHStore_auth _)) fun _ => ?_);
        try dsimp only)
    | (exact ‹ApplyRefineA _ _ _ _› _ _ _ _ _ _ _ _ (mkHStore_auth _))
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem checkD2CoreWithObsA_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g) (checkD2CoreWithObs { d with apply := ap' } h' a c w g) := by
  unfold checkD2CoreWithObs
  dsimp only
  shellA_lockstep
  all_goals shellA_lockstep

theorem checkD2CoreWithA_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g) (checkD2CoreWith { d with apply := ap' } h' a c w g) :=
  Refines.map _ (checkD2CoreWithObsA_apply_mono d ap' h h' hap a c w g)

set_option maxHeartbeats 16000000 in
theorem checkD2CoreGWithA_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g) (checkD2CoreGWith { d with apply := ap' } h' a c w g) := by
  have hW := checkD2CoreWithA_apply_mono d ap' h h' hap a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, crc, cw, bl, ik, sa⟩ := d
  dsimp only at hW hap
  unfold checkD2CoreGWith
  dsimp only
  refines_lockstep
  all_goals shellA_lockstep

set_option maxHeartbeats 16000000 in
theorem checkReshardCoreObsA_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCoreObs d h a c w g) (checkReshardCoreObs { d with apply := ap' } h' a c w g) := by
  unfold checkReshardCoreObs
  dsimp only
  shellA_lockstep
  all_goals shellA_lockstep

theorem checkReshardCoreA_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCore d h a c w g) (checkReshardCore { d with apply := ap' } h' a c w g) :=
  Refines.map _ (checkReshardCoreObsA_apply_mono d ap' h h' hap a c w g)

/-- The shells in two-driver form: `d'` is `d` with another `apply`. -/
theorem shellsA_two (d d' : ExecutionDriver) (hd : d' = { d with apply := d'.apply }) (h h' : ActionHooks)
    (hap : ApplyRefineA d.apply d'.apply h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g) (checkD2CoreGWith d' h' a c w g) ∧
    Refines (checkD2CoreWith d h a c w g) (checkD2CoreWith d' h' a c w g) ∧
    Refines (checkReshardCore d h a c w g) (checkReshardCore d' h' a c w g) := by
  rw [hd]
  exact ⟨checkD2CoreGWithA_apply_mono d _ h h' hap a c w g, checkD2CoreWithA_apply_mono d _ h h' hap a c w g,
    checkReshardCoreA_apply_mono d _ h h' hap a c w g⟩

/-! ## Configuration and tier level -/

/-- **O7.** On every whole-state configuration (storage resolution, global actions or resharding
set), the complete-code flag moves no decided verdict, in either direction. -/
theorem Lift.completeCode (cfg : ProtocolCfg) (b b' : Bool)
    (hw : (cfg.storageResolution || cfg.globalActions || cfg.resharding) = true) :
    Lift { cfg with completeCodeWitness := b } { cfg with completeCodeWitness := b' } := by
  intro c w
  have hap : ∀ (pol pol' : CodeWitnessPolicy) h h',
      ApplyRefineA (recorderDriver cfg.wasm cfg.globalActions pol).apply
        (recorderDriver cfg.wasm cfg.globalActions pol').apply h h' :=
    fun pol pol' _ _ prims e t vu ps rs txs cg he =>
      run_policy_mono cfg.wasm pol pol' prims e t vu ps rs txs cg cfg.globalActions he
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, rh⟩ := cfg
  simp only at hw hap
  have h1 : ∀ x : Bool, (sr || ga || x || rs) = true := by
    intro x; cases sr <;> cases ga <;> cases rs <;> cases x <;> simp_all
  unfold checkSuccessor
  dsimp only
  split
  · simp only [h1, ite_true]
    cases rs
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false]
      refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine (shellsA_two _ _ ?_ _ _ ?_ _ _ _ _).1
        · rfl
        · exact hap _ _ _ _
      · refine (shellsA_two _ _ ?_ _ _ ?_ _ _ _ _).2.1
        · rfl
        · exact hap _ _ _ _
    · simp only [ite_true]
      refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine (shellsA_two _ _ ?_ _ _ ?_ _ _ _ _).2.2
        · rfl
        · exact hap _ _ _ _
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · refine (shellsA_two _ _ ?_ _ _ ?_ _ _ _ _).1
          · rfl
          · exact hap _ _ _ _
        · refine (shellsA_two _ _ ?_ _ _ ?_ _ _ _ _).2.1
          · rfl
          · exact hap _ _ _ _
  · exact Refines.refl _

/-- `.completeCodeGlobal ⊑ .globalActions`. -/
theorem relSuccessor_completeCodeGlobal_globalActions (c w : Bytes) :
    Refines (Tier.checker .completeCodeGlobal c w) (Tier.checker .globalActions c w) :=
  Lift.completeCode (Tier.cfg .globalActions) true false rfl c w

/-- `.globalActions ⊑ .completeCodeGlobal`: the two tiers decide the same chunks the same way. -/
theorem relSuccessor_globalActions_completeCodeGlobal (c w : Bytes) :
    Refines (Tier.checker .globalActions c w) (Tier.checker .completeCodeGlobal c w) :=
  Lift.completeCode (Tier.cfg .globalActions) false true rfl c w

#print axioms run_policy_mono
#print axioms checkD2CoreGWithA_apply_mono
#print axioms checkReshardCoreObsA_apply_mono
#print axioms Lift.completeCode
#print axioms relSuccessor_completeCodeGlobal_globalActions
#print axioms relSuccessor_globalActions_completeCodeGlobal

end NearSpecV3.Successor
