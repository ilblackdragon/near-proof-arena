import NearSpecV3.Successor.TierHooks

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — obligations O1 (floats) and O5 (loading limits), at configuration and tier level

* **O1.** `Lift.floats_legacy`: on every configuration that runs the legacy engine (no storage
  resolution, global actions, complete-code witness or resharding), switching floats on refines.
  Chain: `prepare_floats` (`TierFloats.lean`: preparation changes only where the float-free run
  reported `outOfDomain`) → `runCallWithLimits_floats` (the interpreter never reads the flag) →
  `d3Hooks_floats` (the hook refines) → `checkD2Core_hooks_mono` / `checkD2CoreG_hooks_mono`
  (`TierHooks.lean`: the legacy pipeline only binds the hook's result).
  Named pairs: `.signed ⊑ .floats`, `.protoGas ⊑ .floatsProtoGas`,
  `.genesis ⊑ .genesisFloatsProtoGas`, and the compositions into `.genesisFloatsProtoGas` and
  `.runtimeLimits`.
  Not covered: floats on the whole-state (recorder) engine. No named tier pair needs it (every
  whole-state tier already sets floats); it would need the same propagation through
  `StorageExecution`.
* **O5.** Every named tier sets `loadingLimits` (`Tier.cfg_loadingLimits`), so no named pair
  differs in it, and `.genesisFloatsProtoGas` and `.runtimeLimits` are the same configuration
  (`runtimeLimits_cfg_eq`, `relSuccessor_runtimeLimits_mono`). The flag is a semantic correction,
  not a lift, so `Lift cfg { cfg with loadingLimits := true }` is false in general (a module that
  does not fit the pooling allocator moves the verdict); its call-level inertness on fitting modules
  is `runCallWithLimits_eq_of_fits` (`TierMono.lean`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

theorem ProtocolCfg.wasm_floats (cfg : ProtocolCfg) (h : cfg.floats = false) :
    ({ cfg with floats := true } : ProtocolCfg).wasm = { cfg.wasm with floats := true } := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu⟩ := cfg
  simp only at h
  subst h
  rfl

theorem ProtocolCfg.floats_true_eq (cfg : ProtocolCfg) (h : cfg.floats = true) :
    ({ cfg with floats := true } : ProtocolCfg) = cfg := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu⟩ := cfg
  simp only at h
  subst h
  rfl

/-- On a configuration without the whole-state features, the root is the legacy engine with the
D3 hooks. -/
theorem checkSuccessor_legacy_eq (cfg : ProtocolCfg) (hs : cfg.storageResolution = false)
    (hg : cfg.globalActions = false) (hc : cfg.completeCodeWitness = false)
    (hr : cfg.resharding = false) (c w : Bytes) :
    checkSuccessor cfg c w =
      if cfg.protocolVersion = 86 then
        (if cfg.genesisMainTransition then checkD2CoreG (D3.d3Hooks cfg.wasm) true c w cfg.gasCap
         else checkD2Core (D3.d3Hooks cfg.wasm) true c w cfg.gasCap)
      else .error (unsupportedPvError cfg.protocolVersion) := by
  unfold checkSuccessor
  split
  · rename_i h
    simp only [hs, hg, hc, hr, h, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  · rename_i h
    split
    · exact absurd ‹_› h
    · rfl

/-- **O1 on the legacy engine.** On every configuration that runs `checkD2Core`/`checkD2CoreG`,
switching floats on never changes a decided verdict. -/
theorem Lift.floats_legacy (cfg : ProtocolCfg) (hs : cfg.storageResolution = false)
    (hg : cfg.globalActions = false) (hc : cfg.completeCodeWitness = false)
    (hr : cfg.resharding = false) : Lift cfg { cfg with floats := true } := by
  intro c w
  cases hf : cfg.floats
  · have hh : HooksRefine (D3.d3Hooks cfg.wasm)
        (D3.d3Hooks ({ cfg with floats := true } : ProtocolCfg).wasm) := by
      rw [ProtocolCfg.wasm_floats cfg hf]
      exact d3Hooks_floats _
    rw [checkSuccessor_legacy_eq cfg hs hg hc hr c w,
      checkSuccessor_legacy_eq { cfg with floats := true } hs hg hc hr c w]
    refine Refines.ite_congr _ (fun _ => Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
      (fun _ => Refines.refl _)
    · exact checkD2CoreG_hooks_mono hh _ _ _ _
    · exact checkD2Core_hooks_mono hh _ _ _ _
  · rw [ProtocolCfg.floats_true_eq cfg hf]
    exact Refines.refl _

/-- `.signed ⊑ .floats` (O1). -/
theorem relSuccessor_floats_mono (c w : Bytes) :
    Refines (Tier.checker .signed c w) (Tier.checker .floats c w) :=
  Lift.floats_legacy signedCfg rfl rfl rfl rfl c w

/-- `.protoGas ⊑ .floatsProtoGas` (O1). -/
theorem relSuccessor_protoGas_floatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .protoGas c w) (Tier.checker .floatsProtoGas c w) :=
  Lift.floats_legacy protocolGasCfg rfl rfl rfl rfl c w

/-- `.genesis ⊑ .genesisFloatsProtoGas` (O1, then the gas bound). -/
theorem relSuccessor_genesis_genesisFloatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .genesis c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (Lift.floats_legacy (Tier.cfg .genesis) rfl rfl rfl rfl c w)
    (checkSuccessor_gas_mono { Tier.cfg .genesis with floats := true } (some maxGasBurnt)
      gAlpha_le_maxGasBurnt c w)

/-- `.signed ⊑ .genesisFloatsProtoGas`: the signed statement refines the widest legacy-engine tier. -/
theorem relSuccessor_signed_genesisFloatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .signed c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (relSuccessor_genesis_mono c w) (relSuccessor_genesis_genesisFloatsProtoGas c w)

/-- `.floats ⊑ .genesisFloatsProtoGas`. -/
theorem relSuccessor_floats_genesisFloatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .floats c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (relSuccessor_floatsProtoGas_mono c w) (relSuccessor_genesisFloatsProtoGas_mono c w)

/-! ## O5: loading limits -/

/-- Every named tier carries the pinned loading rule. -/
theorem Tier.cfg_loadingLimits (t : Tier) : (Tier.cfg t).loadingLimits = true := by
  cases t <;> rfl

theorem runtimeLimits_cfg_eq : Tier.cfg .runtimeLimits = Tier.cfg .genesisFloatsProtoGas := rfl

/-- `.genesisFloatsProtoGas ⊑ .runtimeLimits` (both ways: the same configuration). -/
theorem relSuccessor_runtimeLimits_mono (c w : Bytes) :
    Refines (Tier.checker .genesisFloatsProtoGas c w) (Tier.checker .runtimeLimits c w) := by
  unfold Tier.checker
  rw [runtimeLimits_cfg_eq]
  exact Refines.refl _

/-- `.signed ⊑ .runtimeLimits`. -/
theorem relSuccessor_signed_runtimeLimits (c w : Bytes) :
    Refines (Tier.checker .signed c w) (Tier.checker .runtimeLimits c w) :=
  Refines.trans (relSuccessor_signed_genesisFloatsProtoGas c w) (relSuccessor_runtimeLimits_mono c w)

#print axioms Wasm.sectionBody_floats
#print axioms Wasm.earlyPass_floats
#print axioms Wasm.prepare_floats
#print axioms Wasm.run_floats
#print axioms functionCallWith_mono
#print axioms callRel_floats
#print axioms Wasm.runCallWithLimits_floats
#print axioms d3Hooks_floats
#print axioms checkD2Core_hooks_mono
#print axioms checkD2CoreG_hooks_mono
#print axioms checkSuccessor_legacy_eq
#print axioms Lift.floats_legacy
#print axioms relSuccessor_floats_mono
#print axioms relSuccessor_protoGas_floatsProtoGas
#print axioms relSuccessor_genesis_genesisFloatsProtoGas
#print axioms relSuccessor_signed_genesisFloatsProtoGas
#print axioms relSuccessor_floats_genesisFloatsProtoGas
#print axioms Tier.cfg_loadingLimits
#print axioms relSuccessor_runtimeLimits_mono
#print axioms relSuccessor_signed_runtimeLimits

/-! ## O7: the complete-code policy against the cold validator, at the code-resolution step

`completeCodeGlobal` differs from `globalActions` only in `CodeWitnessPolicy` (`.complete` vs
`.coldPartial`), read once per call by `resolveCodeBytes`.

* `.complete` rejects (`w.code_complete`) a call whose code a warm or in-chunk deploy serves and
  that nearcore accepts (census: 178 + 8 valid chunks, `tier-proofs/ccg.json`). That is the W08
  policy question and is not touched here.
* **Race arm (fixed 2026-10-30).** `.complete` used to *accept* a call whose code only a committed
  in-chunk deploy serves although `Pipeline.deterministic` could not rule out that its preparation
  was pipelined before that deploy (`timely = false`), where `.coldPartial` reports the thread race
  out of domain. It now reports the same exclusion (`resolveCompleteCode`). `complete_untimely_ood`
  states that both policies agree on that arm. -/

def raceOOD : String :=
  D3.oodE "contract preparation pipelined before the in-chunk deploy that serves its code"

/-- On the race arm both policies report the same exclusion. -/
theorem complete_untimely_ood (sources : CodeSources) (pre : PrestateCode) (hash code : Bytes)
    (hw : sources.witness hash = none) (hp : pre.needsWitness hash = false)
    (hc : sources.current.find? (fun c => sha256 c == hash) = none)
    (hd : sources.committed.find? (fun c => sha256 c == hash) = some code) :
    resolveCodeBytes .complete sources pre hash false = .error raceOOD ∧
      resolveCodeBytes .coldPartial sources pre hash false = .error raceOOD := by
  refine ⟨?_, ?_⟩
  · simp [resolveCodeBytes, resolveCompleteCode, CodeSources.deployed, List.find?_append, hw, hp,
      hc, hd, raceOOD]
  · simp [resolveCodeBytes, resolveColdCode, List.find?_append, hw, hc, hd, raceOOD]

/-- The concrete instance that the pre-fix policy accepted. -/
theorem complete_untimely_ood_example (code : Bytes) :
    resolveCodeBytes .complete { witness := fun _ => none, committed := [code] } .absent
      (sha256 code) false = .error raceOOD := by
  simp [resolveCodeBytes, resolveCompleteCode, CodeSources.deployed, PrestateCode.needsWitness,
    raceOOD]

/-- **O7, resolve step.** Wherever the complete policy resolves code, the cold policy resolves the
same bytes (an accept of `.complete` is an accept of `.coldPartial`). -/
theorem complete_ok_coldPartial (sources : CodeSources) (pre : PrestateCode) (hash code : Bytes)
    (timely : Bool) (h : resolveCodeBytes .complete sources pre hash timely = .ok code) :
    resolveCodeBytes .coldPartial sources pre hash timely = .ok code := by
  simp only [resolveCodeBytes, resolveCompleteCode, resolveColdCode, CodeSources.deployed,
    List.find?_append] at h ⊢
  rcases hw : sources.witness hash with _ | c <;>
    rcases hc : List.find? (fun c => sha256 c == hash) sources.current with _ | c1 <;>
    rcases hd : List.find? (fun c => sha256 c == hash) sources.committed with _ | c2 <;>
    cases ht : timely <;> cases hn : pre.needsWitness hash <;>
    simp_all <;> (split at h <;> simp_all)

#print axioms complete_ok_coldPartial

theorem raceOOD_isExclusion : isExclusion raceOOD = true := oodE_isExclusion _

#print axioms complete_untimely_ood
#print axioms complete_untimely_ood_example
#print axioms raceOOD_isExclusion

end NearSpecV3.Successor
